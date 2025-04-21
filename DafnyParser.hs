module DafnyParser where


import Control.Applicative
import qualified Data.Char as Char
import Syntax
import Printer
import Parser (Parser)
import qualified Parser as P
import Test.HUnit  (runTestTT,Test(..),Assertion, (~?=), (~:), assert, Counts)

prop_roundtrip_val :: Value -> Bool
prop_roundtrip_val v = P.parse valueP (pretty v) == Right v

prop_roundtrip_exp :: Expression -> Bool
prop_roundtrip_exp e = P.parse expP (pretty e) == Right e

prop_roundtrip_stat :: Statement -> Bool
prop_roundtrip_stat s = P.parse statementP (pretty s) == Right s


wsP :: Parser a -> Parser a
wsP p = p <* many P.space

test_wsP :: Test
test_wsP = TestList [
  P.parse (wsP P.alpha) "a" ~?= Right 'a',
  P.parse (many (wsP P.alpha)) "a b \n   \t c" ~?= Right "abc"
  ]

stringP :: String -> Parser ()
stringP str = wsP (P.string str) *> pure ()

test_stringP :: Test
test_stringP = TestList [
  P.parse (stringP "a") "a" ~?= Right (),
  P.parse (stringP "a") "b" ~?= Left "No parses",
  P.parse (many (stringP "a")) "a  a" ~?= Right [(),()]
  ]


constP :: String -> a -> Parser a
constP str a = pure a <* stringP str

test_constP :: Test
test_constP = TestList [
  P.parse (constP "&" 'a')  "&  " ~?=  Right 'a',
  P.parse (many (constP "&" 'a'))  "&   &" ~?=  Right "aa"
  ]

-- | We will also use `stringP` for some useful operations that parse between
-- | delimiters, consuming additional whitespace.

parens :: Parser a -> Parser a
parens x = P.between (stringP "(") x (stringP ")")

braces :: Parser a -> Parser a
braces x = P.between (stringP "{") x (stringP "}")

-- >>> P.parse (many (brackets (constP "1" 1))) "[1] [  1]   [1 ]"
-- Right [1,1,1]
brackets :: Parser a -> Parser a
brackets x = P.between (stringP "[") x (stringP "]")

valueP :: Parser Value
valueP = intValP <|> boolValP



-- >>> P.parse (many intValP) "1 2\n 3"
-- Right [IntVal 1,IntVal 2,IntVal 3]
intValP :: Parser Value
intValP = IntVal <$> wsP(P.int)


--Parses dafny bool
boolP :: Parser Bool
boolP = trueParser <|> falseParser where
     trueParser = stringP "true" *> pure True
     falseParser = stringP "false" *> pure False


-- >>> P.parse (many boolValP) "true false\n true"
-- Right [BoolVal True,BoolVal False,BoolVal True]
boolValP :: Parser Value
boolValP = BoolVal <$> wsP(boolP)



typeP :: Parser Type
typeP = constP "int" TInt <|> constP "bool" TBool <|> constP "array<int>" TArrayInt



expP :: Parser Expression
expP    = conjP where
  conjP   = compP `P.chainl1` opAtLevel (level Conj)  
  compP   = catP `P.chainl1` opAtLevel (level Gt)
  catP    = sumP `P.chainl1` opAtLevel (level Eq)
  sumP    = prodP `P.chainl1` opAtLevel (level Plus)
  prodP   = uopexpP `P.chainl1` opAtLevel (level Times)
  uopexpP = baseP
      <|> Op1 <$> uopP <*> uopexpP 
  baseP = lenP
       <|> Var <$> varP
       <|> parens expP
       <|> Val <$> valueP
      -- .Length here


-- >>>  P.parse (many varP) "x y z"
-- Right [Name "x", Name "y", Name "z"]
-- >>> P.parse varP "y[1]"
-- Right (Proj "y" (Val (IntVal 1)))
varP :: Parser Var
varP = (Proj <$> nameP <*> brackets expP) <|> (Name <$> nameP)

lenP :: Parser Expression
lenP = (Op1 Len . Var . Name) <$> (nameP <* stringP ".Length")

reserved :: [String]
reserved = [ "assert", "break","else","Length"
 ,"false","for","function","invariant","if","in"
 ,"return","true","method","int", "bool"
 ,"while", "requires","ensures"]

-- >>> P.parse (many nameP) "x sfds _ int"
-- Right ["x","sfds", "_"]

--Helper for nameP that contains predicates of being in reserved and not starting with a digit
predsName :: String -> Bool
predsName [] = True
predsName (x : xs) = not (elem (x : xs) reserved) && not (Char.isDigit x)

--nameP Parser helper to satisfy conditions
nameH :: Parser Char
nameH = P.satisfy (\x -> Char.isDigit x || Char.isAlpha x || x == '_')

-- parser for names
nameP :: Parser Name
nameP = wsP (P.filter predsName (some nameH))

-- Now write parsers for the unary and binary operators. Make sure you
--  check out the Syntax module for the list of all possible
--  operators. The tests are not exhaustive.

-- >>> P.parse (many uopP) "- - !"
-- Right [Neg,Neg,Not]
uopP :: Parser Uop
uopP = constP "-" Neg <|> constP "!" Not 

-- >>> P.parse (many bopP) "+ >= &&"
-- Right [Plus,Ge,Conj]
bopP :: Parser Bop
bopP =  constP "==>" Implies <|> constP "<->" Iff <|> constP "+" Plus
     <|> constP "-" Minus <|> constP "*" Times <|> constP "/" Divide
     <|> constP "%" Modulo <|> constP "==" Eq <|> constP "!=" Neq <|> constP ">=" Ge <|> constP ">" Gt 
     <|> constP "<=" Le <|> constP "<" Lt <|> constP "&&" Conj <|> constP "||" Disj 

bindingP :: Parser Binding
bindingP = (,) <$> (nameP <* stringP ":") <*> (typeP <* stringP ",") 
     <|> (,) <$> (nameP <* stringP ":") <*> typeP 

predicateP :: Parser Predicate
predicateP = Predicate <$> expP <|> invariantP 


assertP :: Parser Statement
assertP = Assert <$> (stringP "assert" *> predicateP)


declP :: Parser Statement 
declP = Decl <$> (stringP "var" *> bindingP) <*> (stringP ":=" *> expP)


assignP :: Parser Statement
assignP = Assign <$> varP <*> (stringP ":=" *> expP)


ifP :: Parser Statement
ifP = If <$> (stringP "if" *> (parens expP)) <*> (braces blockP) <*> (stringP "else" *> braces blockP) 
     <|> If <$> (stringP "if" *> expP) <*> (braces blockP) <*> (stringP "else" *> braces blockP) <|> 
     If <$> (stringP "if" *> expP) <*> (braces blockP) <*> pure (Block [])


whileP :: Parser Statement
whileP = (\exp pred block -> While pred exp block) <$> (stringP "while" *> expP)
      <*> (predicateP) <*> (braces blockP)
     <|> (\exp pred block -> While pred exp block) <$> (stringP "while" *> (parens expP)) 
     <*> (predicateP) <*> (braces blockP)

statementP :: Parser Statement
statementP = declP <|> assertP <|> assignP <|> ifP <|> whileP <|> const Empty <$> stringP ";"


invariantP :: Parser Predicate
invariantP = (stringP "invariant" *> predicateP) <|> pure (Predicate (Val (BoolVal True)))

-- | ... and one for blocks.

blockP :: Parser Block
blockP = Block <$> (many statementP)


--parser for specifications
specsP :: Parser Specification 
specsP = Requires <$> (stringP "requires" *> predicateP) <|> 
     Ensures <$> ((stringP "ensures") *> predicateP) <|> 
     Modifies <$> ((stringP "modifies") *> nameP)

methodP :: Parser Method
methodP = Method <$> (stringP "method" *> nameP) <*> 
     (parens (many bindingP)) <*> (stringP "returns" *> (parens (many bindingP))) 
     <*> (many specsP) <*> (braces blockP)
     <|> Method <$> (stringP "method" *> nameP) <*> 
     (parens (many bindingP)) <*> pure []
     <*> (many specsP) <*> (braces blockP)
 

parseDafnyExp :: String -> Either P.ParseError Expression
parseDafnyExp = P.parse expP 

parseDafnyStat :: String -> Either P.ParseError Statement
parseDafnyStat = P.parse statementP

parseDafnyFile :: String -> IO (Either P.ParseError Method)
parseDafnyFile = P.parseFromFile (const <$> methodP <*> P.eof) 

{- File-based tests
   ----------------
-}

--tParseFiles :: Test
--tParseFiles = "parse files" ~: TestList [
--                 "abs"  ~: p "dafny/abs.dfy"  wAbs,
--                 "minVal"  ~: p "dafny/findMinVal.dfy"  wMinVal,
--                 "minIndex"  ~: p "dafny/findMinIndex.dfy"  wMinIndex,                 
--                 "minMax"   ~: p "dafny/minMax.dfy"   wMinMax,
--                 "arraySpec" ~: p "dafny/arraySpec.dfy" wArraySpec
--               ] where
--   p fn ast = do
--     result <- parseDafnyFile fn
--     case result of
--       (Left _) -> assert False
--       (Right ast') -> assert (ast == ast')

{- | Unit Tests
      ---------

These unit tests summarize the tests given above.
-}

test_comb = "parsing combinators" ~: TestList [
 P.parse (wsP P.alpha) "a" ~?= Right 'a',
 P.parse (many (wsP P.alpha)) "a b \n   \t c" ~?= Right "abc",
 P.parse (stringP "a") "a" ~?= Right (),
 P.parse (stringP "a") "b" ~?= Left "No parses",
 P.parse (many (stringP "a")) "a  a" ~?= Right [(),()],
 P.parse (constP "&" 'a')  "&  " ~?=  Right 'a',
 P.parse (many (constP "&" 'a'))  "&   &" ~?=  Right "aa",
 P.parse (many (brackets (constP "1" 1))) "[1] [  1]   [1 ]" ~?= Right [1,1,1]
 ]

test_value = "parsing values" ~: TestList [
 P.parse (many intValP) "1 2\n 3" ~?= Right [IntVal 1,IntVal 2,IntVal 3],
 P.parse (many boolValP) "true false\n true" ~?= Right [BoolVal True,BoolVal False,BoolVal True]
 ]

test_exp = "parsing expressions" ~: TestList [
 P.parse (many varP) "x y z" ~?= Right [Name "x", Name "y", Name "z"],
 P.parse (many nameP) "x sfds _" ~?= Right ["x","sfds", "_"],
 P.parse (many uopP) "- -" ~?=  Right [Neg,Neg],
 P.parse (many bopP) "+ >= .." ~?= Right [Plus,Ge]
 ]

test_stat = "parsing statements" ~: TestList [
 P.parse statementP ";" ~?= Right Empty,
 P.parse statementP "x := 3" ~?= Right (Assign (Name "x") (Val (IntVal 3))),
 P.parse statementP "if x { y := true; }" ~?=
    Right (If (Var (Name "x")) (Block [Assign (Name "y") (Val $ BoolVal True), Empty]) (Block [])),
 P.parse statementP "while 0 { }" ~?=
    Right (While (Predicate (Val (BoolVal True))) (Val (IntVal 0)) (Block []))
   ]

-- | Testing summary
--------------------
c = parseDafnyFile "dafny/max.dfy"
test_all :: IO Counts
test_all = runTestTT $ TestList [ test_comb, test_value, test_exp, test_stat] --, tParseFiles ]

