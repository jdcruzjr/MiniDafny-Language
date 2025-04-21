
module Syntax where

import Data.List(intersperse)
import Data.Map (Map)
import qualified Data.Map as Map
import Text.PrettyPrint ( (<+>), Doc )
import qualified Text.PrettyPrint as PP
import Test.QuickCheck(Arbitrary(..),Gen)
import qualified Test.QuickCheck as QC
import Control.Monad(mapM_)
import qualified Data.Char as Char

import Test.HUnit


data Method = Method Name [Binding] [Binding] [Specification] Block
  deriving (Eq, Show)

-- | A Name is just a type synonym for a String:

type Name = String            -- either the name of a variable or the name of a method

-- | A Binding is a Name together with its Type:

type Binding = (Name, Type)


data Type = TInt | TBool | TArrayInt
  deriving (Eq, Show)


data Specification =
    Requires Predicate
  | Ensures  Predicate
  | Modifies Name
  deriving (Eq, Show)


data Predicate = Predicate [Binding] Expression
  deriving (Eq, Show)

newtype Block = Block [ Statement ]                 -- s1 ... sn 
  deriving (Eq, Show)
  
data Statement =
    Decl Binding Expression            -- var x : int := e;
  | New  Binding Expression            -- var x : array<int> := new int[e];
  | Assert Predicate                   -- (assert FOO)
  | Assign Var Expression              -- x := e
  | If Expression Block Block          -- if e { s1 } else { s2 }
  | While [Predicate] Expression Block -- while e [invariant P] { s }
  | Empty                              -- 
  deriving (Eq, Show)

-- | Expressions are variables, literal constants, or operators applied
-- | to sub-expressions:

data Expression =
    Var Var                            -- global variables x and table indexing
  | Val Value                          -- literal values
  | Op1 Uop Expression                 -- unary operators
  | Op2 Expression Bop Expression      -- binary operators
  deriving (Eq, Show)

data Value =
    IntVal Int         -- 1
  | BoolVal Bool       -- false, true
  | ArrayVal [Int]
  deriving (Eq, Show, Ord)

data Uop =
    Neg   -- `-` :: Int -> Int
  | Not   -- `not` :: a -> Bool
  | Len   -- `.Length` :: Array -> Int
  deriving (Eq, Show, Enum, Bounded)

data Bop =
    Plus     -- `+`  :: Int -> Int -> Int
  | Minus    -- `-`  :: Int -> Int -> Int
  | Times    -- `*`  :: Int -> Int -> Int
  | Divide   -- `/`  :: Int -> Int -> Int   -- floor division
  | Modulo   -- `%`  :: Int -> Int -> Int   -- modulo
  | Eq       -- `==` :: a -> a -> Bool
  | Neq      -- `!=` :: a -> a -> Bool> 
  | Gt       -- `>`  :: a -> a -> Bool
  | Ge       -- `>=` :: a -> a -> Bool
  | Lt       -- `<`  :: a -> a -> Bool
  | Le       -- `<=` :: a -> a -> Bool
  | Conj     -- `&&` :: Bool -> Bool -> Bool
  | Disj     -- `||` :: Bool -> Bool -> Bool
  | Implies  -- `==>` :: Bool -> Bool -> Bool
  | Iff      -- `<->` :: Bool -> Bool -> Bool
  deriving (Eq, Show, Enum, Bounded)

var :: String -> Expression
var = Var . Name

-- abs.dfy
wAbs = Method "Abs" [("r",TInt)] [("absR",TInt)] []
              (Block [If (Op2 (Var (Name "r")) Lt (Val (IntVal 0)))
                         (Block [Assign (Name "absR") (Op1 Neg (Var (Name "r"))),Empty])
                         (Block [Assign (Name "absR") (Var (Name "r")),Empty])])
-- findMinVal.dfy
wMinVal = Method "FindMinVal" [("a",TArrayInt)] [("min",TInt)] [Requires (Predicate [] (Op2 (Op1 Len (Var (Name "a"))) Gt (Val (IntVal 0)))),Ensures (Predicate [("i",TInt)] (Op2 (Op2 (Op2 (Op2 (Val (IntVal 0)) Le (Op2 (Var (Name "i")) Conj (Var (Name "i")))) Lt (Op1 Len (Var (Name "a")))) Implies (Var (Name "min"))) Le (Var (Proj (Var (Name "a")) (Var (Name "i"))))))] (Block [Assign (Name "min") (Var (Proj (Var (Name "a")) (Val (IntVal 0)))),Empty,Decl ("i",TInt) (Val (IntVal 1)),Empty,While [] (Op2 (Var (Name "i")) Lt (Op1 Len (Var (Name "a")))) (Block [If (Op2 (Var (Proj (Var (Name "a")) (Var (Name "i")))) Lt (Var (Name "min"))) (Block [Assign (Name "min") (Var (Proj (Var (Name "a")) (Var (Name "i")))),Empty]) (Block []),Assign (Name "i") (Op2 (Var (Name "i")) Plus (Val (IntVal 1))),Empty])])

-- findMinIndex.dfy
wMinIndex = Method "FindMinIndex" [("a",TArrayInt)] [("index",TInt)] [] (Block [Decl ("min",TInt) (Var (Proj (Var (Name "a")) (Val (IntVal 0)))),Empty,Decl ("i",TInt) (Val (IntVal 0)),Empty,Assign (Name "index") (Val (IntVal 0)),Empty,While [] (Op2 (Var (Name "i")) Lt (Op1 Len (Var (Name "a")))) (Block [If (Op2 (Var (Proj (Var (Name "a")) (Var (Name "i")))) Lt (Var (Name "min"))) (Block [Assign (Name "min") (Var (Proj (Var (Name "a")) (Var (Name "i")))),Empty,Assign (Name "index") (Val (IntVal 1)),Empty]) (Block []),Assign (Name "i") (Op2 (Var (Name "i")) Plus (Val (IntVal 1))),Empty])])

-- minMax.dfy
wMinMax =  Method "MinMax" [("x",TInt),("y",TInt)] [("min",TInt),("max",TInt)] [] (Block [If (Op2 (Var (Name "x")) Lt (Var (Name "y"))) (Block [Assign (Name "min") (Var (Name "x")),Empty,Assign (Name "max") (Var (Name "y")),Empty]) (Block [Assign (Name "max") (Var (Name "x")),Empty,Assign (Name "min") (Var (Name "y")),Empty])])

-- arraySpec.dfy
wArraySpec = Method "ArrayTest" [("a",TArrayInt)] [("x",TInt)] [Requires (Predicate [] (Op2 (Op1 Len (Var (Name "a"))) Gt (Val (IntVal 0)))),Requires (Predicate [("i",TInt)] (Op2 (Op2 (Op2 (Op2 (Val (IntVal 0)) Le (Op2 (Var (Name "i")) Conj (Var (Name "i")))) Lt (Op1 Len (Var (Name "a")))) Implies (Var (Proj (Var (Name "a")) (Var (Name "i"))))) Gt (Val (IntVal 0)))),Ensures (Predicate [] (Op2 (Var (Name "x")) Gt (Val (IntVal 0))))] (Block [Assign (Name "x") (Var (Proj (Var (Name "a")) (Val (IntVal 0)))),Empty])

wIntDiv = Method "IntDiv" [("m",TInt),("n",TInt)] [("d",TInt),("r",TInt)] [Requires (Predicate [] (Op2 (Var (Name "n")) Gt (Val (IntVal 0)))),Ensures (Predicate [] (Op2 (Var (Name "m")) Eq (Op2 (Op2 (Var (Name "d")) Times (Var (Name "n"))) Plus (Var (Name "r"))))),Ensures (Predicate [] (Op2 (Op2 (Val (IntVal 0)) Le (Op2 (Var (Name "r")) Conj (Var (Name "r")))) Lt (Var (Name "n"))))] (Block [Assign (Name "d") (Op2 (Var (Name "m")) Divide (Var (Name "n"))),Empty,Assign (Name "r") (Op2 (Var (Name "m")) Modulo (Var (Name "n"))),Empty])

wReq = Method "Req" [("x",TInt)] [("y",TInt)] [Requires (Predicate [] (Op2 (Var (Name "x")) Gt (Val (IntVal 0)))),Ensures (Predicate [] (Op2 (Var (Name "y")) Gt (Val (IntVal 0))))] (Block [Assign (Name "y") (Var (Name "x")),Empty])

wAssign = Method "Assign" [("x",TInt)] [("y",TInt)] [] (Block [Assign (Name "y") (Var (Name "x")),Empty])

wArrayTest = Method "ArrayTest" [("a",TArrayInt)] [("x",TInt)] [Requires (Predicate [] (Op2 (Op1 Len (Var (Name "a"))) Gt (Val (IntVal 0)))),Ensures (Predicate [] (Op2 (Var (Name "x")) Gt (Val (IntVal 0))))] (Block [Assign (Name "x") (Var (Proj (Var (Name "a")) (Val (IntVal 0)))),Empty])

wEnsures = Method "Ensures" [("x",TInt)] [("y",TInt)] [Ensures (Predicate [] (Op2 (Var (Name "y")) Eq (Var (Name "x"))))] (Block [Assign (Name "y") (Var (Name "x")),Empty])

wTwoLoops = (Method "TwoLoops" [("a",TInt),("b",TInt),("c",TInt)] [("x",TInt),("y",TInt),("z",TInt)] [Requires (Predicate [] 
  (Op2 (Var (Name "a")) Gt (Val (IntVal 0)))),Requires (Predicate [] (Op2 (Var (Name "b")) Gt (Val (IntVal 0)))),Requires 
  (Predicate [] (Op2 (Var (Name "c")) Gt (Val (IntVal 0)))),Ensures (Predicate [] (Op2 (Var (Name "z")) Eq (
  Op2 (Op2 (Var (Name "a")) Plus (Var (Name "b"))) Plus (Var (Name "c")))))] (Block [Assign (Name "x") 
  (Val (IntVal 0)),Empty,Assign (Name "y") (Val (IntVal 0)),Empty,Assign (Name "z") 
  (Var (Name "c")),Empty,While [Predicate [] (Op2 (Var (Name "x")) Le (Var (Name "a"))),
  Predicate [] (Op2 (Var (Name "y")) Eq (Val (IntVal 0))),Predicate [] (Op2 (Var (Name "z")) Eq (Op2 (Op2 (Var (Name "x"))
   Plus (Var (Name "y"))) Plus (Var (Name "c"))))] (Op2 (Var (Name "x")) Lt (Var (Name "a"))) (Block [Assign (Name "x") 
   (Op2 (Var (Name "x")) Plus (Val (IntVal 1))),Empty,Assign (Name "z") (Op2 (Var (Name "z")) Plus (Val (IntVal 1))),Empty]),
   While [Predicate [] (Op2 (Var (Name "y")) Le (Var (Name "b"))),Predicate [] (Op2 (Var (Name "x")) Eq (Var (Name "a"))),Predicate [] 
   (Op2 (Var (Name "z")) Eq (Op2 (Op2 (Var (Name "a")) Plus (Var (Name "y"))) Plus (Var (Name "c"))))] (Op2 (Var (Name "y")) Lt (Var (Name "b"))) (Block [Assign (Name "y") (Op2 (Var (Name "y")) Plus (Val (IntVal 1))),Empty,Assign (Name "z") (Op2 (Var (Name "z")) Plus (Val (IntVal 1))),Empty])]))

wManyBinops = Method "ManyBinops" [("x",TInt),("y",TInt),("a",TBool),("b",TBool)] [("c",TInt)] [Requires (Predicate [] (Op2 (Var (Name "y")) Neq (Val (IntVal 0))))] (Block [If (Op2 (Op2 (Op2 (Var (Name "a")) Conj (Var (Name "b"))) Disj (Op2 (Op2 (Op1 Not (Var (Name "a"))) Conj (Var (Name "x"))) Lt (Var (Name "y")))) Disj (Op2 (Var (Name "x")) Ge (Var (Name "y")))) (Block [Assign (Name "c") (Op2 (Op2 (Var (Name "x")) Plus (Var (Name "y"))) Minus (Op2 (Var (Name "x")) Divide (Var (Name "y")))),Empty]) (Block [Assign (Name "c") (Op2 (Op2 (Var (Name "x")) Times (Var (Name "y"))) Modulo (Var (Name "y"))),Empty])])
wMinMax2 = Method "MinMax" [("x",TInt),("y",TInt)] [("min",TInt),("max",TInt)] [] (Block [If (Op2 (Var (Name "x")) Lt (Var (Name "y"))) (Block [Assign (Name "min") (Var (Name "x")),Empty,Assign (Name "max") (Var (Name "y")),Empty]) (Block [Assign (Name "max") (Var (Name "x")),Empty,Assign (Name "min") (Var (Name "y")),Empty])])

class PP a where
  pp :: a -> Doc

pretty :: PP a => a -> String
pretty = PP.render . pp

oneLine :: PP a => a -> String
oneLine = PP.renderStyle (PP.style {PP.mode=PP.OneLineMode}) . pp

instance PP Uop where
  pp Neg = PP.char '-'
  pp Not = PP.char '!'
  pp Len = PP.text ".Length"
  
instance PP String where
  pp = PP.text

instance PP Int where
  pp = PP.int

instance PP Bool where
  pp True = PP.text "true"
  pp False = PP.text "false"

ppIntListAux :: [Int] -> Doc
ppIntListAux [] = PP.empty
ppIntListAux [x] = PP.int x
ppIntListAux (x:xs) = PP.int x <> PP.comma <> ppIntListAux xs

instance PP [Int] where
  pp list = PP.brackets $ ppIntListAux list
  
instance PP Value where
  pp (IntVal i)  = pp i
  pp (BoolVal b) = pp b
  pp (ArrayVal l)  = pp l

instance PP Bop where
  pp Plus = PP.char '+'
  pp Minus = PP.char '-'
  pp Times = PP.char '*'
  pp Divide = PP.char '/'
  pp Modulo = PP.char '%'
  pp Eq = PP.text "==" 
  pp Neq = PP.text "!="
  pp Gt = PP.char '>'
  pp Ge = PP.text ">=" 
  pp Lt = PP.char '<' 
  pp Le = PP.text "<=" 
  pp Conj = PP.text "&&"
  pp Disj = PP.text "||"
  pp Implies = PP.text "==>"
  pp Iff = PP.text "<==>"

instance PP Type where
  pp TInt  = PP.text "int"
  pp TBool = PP.text "bool"
  pp TArrayInt = PP.text "array<int>"

instance PP Binding where
  pp (x, t) = PP.text x <+> PP.text ":" <+> pp t

instance PP Expression where
  pp (Var v) = pp v
  pp (Val v) = pp v
  pp (Op1 Len v) = (if isBase v then pp v else PP.parens (pp v)) <> pp Len  
  pp (Op1 o v) = pp o <+> if isBase v then pp v else PP.parens (pp v)
  pp e@Op2{} = ppPrec 0 e  where
     ppPrec n (Op2 e1 bop e2) =
        ppParens (level bop < n) $
           ppPrec (level bop) e1 <+> pp bop <+> ppPrec (level bop + 1) e2
     ppPrec _ e' = pp e'
     ppParens b = if b then PP.parens else id

isBase :: Expression -> Bool
isBase Val{} = True
isBase Var{} = True
isBase Op1{} = True
isBase _ = False

level :: Bop -> Int
level Times  = 7
level Divide = 7
level Plus   = 5
level Minus  = 5
level Conj   = 3
level _      = 2    -- comparison operators

instance PP Var where
  pp (Name name) = PP.text name
  pp (Proj array index) = pp array <> PP.brackets (pp index)
 
instance PP Block where
  pp (Block []) = PP.empty
  pp (Block [statement]) = pp statement
  pp (Block statements) = (PP.vcat $ blockAux statements) where
    blockAux [] = []
    blockAux (x:xs) = pp x : blockAux xs

instance PP Statement where
  pp Empty = PP.empty
  pp (Decl binding exp) = (PP.text "var" <+> pp binding <+> PP.text ":=" <+>
   pp exp) <> PP.semi
  pp (New binding exp) = (PP.text "var" <+> pp binding <+> PP.text ":=" <+>
   PP.text "new" <+> pp exp) <> PP.semi
  pp (Assert pred) = (PP.text "assert" <+> pp pred) <> PP.semi
  pp (Assign var exp) = (pp var <+> PP.text ":=" <+> pp exp) <> PP.semi

  pp (If exp block1 (Block [])) = (PP.hang (PP.text "if" <+> pp exp <+> 
    PP.lbrace) 4 (pp block1)) PP.$$ PP.rbrace

  pp (If exp block1 block2) = (PP.hang ((PP.hang (PP.text "if" <+> pp exp 
    <+> PP.lbrace) 4 (pp block1)) PP.$$ (PP.rbrace 
      <+> PP.text "else" <+> PP.lbrace)) 4 (pp block2)) PP.$$ PP.rbrace

  pp (While [] exp block) = (PP.hang (PP.text "while" <+> pp exp <+> 
    PP.lbrace) 2 (pp block)) PP.$$ PP.rbrace
    
  pp (While predLists exp block) = 
    (PP.hang
      ((PP.hang (PP.text "while" <+> pp exp) 2 (PP.vcat $ whileAux predLists)) 
      PP.$$ (PP.lbrace <+> PP.text ""))
    (2) 
    (pp block))
    PP.$$ PP.rbrace
    where
      whileAux [] = []
      whileAux (x : xs) = PP.text "invariant" <+> pp x : whileAux xs

bindAux :: [Binding] -> Doc
bindAux [] = PP.empty
bindAux [x] = pp x
bindAux (x:xs) = pp x <> PP.comma <> bindAux xs

instance PP Predicate where
  pp (Predicate [] exp) = pp exp
  pp (Predicate bindList exp) = PP.text "forall" <+> bindAux bindList <+> 
    PP.text "::" <+> pp exp where
      bindAux [] = PP.empty
      bindAux [x] = pp x
      bindAux (x:xs) = pp x <> PP.comma <> bindAux xs

instance PP Method where
  pp (Method name bList1 bList2 specList block) =
    (PP.hang
      ((PP.hang (PP.text "method" <+> pp name <+> (PP.parens $ bindAux bList1)
       <+> PP.text "returns" <+> (PP.parens $ bindAux bList2)) 
      (2) (PP.vcat $ specsAux specList)) PP.$$ (PP.lbrace <+> PP.text ""))
    (2) 
    (pp block))
    PP.$$ PP.rbrace
      where
        specsAux [] = []
        specsAux (Requires p : xs) = PP.text "requires" <+> pp p : specsAux xs
        specsAux (Ensures p : xs) = PP.text "ensures" <+> pp p : specsAux xs
        specsAux (Modifies n : xs) = PP.text "modifies" <+> pp n : specsAux xs
