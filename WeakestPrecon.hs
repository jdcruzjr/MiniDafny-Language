
{- | Weakest Preconditions |

method Square (x : int) returns (z : int) 
  requires x > 0 
  ensures z == x * x
{
    var y : int := 0;
    z := 0;
    while y < x 
      invariant y <= x && z == y * x
    {
      z := z + x;
      y := y + 1;
    }
}

and it's full annotation in Hoare Logic:

{ x > 0} ->                               (1)
{ 0 <= x && 0 == 0 * x }
    var y : int := 0;
{ y <= x && 0 == y * x }
    z := 0;
{ y <= x && z == y * x }
    while y < x {
{ y <= x && z == y * x && y < x } ->      (2)
{ y + 1 <= x && z + x == (y + 1) * x }
      z := z + x;
{ y + 1 <= x && z == (y + 1) * x }
      y := y + 1;
{ y <= x && z == y * x }
    }
{ y <= x && z == y * x && !(y < x) } ->   (3)
{ z == x * x }

-}

module WP where

import Printer
import Syntax

import Test.HUnit

-- {Q[x := a] x := a; {Q}

class Subst a where
  subst :: a -> Name -> Expression -> a



instance Subst Expression where
  subst (Var (Proj _ _)) _ _ = error "Ignore arrays for this project"
  subst (Var (Name name)) x e' = if name == x then e' else Var (Name name)
  subst (Val v) _ _ = Val v
  subst (Op1 uop e) x e' = Op1 uop (subst e x e')
  subst (Op2 exp bop exp') x e' = Op2 (subst exp x e') bop (subst exp' x e') 


-- | As an example, consider the loop invariant of Square:
--
--   y <= x && z == y * x
--
--   Or, in our AST representation:

wInv :: Expression
wInv =  Op2 (Op2 (Var (Name "y")) Le (Var (Name "x")))
            Conj
            (Op2 (Var (Name "z")) Eq (Op2 (Var (Name "y")) Times (Var (Name "x"))))

wYPlus1 :: Expression
wYPlus1 = Op2 (Var (Name "y")) Plus (Val (IntVal 1))

wInvSubstYY1 :: Expression
wInvSubstYY1 = Op2 (Op2 (Op2 (Var (Name "y")) Plus (Val (IntVal 1))) Le (Var (Name "x")))
                   Conj
                   (Op2 (Var (Name "z")) Eq (Op2 (Op2 (Var (Name "y")) Plus (Val (IntVal 1))) Times (Var (Name "x"))))

test_substExp :: Test
test_substExp = TestList [ "exp-subst" ~: subst wInv "y" wYPlus1 ~?= wInvSubstYY1 ]

-- | You will also need to implement substitution for predicates, which is
--   simply a matter of invoking substitution for expressions.
 -- subst e x e' 
instance Subst Predicate where
  subst (Predicate exp) x e' = Predicate (subst exp x e')

test_substPred :: Test
test_substPred = TestList [ "pred-subst" ~: subst (Predicate wInv) "y" wYPlus1 ~?= Predicate wInvSubstYY1 ]
testsP = subst (Predicate wInv) "y" wYPlus1


class WP a where
  wp :: a -> Predicate -> Predicate
--   subst :: a -> Name -> Expression -> a
--   wp :: a -> Predicate -> Predicate
-- b ==> P1 && !b ==> P2
instance WP Statement where
  wp (Assert _) p = error "Ignore assert for this project"
  wp (Assign (Proj _ _) _) p = error "Ignore arrays for this project"
  wp (Assign (Name name) exp) p = subst p name exp
  wp (Decl ((name), _) exp) p = subst p name exp
  wp (If exp bl bl') p = 
    let Predicate p1 = wp bl p in 
      let Predicate p2 = wp bl' p in 
        Predicate (Op2 (Op2 exp Implies p1) Conj (Op2 (Op1 Not exp) Implies p2))
  wp (While inv exp bl) p = inv 
  wp Empty p = p

-- | You will also need to implement weakest preconditions for blocks
--   of statements, by repeatedly getting the weakest precondition
--   starting from the end.
--   HINT: folds are your friend.
instance WP Block where
  wp (Block statements) p = foldr (\s p'-> wp s p') p (statements)

-- | The while loop from Square:
-- while y < x
--   invariant y <= x && z == y * x
-- {
--   z := z + x;
--   y := y + 1;
-- }
wSquareWhile :: Statement 
wSquareWhile = While (Predicate (Op2 (Op2 (Var (Name "y")) Le (Var (Name "x"))) Conj (Op2 (Var (Name "z")) Eq (Op2 (Var (Name "y")) Times (Var (Name "x")))))) (Op2 (Var (Name "y")) Lt (Var (Name "x"))) (Block [Assign (Name "z") (Op2 (Var (Name "z")) Plus (Var (Name "x"))),Empty,Assign (Name "y") (Op2 (Var (Name "y")) Plus (Val (IntVal 1))),Empty])

-- | The post condition of Square
-- z == x * x
wWhilePost :: Expression
wWhilePost = Op2 (Var (Name "z")) Eq (Op2 (Var (Name "x")) Times (Var (Name "x")))

-- | The two verification conditions it gives rise to --- (2) and (3) above.
-- y <= x && z == y * x && y < x ==> (y + 1 <= x && z + x == (y + 1) * x)
-- y <= x && z == y * x && ! (y < x) ==> z == x * x

vcsWhile :: [Predicate]
vcsWhile =
  [ Predicate (Op2 (Op2 (Op2 (Op2 (Var (Name "y")) Le (Var (Name "x"))) Conj (Op2 (Var (Name "z")) Eq (Op2 (Var (Name "y")) Times (Var (Name "x"))))) Conj (Op2 (Var (Name "y")) Lt (Var (Name "x")))) Implies (Op2 (Op2 (Op2 (Var (Name "y")) Plus (Val (IntVal 1))) Le (Var (Name "x"))) Conj (Op2 (Op2 (Var (Name "z")) Plus (Var (Name "x"))) Eq (Op2 (Op2 (Var (Name "y")) Plus (Val (IntVal 1))) Times (Var (Name "x"))))))
  ,Predicate (Op2 (Op2 (Op2 (Op2 (Var (Name "y")) Le (Var (Name "x"))) Conj (Op2 (Var (Name "z")) Eq (Op2 (Var (Name "y")) Times (Var (Name "x"))))) Conj (Op1 Not (Op2 (Var (Name "y")) Lt (Var (Name "x"))))) Implies (Op2 (Var (Name "z")) Eq (Op2 (Var (Name "x")) Times (Var (Name "x")))))]

test_vcStmt :: Test
test_vcStmt =
  TestList [ "vc - while" ~: vcStmt (Predicate wWhilePost) wSquareWhile ~?= vcsWhile ]

vcStmt :: Predicate -> Statement -> [Predicate]
vcStmt (Predicate p) (While (Predicate inv) e b) = 
  let Predicate wpBlock = wp b (Predicate inv) in
  let notExp = Op1 Not e in 
  let condition1 = Predicate (Op2 (Op2 inv Conj e) Implies wpBlock) in
  let condition2 = Predicate (Op2 (Op2 inv Conj notExp) Implies p) in 
  condition1 : (condition2 : []) 
vcStmt _ _ = []

-- | Then, calculate the while loop verification conditions for blocks.
vcBlock :: Predicate -> Block -> [Predicate]
--vcBlock p (Block statements) = foldr (\s acc -> (vcStmt p s) ++ acc ) [] (statements)

vcBlock p (Block statements) = vcBlockH p (reverse(statements)) where
  vcBlockH _ [] = []
  vcBlockH p (x : xs) = (vcBlockH (wp x p) xs) ++ (vcStmt p x)

requires :: [Specification] -> Expression
requires [] = Val (BoolVal True)
requires (Requires (Predicate e) : ps) = Op2 e Conj (requires ps)
requires (_ : ps) = requires ps

ensures :: [Specification] -> Expression
ensures [] = Val (BoolVal True)
ensures (Ensures (Predicate e) : ps) = Op2 e Conj (ensures ps)
ensures (_ : ps) = ensures ps


vc :: Method -> [Predicate] 
vc (Method _ _ _ specs (Block ss)) =
  let e = ensures specs
      r = requires specs
      Predicate exp = wp (Block ss) (Predicate e)
  in (Predicate(Op2 r Implies exp)) : vcBlock (Predicate e) (Block ss)

-- x > 0 && true ==> (0 <= x && 0 == 0 * x)
-- y <= x && z == y * x && y < x ==> (y + 1 <= x && z + x == (y + 1) * x)
-- y <= x && z == y * x && ! (y < x) ==> (z == x * x && true)

vcSquare :: [Predicate]
vcSquare = [ Predicate (Op2 (Op2 (Op2 (Var (Name "x")) Gt (Val (IntVal 0))) Conj (Val (BoolVal True))) Implies (Op2 (Op2 (Val (IntVal 0)) Le (Var (Name "x"))) Conj (Op2 (Val (IntVal 0)) Eq (Op2 (Val (IntVal 0)) Times (Var (Name "x"))))))
           , Predicate (Op2 (Op2 (Op2 (Op2 (Var (Name "y")) Le (Var (Name "x"))) Conj (Op2 (Var (Name "z")) Eq (Op2 (Var (Name "y")) Times (Var (Name "x"))))) Conj (Op2 (Var (Name "y")) Lt (Var (Name "x")))) Implies (Op2 (Op2 (Op2 (Var (Name "y")) Plus (Val (IntVal 1))) Le (Var (Name "x"))) Conj (Op2 (Op2 (Var (Name "z")) Plus (Var (Name "x"))) Eq (Op2 (Op2 (Var (Name "y")) Plus (Val (IntVal 1))) Times (Var (Name "x"))))))
           , Predicate (Op2 (Op2 (Op2 (Op2 (Var (Name "y")) Le (Var (Name "x"))) Conj (Op2 (Var (Name "z")) Eq (Op2 (Var (Name "y")) Times (Var (Name "x"))))) Conj (Op1 Not (Op2 (Var (Name "y")) Lt (Var (Name "x"))))) Implies (Op2 (Op2 (Var (Name "z")) Eq (Op2 (Var (Name "x")) Times (Var (Name "x")))) Conj (Val (BoolVal True))))]
vc2Loops :: [Predicate]
vc2Loops = [Predicate (Op2 (Op2 (Op2 (Op2 (Op2 (Var (Name "a")) Gt (Val (IntVal 0))) Conj (Op2 (Var (Name "b")) Gt (Val (IntVal 0)))) Conj (Op2 (Var (Name "c")) Gt (Val (IntVal 0)))) Conj (Val (BoolVal True))) Implies (Op2 (Op2 (Op2 (Val (IntVal 0)) Le (Var (Name "a"))) Conj (Op2 (Val (IntVal 0)) Eq (Val (IntVal 0)))) Conj (Op2 (Var (Name "c")) Eq (Op2 (Op2 (Val (IntVal 0)) Plus (Val (IntVal 0))) Plus (Var (Name "c")))))),
            Predicate (Op2 (Op2 (Op2 (Op2 (Op2 (Var (Name "x")) Le (Var (Name "a"))) Conj (Op2 (Var (Name "y")) Eq (Val (IntVal 0)))) Conj (Op2 (Var (Name "z")) Eq (Op2 (Op2 (Var (Name "x")) Plus (Var (Name "y"))) Plus (Var (Name "c"))))) Conj (Op2 (Var (Name "x")) Lt (Var (Name "a")))) Implies (Op2 (Op2 (Op2 (Op2 (Var (Name "x")) Plus (Val (IntVal 1))) Le (Var (Name "a"))) Conj (Op2 (Var (Name "y")) Eq (Val (IntVal 0)))) Conj (Op2 (Op2 (Var (Name "z")) Plus (Val (IntVal 1))) Eq (Op2 (Op2 (Op2 (Var (Name "x")) Plus (Val (IntVal 1))) Plus (Var (Name "y"))) Plus (Var (Name "c")))))),
            Predicate (Op2 (Op2 (Op2 (Op2 (Op2 (Var (Name "x")) Le (Var (Name "a"))) Conj (Op2 (Var (Name "y")) Eq (Val (IntVal 0)))) Conj (Op2 (Var (Name "z")) Eq (Op2 (Op2 (Var (Name "x")) Plus (Var (Name "y"))) Plus (Var (Name "c"))))) Conj (Op1 Not (Op2 (Var (Name "x")) Lt (Var (Name "a"))))) Implies (Op2 (Op2 (Op2 (Var (Name "y")) Le (Var (Name "b"))) Conj (Op2 (Var (Name "x")) Eq (Var (Name "a")))) Conj (Op2 (Var (Name "z")) Eq (Op2 (Op2 (Var (Name "a")) Plus (Var (Name "y"))) Plus (Var (Name "c")))))),
            Predicate (Op2 (Op2 (Op2 (Op2 (Op2 (Var (Name "y")) Le (Var (Name "b"))) Conj (Op2 (Var (Name "x")) Eq (Var (Name "a")))) Conj (Op2 (Var (Name "z")) Eq (Op2 (Op2 (Var (Name "a")) Plus (Var (Name "y"))) Plus (Var (Name "c"))))) Conj (Op2 (Var (Name "y")) Lt (Var (Name "b")))) Implies (Op2 (Op2 (Op2 (Op2 (Var (Name "y")) Plus (Val (IntVal 1))) Le (Var (Name "b"))) Conj (Op2 (Var (Name "x")) Eq (Var (Name "a")))) Conj (Op2 (Op2 (Var (Name "z")) Plus (Val (IntVal 1))) Eq (Op2 (Op2 (Var (Name "a")) Plus (Op2 (Var (Name "y")) Plus (Val (IntVal 1)))) Plus (Var (Name "c")))))),
            Predicate (Op2 (Op2 (Op2 (Op2 (Op2 (Var (Name "y")) Le (Var (Name "b"))) Conj (Op2 (Var (Name "x")) Eq (Var (Name "a")))) Conj (Op2 (Var (Name "z")) Eq (Op2 (Op2 (Var (Name "a")) Plus (Var (Name "y"))) Plus (Var (Name "c"))))) Conj (Op1 Not (Op2 (Var (Name "y")) Lt (Var (Name "b"))))) Implies (Op2 (Op2 (Var (Name "z")) Eq (Op2 (Op2 (Var (Name "a")) Plus (Var (Name "b"))) Plus (Var (Name "c")))) Conj (Val (BoolVal True))))]

test_vc_method :: Test
test_vc_method = TestList [ "vc square" ~: vc wSquare ~?= vcSquare ]

ppPredList (x:xs) = (pretty x): ppPredList xs
ppPredList [] = []

x = ppPredList (vc wTwoLoops) 
y = ppPredList vc2Loops

testTwoLoops :: Test
testTwoLoops = TestList [ "vc two loops" ~: vc wTwoLoops ~?= vc2Loops ]
