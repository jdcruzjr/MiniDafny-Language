
{- | Z3 integration | -}

module Z3 where

import Syntax
import Data.List(intersperse)
import Text.PrettyPrint ( (<+>), Doc )
import qualified Text.PrettyPrint as PP

import System.Process(readProcessWithExitCode)
import Data.Set(Set)
import qualified Data.Set as Set

-- | This is the function you need to implement. You can ignore arrays, as with
--   the weakest precondition homework, but everything else needs to be handled!

calcVariables :: Expression -> Set Name 
calcVariables (Var (Name name)) = Set.singleton name
calcVariables (Var _) = Set.empty
calcVariables (Val _) = Set.empty 
calcVariables (Op1 (uop) (expr)) = calcVariables expr 
calcVariables (Op2 (expr) bop (expr2)) =  Set.union (calcVariables expr) (calcVariables expr2)

declare :: Set Name -> String
declare s = declareH (Set.toList s) where
  declareH [] = ""
  declareH (x : xs) = "(declare-const " ++ x ++ " Int)\n" ++ (declareH xs)

assertion :: Expression -> String
assertion (Var (Name name)) = name
assertion (Var _) = ""
assertion (Val (BoolVal val)) = if val then "true" else "false"
assertion (Val (IntVal val)) = show val
assertion (Val _) = ""
assertion (Op1 Neg expr) = "(- " ++ (assertion expr) ++ ")"
assertion (Op1 Not expr) = "(not " ++ (assertion expr) ++ ")"
assertion (Op1 _ expr) = ""
assertion (Op2 expr1 (Plus) expr2) = "(+ " ++ (assertion expr1) ++ " " ++ (assertion expr2) ++ ")"
assertion (Op2 expr1 (Minus) expr2) = "(- " ++ (assertion expr1) ++ " " ++ (assertion expr2) ++ ")"
assertion (Op2 expr1 (Times) expr2) = "(* " ++ (assertion expr1) ++ " " ++ (assertion expr2) ++ ")"
assertion (Op2 expr1 (Divide) expr2) = "(div " ++ (assertion expr1) ++ " " ++ (assertion expr2) ++ ")"
assertion (Op2 expr1 (Modulo) expr2) = "(mod " ++ (assertion expr1) ++ " " ++ (assertion expr2) ++ ")"
assertion (Op2 expr1 (Eq) expr2) = "(= " ++ (assertion expr1) ++ " " ++ (assertion expr2) ++ ")"
assertion (Op2 expr1 (Neq) expr2) = "(distinct " ++ (assertion expr1) ++ " " ++ (assertion expr2) ++ ")"
assertion (Op2 expr1 (Gt) expr2) = "(> " ++ (assertion expr1) ++ " " ++ (assertion expr2) ++ ")"
assertion (Op2 expr1 (Ge) expr2) = "(>= " ++ (assertion expr1) ++ " " ++ (assertion expr2) ++ ")"
assertion (Op2 expr1 (Lt) expr2) = "(< " ++ (assertion expr1) ++ " " ++ (assertion expr2) ++ ")"
assertion (Op2 expr1 (Le) expr2) = "(<= " ++ (assertion expr1) ++ " " ++ (assertion expr2) ++ ")"
assertion (Op2 expr1 (Conj) expr2) = "(and " ++ (assertion expr1) ++ " " ++ (assertion expr2) ++ ")"
assertion (Op2 expr1 (Disj) expr2) = "(or " ++ (assertion expr1) ++ " " ++ (assertion expr2) ++ ")"
assertion (Op2 expr1 (Implies) expr2) = "(=> " ++ (assertion expr1) ++ " " ++ (assertion expr2) ++ ")"
assertion (Op2 expr1 (Iff) expr2) = "(and " ++ "(=> " ++ (assertion expr1) ++ " " ++ (assertion expr2) ++ ")" 
  ++ " " ++ "(=> " ++ (assertion expr2) ++ " " ++ (assertion expr1) ++ "))"


toSMT :: Predicate -> String
toSMT (Predicate expr) = 
  let set = calcVariables expr in
    let decls = (declare set)
        asserts = "(assert (not " ++ (assertion expr) ++ "))\n"
        check = "(check-sat)"
        in (decls ++ asserts) ++ check

-- | The name of the z3 executable. Change this to whatever it is in your system:
--   In unix based systems, this is just "z3".
--   In Windows, it will be the name of the executable that was installed alongside Dafny.
z3 :: String
z3 = "z3"

test1 = toSMT (Predicate (Op2 (Op2 (Op2 (Var (Name "x")) Gt (Val (IntVal 0))) Conj (Val (BoolVal True))) Implies (Op2 (Op2 (Val (IntVal 0)) Le (Var (Name "x"))) Conj (Op2 (Val (IntVal 0)) Eq (Op2 (Val (IntVal 0)) Times (Var (Name "x")))))))
test2 = toSMT (Predicate (Op2 (Op2 (Op2 (Op2 (Var (Name "y")) Le (Var (Name "x"))) Conj (Op2 (Var (Name "z")) Eq (Op2 (Var (Name "y")) Times (Var (Name "x"))))) Conj (Op2 (Var (Name "y")) Lt (Var (Name "x")))) Implies (Op2 (Op2 (Op2 (Var (Name "y")) Plus (Val (IntVal 1))) Le (Var (Name "x"))) Conj (Op2 (Op2 (Var (Name "z")) Plus (Var (Name "x"))) Eq (Op2 (Op2 (Var (Name "y")) Plus (Val (IntVal 1))) Times (Var (Name "x")))))))
test3 = toSMT (Predicate (Op2 (Op2 (Op2 (Op2 (Var (Name "y")) Le (Var (Name "x"))) Conj (Op2 (Var (Name "z")) Eq (Op2 (Var (Name "y")) Times (Var (Name "x"))))) Conj (Op1 Not (Op2 (Var (Name "y")) Lt (Var (Name "x"))))) Implies (Op2 (Op2 (Var (Name "z")) Eq (Op2 (Var (Name "x")) Times (Var (Name "x")))) Conj (Val (BoolVal True)))))
test4 = calcVariables ((Op2 (Op2 (Op2 (Op2 (Var (Name "y")) Le (Var (Name "x"))) Conj (Op2 (Var (Name "z")) Eq (Op2 (Var (Name "y")) Times (Var (Name "x"))))) Conj (Op2 (Var (Name "y")) Lt (Var (Name "x")))) Implies (Op2 (Op2 (Op2 (Var (Name "y")) Plus (Val (IntVal 1))) Le (Var (Name "x"))) Conj (Op2 (Op2 (Var (Name "z")) Plus (Var (Name "x"))) Eq (Op2 (Op2 (Var (Name "y")) Plus (Val (IntVal 1))) Times (Var (Name "x")))))))
test5 = (Predicate (Op2 (Val (BoolVal True)) Implies (Op2 (Op2 (Op2 (Var (Name "x")) Lt (Var (Name "y"))) Implies (Op2 (Op2 (Op2 (Op2 (Var (Name "x")) Le (Var (Name "x"))) Conj (Op2 (Var (Name "x")) Le (Var (Name "y")))) Conj (Op2 (Op2 (Var (Name "x")) Eq (Var (Name "x"))) Disj (Op2 (Var (Name "x")) Eq (Var (Name "y"))))) Conj (Op2 (Op2 (Op2 (Op2 (Var (Name "y")) Ge (Var (Name "x"))) Conj (Op2 (Var (Name "y")) Ge (Var (Name "y")))) Conj (Op2 (Op2 (Var (Name "y")) Eq (Var (Name "x"))) Disj (Op2 (Var (Name "y")) Eq (Var (Name "y"))))) Conj (Val (BoolVal True))))) Conj (Op2 (Op1 Not (Op2 (Var (Name "x")) Lt (Var (Name "y")))) Implies (Op2 (Op2 (Op2 (Op2 (Var (Name "y")) Le (Var (Name "x"))) Conj (Op2 (Var (Name "y")) Le (Var (Name "y")))) Conj (Op2 (Op2 (Var (Name "y")) Eq (Var (Name "x"))) Disj (Op2 (Var (Name "y")) Eq (Var (Name "y"))))) Conj (Op2 (Op2 (Op2 (Op2 (Var (Name "x")) Ge (Var (Name "x"))) Conj (Op2 (Var (Name "x")) Ge (Var (Name "y")))) Conj (Op2 (Op2 (Var (Name "x")) Eq (Var (Name "x"))) Disj (Op2 (Var (Name "x")) Eq (Var (Name "y"))))) Conj (Val (BoolVal True))))))))

-- | This function uses "toSMT" in order to write a file, and invoke z3 on it, checking its
--   output. You're welcome to modify this function as you see fit, the only thing we will
--   automatically test is your "toSMT" function.
convertAndCheck :: Predicate -> String -> IO Bool
convertAndCheck p fn = do
  writeFile fn (toSMT p)
  (_exitCode, stdout, _stderr) <- readProcessWithExitCode z3 [fn] ""
  case stdout of
    's':'a':'t':_ -> return False
    'u':'n':'s':'a':'t':_ -> return True
    _ -> error $ "Z3 output was neither sat or unsat: " ++ stdout
