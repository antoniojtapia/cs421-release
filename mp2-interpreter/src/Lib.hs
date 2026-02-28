module Lib where
import Data.HashMap.Strict as H (HashMap, empty, fromList, insert, lookup, union)


--- Data Types
--- ----------

--- ### Environments and Results

type Env  = H.HashMap String Val
type PEnv = H.HashMap String Stmt

type Result = (String, PEnv, Env)

--- ### Values

data Val = IntVal Int
         | BoolVal Bool
         | CloVal [String] Exp Env
         | ExnVal String
    deriving (Eq)

instance Show Val where
    show (IntVal i) = show i
    show (BoolVal i) = show i
    show (CloVal xs body env) = "<" ++ show xs   ++ ", "
                                    ++ show body ++ ", "
                                    ++ show env  ++ ">"
    show (ExnVal s) = "exn: " ++ s

--- ### Expressions

data Exp = IntExp Int
         | BoolExp Bool
         | FunExp [String] Exp
         | LetExp [(String,Exp)] Exp
         | AppExp Exp [Exp]
         | IfExp Exp Exp Exp
         | IntOpExp String Exp Exp
         | BoolOpExp String Exp Exp
         | CompOpExp String Exp Exp
         | VarExp String
    deriving (Show, Eq)

--- ### Statements

data Stmt = SetStmt String Exp
          | PrintStmt Exp
          | QuitStmt
          | IfStmt Exp Stmt Stmt
          | ProcedureStmt String [String] Stmt
          | CallStmt String [Exp]
          | SeqStmt [Stmt]
    deriving (Show, Eq)

--- Primitive Functions
--- -------------------

intOps :: H.HashMap String (Int -> Int -> Int)
intOps = H.fromList [ ("+", (+))
                    , ("-", (-))
                    , ("*", (*))
                    , ("/", (div))
                    ]

boolOps :: H.HashMap String (Bool -> Bool -> Bool)
boolOps = H.fromList [ ("and", (&&))
                     , ("or", (||))
                     ]

compOps :: H.HashMap String (Int -> Int -> Bool)
compOps = H.fromList [ ("<", (<))
                     , (">", (>))
                     , ("<=", (<=))
                     , (">=", (>=))
                     , ("/=", (/=))
                     , ("==", (==))
                     ]

--- Problems
--- ========

--- Lifting Functions
--- -----------------

liftIntOp :: (Int -> Int -> Int) -> Val -> Val -> Val
liftIntOp op (IntVal x) (IntVal y) = IntVal $ op x y
liftIntOp _ _ _ = ExnVal "Cannot lift"

liftBoolOp :: (Bool -> Bool -> Bool) -> Val -> Val -> Val
liftBoolOp op (BoolVal x) (BoolVal y) = BoolVal $ op x y
liftBoolOp _ _ _ = ExnVal "Cannot lift"

liftCompOp :: (Int -> Int -> Bool) -> Val -> Val -> Val
liftCompOp op (IntVal x) (IntVal y) = BoolVal $ op x y
liftCompOp _ _ _ = ExnVal "Cannot lift"

--- Eval
--- ----

eval :: Exp -> Env -> Val

--- ### Constants

eval (IntExp i)  _ = IntVal i
eval (BoolExp i) _ = BoolVal i

--- ### Variables

eval (VarExp s) env
    | Just val <- H.lookup s env = val
    | otherwise = ExnVal "No match in env"

--- ### Arithmetic

eval (IntOpExp "/" e1 e2) env -- handle division by 0 case separately
    | IntVal 0 <- v2 = ExnVal "Division by 0"
    | otherwise = liftIntOp div v1 v2
        where (v1, v2) = (eval e1 env, eval e2 env)
eval (IntOpExp op e1 e2) env = liftIntOp intOp (eval e1 env) (eval e2 env)
    where Just intOp = H.lookup op intOps

--- ### Boolean and Comparison Operators

eval (BoolOpExp op e1 e2) env = liftBoolOp boolOp (eval e1 env) (eval e2 env)
    where Just boolOp = H.lookup op boolOps

eval (CompOpExp op e1 e2) env = liftCompOp compOp (eval e1 env) (eval e2 env)
    where Just compOp = H.lookup op compOps

--- ### If Expressions

eval (IfExp e1 e2 e3) env
    | BoolVal True <- eval e1 env = eval e2 env
    | BoolVal False <- eval e1 env = eval e3 env
    | otherwise = ExnVal "Condition is not a Bool"

--- ### Functions and Function Application

eval (FunExp params body) env = CloVal params body env

eval (AppExp e1 args) env
    | CloVal params body cloEnv <- eval e1 env =
        let argVals = (`eval` env) <$> args
            newEnv = H.union (H.fromList $ zip params argVals) cloEnv
        in eval body newEnv
    | otherwise = ExnVal "Apply to non-closure"

--- ### Let Expressions

eval (LetExp pairs body) env =
    let newEnv = H.union (H.fromList $ (\(s,e) -> (s, eval e env)) <$> pairs) env
    in eval body newEnv

--- Statements
--- ----------

-- Statement Execution
-- -------------------

exec :: Stmt -> PEnv -> Env -> Result
exec (PrintStmt e) penv env = (val, penv, env)
    where val = show $ eval e env

--- ### Set Statements

exec (SetStmt var e) penv env = ("", penv, H.insert var val env)
    where val = eval e env

--- ### Sequencing

exec (SeqStmt []) penv env = ("", penv, env)
exec (SeqStmt (s:ss)) penv env =
    let (out1, penv2, env2) = exec s penv env
        (out2, penv3, env3) = exec (SeqStmt ss) penv2 env2
    in (out1 ++ out2, penv3, env3)

--- ### If Statements

exec (IfStmt e1 s1 s2) penv env
    | BoolVal True <- eval e1 env = exec s1 penv env
    | BoolVal False <- eval e1 env = exec s2 penv env
    | otherwise = (show $ ExnVal "Condition is not a Bool", penv, env)

--- ### Procedure and Call Statements

exec p@(ProcedureStmt name args body) penv env = 
    let newPenv = H.insert name p penv
    in ("", newPenv, env)

exec (CallStmt name args) penv env
    | Just (ProcedureStmt _ params body) <- H.lookup name penv =
        let argVals = (`eval` env) <$> args
            newEnv = H.union (H.fromList $ zip params argVals) env
        in exec body penv newEnv
    | otherwise = ("Procedure not found: " ++ name, penv, env)
