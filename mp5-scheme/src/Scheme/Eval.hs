{-# LANGUAGE FlexibleContexts, LambdaCase #-}

module Scheme.Eval where

import Scheme.Core

import Prelude hiding (lookup)
import qualified Data.HashMap.Strict as H (HashMap, insert, lookup, empty, fromList, union)
import Control.Monad.State
import Control.Monad.Except

-- ### Evaluation helpers

tag1 = 39236
tag2 = 97713

-- Evaluates a symbol to string
-- Throws an error if value is not a symbol
-- Examples:
--   getSym (Symbol "x")  ==> "x"
--   getSym (Number 1)    ==> Not a symbol: x
getSym :: Val -> EvalState String
getSym (Symbol x) = return x
getSym         v  = throwError $ NotASymbol v

-- `let` and `let*`
getBinding :: Val -> EvalState (String, Val)
getBinding (Pair c (Pair e Nil)) = liftA2 (,) (getSym c) (eval e)
getBinding v = throwError $ NotAListOfTwo v

-- Evaluates a list of two to a tuple
-- Throws an error if value is not a list of two
-- This is useful in special form `cond`, since each clause
-- is expected to be exactly a two-element list
getListOf2 :: Val -> EvalState (Val, Val)
getListOf2 (Pair c (Pair e Nil)) = return (c, e)
getListOf2 v = throwError $ NotAListOfTwo v

-- Evaluates a value representing a list into an actual list
getList :: Val -> EvalState [Val]
getList Nil = return []
getList (Pair v1 v2) =
  do xs <- getList v2
     return (v1 : xs)
getList e = throwError $ InvalidSpecialForm "special" e

--- ### Keywords

-- When evaluating special forms, a list form starting with a keyword
-- is expected to match the special form syntax.
keywords :: [String]
keywords = [ "define"
           , "lambda"
           , "cond"
           , "let"
           , "let*"
           , "define-macro"
           , "quasiquote"
           , "unquote"
           ]

-- ### The monadic evaluator
-- Unlike evaluators in previous MPs, `eval` does not take any environment!
-- This is because the environment is encapsulated in the `EvalState` monad.
-- To access the environment, all you have to do is `get`, `modify` or `put`!
eval :: Val -> EvalState Val

-- Self-evaluating expressions
eval v@(Number _) = return v
eval v@(Boolean _) = return v

-- Symbol evaluates to the value bound to it
eval (Symbol sym) =
  do env <- get
     case H.lookup sym env of
       Just v -> return v
       Nothing -> throwError $ UndefSymbolError sym

-- Function closure is also self-evaluating
eval v@(Func _ _ _) = return v

-- We check to see if the pair is a "proper list". If it is,
-- then we try to evaluate it, as one of the following forms:
-- 1. Special form (`define`, `let`, `let*`, `cond`, `quote`, `quasiquote`,
--    `unquote`, `define-macro`, ...)
-- 2. Macro expansion (Macro)
-- 3. Function application (Func)
-- 4. Primitive function application (PrimFunc)
eval expr@(Pair v1 v2) = case flattenList expr of
  Left _ -> throwError $ InvalidExpression expr
  Right lst -> evalList lst where
    --- Evaluator for forms
    invalidSpecialForm :: String -> EvalState e
    invalidSpecialForm frm = throwError $ InvalidSpecialForm frm expr

    evalList :: [Val] -> EvalState Val

    evalList [] = throwError $ InvalidExpression expr

    -- quote
    evalList [Symbol "quote", e] = return e

    -- unquote (illegal at surface evaluation)
    evalList [Symbol "unquote", e] = throwError $ UnquoteNotInQuasiquote e

    -- quasiquote
    evalList [Symbol "quasiquote", e] = evalQuasi 1 e where
      evalQuasi :: Int -> Val -> EvalState Val
      evalQuasi 0 (Pair (Symbol "unquote") v) = throwError $ UnquoteNotInQuasiquote v
      evalQuasi 1 (Pair (Symbol "unquote") (Pair v Nil)) = eval v
      evalQuasi n (Pair (Symbol "quasiquote") (Pair v Nil)) =
        do v' <- evalQuasi (n+1) v
           return $ Pair (Symbol "quasiquote") (Pair v' Nil)
      evalQuasi n (Pair (Symbol "unquote") (Pair v Nil)) =
        do v' <- evalQuasi (n-1) v
           return $ Pair (Symbol "unquote") (Pair v' Nil)
      evalQuasi n (Pair x y) = Pair <$> evalQuasi n x <*> evalQuasi n y
      evalQuasi _ v = return v

    -- cond
    evalList (Symbol "cond" : clauses) =
      case clauses of
        [] -> invalidSpecialForm "cond"
        _ -> evalCond clauses where
          evalCond [] = return Void
          evalCond (cl:rest) =
            do (c, e) <- getListOf2 cl
               case (c, rest) of
                 (Symbol "else", _ : _) -> invalidSpecialForm "cond"
                 (Symbol "else", []) -> eval e
                 _ -> do cv <- eval c
                         case cv of
                           Boolean False -> evalCond rest
                           _ -> eval e

    -- let
    evalList [Symbol "let", bindForm, body] =
      do env0 <- get
         result <-
           (do bindVals <- evalSimulBinds env0 bindForm
               put $ H.union (H.fromList bindVals) env0
               eval body)
           `catchError` (\err -> put env0 >> throwError err)
         put env0
         return result where
           evalSimulBinds env0 bindForm =
             do bindList <- getList bindForm
                mapM (evalOne env0) bindList
           evalOne env0 bind =
             do put env0
                getBinding bind

    evalList [Symbol "let*", bindForm, body] =
      do env0 <- get
         result <-
           (do bindList <- getList bindForm
               env' <- evalSeqBinds env0 bindList
               put env'
               eval body)
           `catchError` (\err -> put env0 >> throwError err)
         put env0
         return result where
           evalSeqBinds env [] = return env
           evalSeqBinds env (b:bs) =
             do put env
                (name, val) <- getBinding b
                evalSeqBinds (H.insert name val env) bs

    -- lambda
    evalList [Symbol "lambda", args, body] =
      do env <- get
         argList <- getList args
         val <- (\ns -> Func ns body env) <$> mapM getSym argList
         return val

    -- define function
    evalList [Symbol "define", Pair (Symbol fname) args, body] =
      do env <- get
         argList <- getList args
         val <- (\argVal -> Func argVal body env) <$> mapM getSym argList
         modify $ H.insert fname val
         return Void

    -- define variable
    evalList [Symbol "define", Symbol var, e] =
      do v <- eval e
         modify $ H.insert var v
         return Void

    -- define-macro
    evalList [Symbol "define-macro", Pair (Symbol mname) args, body] =
      do argList <- getList args
         params <- mapM getSym argList
         modify $ H.insert mname (Macro params body)
         return Void

    -- invalid use of keyword, throw a diagnostic
    evalList (Symbol sym : _) | elem sym keywords = invalidSpecialForm sym

    -- application
    evalList (fexpr:args) =
      do f <- eval fexpr
         apply f args

eval val = throwError $ InvalidExpression val

-- Function application
apply :: Val -> [Val] -> EvalState Val
  -- Function
apply f@(Func params body fenv) args =
  if length params /= length args
    then throwError $ CannotApply f args
    else do
      argVals <- mapM eval args
      env0 <- get
      result <-
        (do put $ H.union (H.fromList (zip params argVals)) (H.union fenv env0)
            eval body)
        `catchError` (\err -> put env0 >> throwError err)
      put env0
      return result

  -- Macro
apply m@(Macro params body) args =
  if length params /= length args
    then throwError $ CannotApply m args
    else do
      env0 <- get
      expanded <-
        (do put $ H.union (H.fromList (zip params args)) env0
            eval body)
        `catchError` (\err -> put env0 >> throwError err)
      put env0
      eval expanded

  -- Primitive
apply (PrimFunc p) args =
  do argVals <- mapM eval args
     p argVals
  -- Other values are not applicable
apply f args = throwError $ CannotApply f args
