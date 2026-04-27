module Infer where

import Common

import Control.Monad.Writer (listen)
import Control.Monad.Except (throwError)
import Data.Map.Strict as H (Map, insert, lookup, empty, fromList, singleton)

tag1 = 64002
tag2 = 68869
tag3 = 19545

  {- question 1: fresh instance function -}

freshInst :: PolyTy -> Infer MonoTy
freshInst (Forall qVars tau) = do
  freshTaus <- mapM (const freshTau) qVars
  let subst = H.fromList $ zip qVars freshTaus
  return $ apply subst tau

  {- question 2: occurs check -}

occurs :: VarId -> MonoTy -> Bool
occurs i tau = i `elem` freeVars tau

  {- question 3: unification -}

unify :: [Constraint] -> Infer Substitution
unify [] = return substEmpty
unify ((tau1 :~: tau2) : constraints)
  | tau1 == tau2 = unify constraints

  -- Orient: keep a type variable on the left.
  | not (isTyVar tau1) && isTyVar tau2 = unify ((tau2 :~: tau1) : constraints)

  -- Decompose matching type constructors.
  | TyConst c1 args1 <- tau1
  , TyConst c2 args2 <- tau2
  = if c1 == c2 && length args1 == length args2
      then unify (zipWith (:~:) args1 args2 ++ constraints)
      else throwError $ Can'tMatch tau1 tau2

  -- Eliminate a variable by substitution.
  | TyVar i <- tau1
  = if occurs i tau2
      then throwError $ InfiniteType i tau2
      else do
        let sub = substInit i tau2
        theta <- unify (map (apply sub) constraints)
        return $ substCompose theta (substInit i tau2)

  | otherwise = throwError $ Can'tMatch tau1 tau2
  where
    isTyVar TyVar{} = True
    isTyVar _       = False

  {- question 4: type inference -}

infer :: TypeEnv -> Exp -> Infer MonoTy
infer _ (ConstExp c) = freshInst $ constTySig c

infer env (VarExp x) =
  case H.lookup x env of
    Nothing   -> throwError $ LookupError x
    Just sigma -> freshInst sigma

infer env (MonOpExp op e') = do
  tau1 <- infer env e'
  tau <- freshTau
  opTau <- freshInst $ monopTySig op
  constrain (funTy tau1 tau) opTau
  return tau

infer env (BinOpExp op e1 e2) = do
  tau1 <- infer env e1
  tau2 <- infer env e2
  tau <- freshTau
  opTau <- freshInst $ binopTySig op
  constrain (binopFunTy tau1 tau2 tau) opTau
  return tau

infer env (IfExp e1 e2 e3) = do
  tau1 <- infer env e1
  tau2 <- infer env e2
  tau3 <- infer env e3
  constrain tau1 boolTy
  constrain tau2 tau3
  return tau2

infer env (AppExp e1 e2) = do
  tau1 <- infer env e1
  tau2 <- infer env e2
  tau <- freshTau
  constrain tau1 (funTy tau2 tau)
  return tau

infer env (FunExp x e') = do
  tauArg <- freshTau
  tauBody <- infer (H.insert x (polyTyOfMonoTy tauArg) env) e'
  return $ funTy tauArg tauBody

infer env (LetExp x e1 e2) = do
  (tau1, c1) <- listen $ infer env e1
  sub1 <- unify c1
  let sigma = gen env (apply sub1 tau1)
  infer (H.insert x sigma env) e2

infer env (LetRecExp f x e1 e2) = do
  tauArg <- freshTau
  tauRes <- freshTau
  let tauFun = funTy tauArg tauRes
      env' = H.insert x (polyTyOfMonoTy tauArg)
           $ H.insert f (polyTyOfMonoTy tauFun) env

  (tauBody, c1) <- listen $ infer env' e1
  sub1 <- unify ((tauRes :~: tauBody) : c1)

  let sigma = gen env (apply sub1 tauFun)
  infer (H.insert f sigma env) e2

inferInit :: TypeEnv -> Exp -> Infer PolyTy
inferInit env e = do
  (tau, constraints) <- listen $ infer env e
  substitution <- unify constraints
  return $ quantifyMonoTy $ apply substitution tau

inferDec :: TypeEnv -> Dec -> Infer (TypeEnv, PolyTy)
inferDec env (AnonDec e') = do
  tau <- inferInit env e'
  return (env, tau)
inferDec env (LetDec x e') = do
  tau <- inferInit env (LetExp x e' (VarExp x))
  return (H.insert x tau env, tau)
inferDec env (LetRec f x e') = do
  tau <- inferInit env (LetRecExp f x e' (VarExp f))
  return (H.insert f tau env, tau)
