{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE FlexibleInstances #-}
module FCC.Typecheck (

  ) where

import FCC.Type
import FCC.TypecheckError
import FCC.Expr

import Bound

import Control.Monad.State
import Control.Monad.Reader
import Control.Monad.Except

import qualified Data.Map as M

data Context = Context {
  expectedRetType :: Type
  }

fresh :: Typecheck String
fresh = do
  cnt <- get
  modify (+1)
  return $ "var_" ++ show cnt

newtype Typecheck a = Typecheck {
  runTypecheck :: StateT Int (ReaderT Context (Except TypecheckError)) a
  } deriving (Functor, Applicative, Monad,
              MonadError TypecheckError, MonadReader Context, MonadState Int)

class Typecheckable (f :: * -> *) t | f -> t where
  typecheck :: f t -> Typecheck (f t, Type)

instance Typecheckable Expr (String, Type) where
  typecheck v@(Var (_, t)) = do
    return (v, t)
  typecheck (Lit i) = return (Lit i, TInt)
  typecheck (LitBool b) = return (LitBool b, TBool)
  typecheck (Lam t s) = do
    var <- fresh
    (e, te) <- typecheck $ instantiate1 (Var (var, t)) s
    return (Lam t (abstract1 (var, t) e), te)
  typecheck Empty = return (Empty, TVoid)
  typecheck (Seq e1 e2) = do
    (e1', _) <- typecheck e1
    (e2', _) <- typecheck e2
    return $ (Seq e1' e2', TVoid)
  typecheck (Call f@(Var _) args) = do
    (f', tf) <- typecheck f
    args' <- mapM typecheck args
    let targs = fmap snd args'
    (tfargs, tfret) <- case tf of
      TFun ta t -> return (ta, t)
      t -> throwError $ NotAFunction t f
    when (targs /= tfargs) $ throwError $ ArgumentsTypesDiffer targs tfargs f
    return (f', tfret)
  typecheck (Call f args) = throwError $ NotCallable f
  typecheck (Eq e1 e2) = do
    (e1', te1) <- typecheck e1
    (e2', te2) <- typecheck e2
    when (te1 /= te2) $ throwError $ EqTypesDiffer te1 te2 e1 e2
    let select fname t = return (Call (Var (fname, TFun [t, t] TBool)) [e1', e2'], TBool)
    case te1 of
     TInt -> select "_builtin_eq_int" TInt
     TBool -> select "_builtin_eq_bool" TBool
     TArray a -> select "_builtin_eq_ptr" (TArray a)
     t -> throwError $ UnsupportedTypeForEq te1 e1 e2
  typecheck (While cond body) = do
    (cond', tcond) <- typecheck cond
    (body', tbody) <- typecheck body
    when (tcond /= TBool) $ throwError $ WhileConditionIsNotBool tcond cond
    return (While cond' body', TVoid)
  typecheck (If cond thn els) = do
    (cond', tcond) <- typecheck cond
    (thn', tthn) <- typecheck thn
    (els', tels) <- typecheck els
    when (tcond /= TBool) $ throwError $ IfConditionIsNotBool tcond cond
    return (If cond' thn' els', TVoid)
  typecheck (Assign v@(Var _) val) = do
    (v', tv) <- typecheck v
    (val', tval) <- typecheck val
    when (tv /= tval) $ throwError $ AssignTypeMismatch tv tval v val
    return (Assign v' val', TVoid)
  typecheck (Assign ai@(Array _ _) val) = do
    (ai', tai) <- typecheck ai
    (val', tval) <- typecheck val
    when (tai /= tval) $ throwError $ AssignTypeMismatch tai tval ai val
    return (Assign ai' val', TVoid)
  typecheck (Assign dst val) = throwError $ NotAssignable dst
  typecheck (Array a i) = do
    (a', ta) <- typecheck a
    (i', ti) <- typecheck i
    ta' <- case ta of
      TArray x -> return x
      t -> throwError $ NotAnArray ta a
    when (ti /= TInt) $ throwError $ IndexIsNotInt ti i
    return $ (Array a' i', ta')
  typecheck (Return e) = do
    (e', te) <- typecheck e
    tret <- asks expectedRetType
    when (te /= tret) $ throwError $ WrongReturnType te tret e
    return (Return e', TVoid)
