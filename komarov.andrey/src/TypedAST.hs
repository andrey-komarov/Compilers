{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE FlexibleContexts #-}
module TypedAST (

  ) where

import Control.Monad.State
import Control.Monad.Error
import Control.Applicative

import qualified Data.Map as M

import qualified AST

type Id = String

data Type = TBool
          | TInt
          | TString
          | TVoid
          deriving (Show, Eq)

data FType = FType Type [Type]

data Env = Env {
  functions :: M.Map Id FType,
  variables :: M.Map Id Type
  }

data TypecheckError = UnknownVar Id
                    | UnknownFun Id
                    | UnknownType AST.Id
                    | AlreadyBound Id
                    | TypeMismatch Type Type
                    | SomethingWentWrong String
                    deriving (Show)

instance Error TypecheckError where
  strMsg = SomethingWentWrong 

newtype Typechecker a = Typechecker { unCompiler :: ErrorT TypecheckError (State Env) a } deriving (Functor, Applicative, Monad, MonadState Env, MonadError TypecheckError)

class Typecheckable a b | a -> b where
  typecheck :: a -> Typechecker b

getVarType :: Id -> Typechecker Type
getVarType name = do
  vars <- gets variables
  case M.lookup name vars of
   Nothing -> throwError $ UnknownVar name
   Just t -> return t

getFunType :: Id -> Typechecker FType
getFunType name = do
  funs <- gets functions
  case M.lookup name funs of
   Nothing -> throwError $ UnknownFun name
   Just t -> return t

updateVar :: Id -> Type -> Typechecker ()
updateVar name t = do
  env <- get
  let vars = variables env
  case M.lookup name vars of
   Nothing -> put $ env { variables = M.insert name t vars }
   Just t' -> throwError $ AlreadyBound name

expect :: Typecheckable t Type => Type -> t -> Typechecker ()
expect x ta = do
  a <- typecheck ta
  when (a /= x) $ throwError $ TypeMismatch a x

ensureSame :: Type -> Type -> Typechecker ()
ensureSame t1 t2 = when (t1 /= t2) $ throwError $ TypeMismatch t1 t2

parseType :: AST.Id -> Typechecker Type
parseType "int" = return TInt
parseType "bool" = return TBool
parseType "string" = return TString
parseType "void" = return TVoid
parseType t = throwError $ UnknownType t

instance Typecheckable AST.Expression Type where
  typecheck (AST.EVar v) = getVarType v
  typecheck (AST.EInt _) = return TInt
  typecheck (AST.EBool _) = return TBool
  typecheck (AST.EAdd lhs rhs) =
    expect TInt lhs >> expect TInt rhs >> return TInt
  typecheck (AST.ESub lhs rhs) =
    expect TInt lhs >> expect TInt rhs >> return TInt
  typecheck (AST.EMul lhs rhs) =
    expect TInt lhs >> expect TInt rhs >> return TInt
  typecheck (AST.ELess lhs rhs) =
    expect TInt lhs >> expect TInt rhs >> return TBool
  typecheck (AST.EGreater lhs rhs) =
    expect TInt lhs >> expect TInt rhs >> return TBool
  typecheck (AST.ELessEq lhs rhs) =
    expect TInt lhs >> expect TInt rhs >> return TBool
  typecheck (AST.EGreaterEq lhs rhs) =
    expect TInt lhs >> expect TInt rhs >> return TBool
  typecheck (AST.EEqual lhs rhs) = do
    tl <- typecheck lhs
    tr <- typecheck rhs
    ensureSame tl tr
    return TBool
  typecheck (AST.ENotEqual lhs rhs) = do
    tl <- typecheck lhs
    tr <- typecheck rhs
    ensureSame tl tr
    return TBool
  typecheck (AST.EAnd lhs rhs) =
    expect TBool lhs >> expect TBool rhs >> return TBool
  typecheck (AST.EOr lhs rhs) =
    expect TBool lhs >> expect TBool rhs >> return TBool
  typecheck (AST.ECall name args) = do
    targs <- forM args typecheck
    FType ret targs' <- getFunType name
    forM (zip targs targs') $ \(t, t') ->
      ensureSame t t'
    return ret

instance Typecheckable AST.Statement () where
  typecheck (AST.SBlock stmts) = do
    s <- get
    forM_ stmts typecheck
    put s
  typecheck (AST.SVarDecl tp name) = do
    t <- parseType tp
    updateVar name t
  typecheck (AST.SAssignment name expr) = do
    tl <- getVarType name
    tr <- typecheck expr
    ensureSame tl tr
  typecheck (AST.SRawExpr e) = void $ typecheck e
  typecheck (AST.SIfThenElse cond thn els) =
    expect TBool cond >> typecheck thn >> typecheck els
  typecheck (AST.SWhile cond body) =
    expect TBool cond >> typecheck body
  typecheck (AST.SReturn e) = void $ typecheck e
