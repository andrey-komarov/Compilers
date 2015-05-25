{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE DeriveFoldable #-}
module FCC.Expr (
  Expr(..),
  declVar,
  ) where

import FCC.Type

import Data.Foldable
import Data.Traversable
import Control.Applicative
import Control.Monad

import Data.Int
import Prelude.Extras
import Bound

data Expr a
  = Var a
  | Lit Int32
  | LitBool Bool
  | Lam Type (Scope () Expr a)
  | Empty
  | Pop (Expr a)
  | Seq (Expr a) (Expr a)
  | Call (Expr a) [Expr a]
  | Eq (Expr a) (Expr a) -- костыль во имя нереализации ad-hoc полиморфизма
  | While (Expr a) (Expr a)
  | If (Expr a) (Expr a) (Expr a)
  | Assign (Expr a) (Expr a)
  | Array (Expr a) (Expr a)
  | New Type (Expr a)
  | Return (Expr a)
  deriving (Eq, Ord, Show, Read, Foldable, Traversable)

instance Functor Expr where
  fmap = liftM
  
instance Applicative Expr where
  pure = return
  (<*>) = ap

instance Monad Expr where
  return = Var
  Var a >>= f = f a
  Lit i >>= _ = Lit i
  LitBool b >>= _ = LitBool b
  Lam t scope >>= f = Lam t $ scope >>>= f
  Empty >>= f = Empty
  Pop e >>= f = Pop $ e >>= f
  Seq e1 e2 >>= f = Seq (e1 >>= f) (e2 >>= f)
  Call fun args >>= f = Call (fun >>= f) $ fmap (>>= f) args
  Eq e1 e2 >>= f = Eq (e1 >>= f) (e2 >>= f)
  While cond e >>= f = While (cond >>= f) (e >>= f)
  If cond thn els >>= f = If (cond >>= f) (thn >>= f) (els >>= f)
  Assign dest src >>= f = Assign (dest >>= f) (src >>= f)
  Array arr ind >>= f = Array (arr >>= f) (ind >>= f)
  New t e >>= f = New t $ e >>= f
  Return e >>= f = Return $ e >>= f

declVar :: Eq a => Type -> a -> Expr a -> Expr a
declVar t x e = Lam t $ abstract1 x e

instance Eq1 Expr where
  (==#) = (==)
instance Ord1 Expr where
  compare1 = compare
instance Show1 Expr where
  showsPrec1 = showsPrec
instance Read1 Expr where
  readsPrec1 = readsPrec
