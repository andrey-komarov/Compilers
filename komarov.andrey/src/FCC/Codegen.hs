{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE FlexibleContexts #-}
module FCC.Codegen (
  codegen,
  ) where

import FCC.Expr
import FCC.Program

import Bound

import Data.Monoid
import Control.Applicative
import Control.Monad.State

import qualified Data.Map as M

impossible = error "Internal compiler error. Please submit a bug-report."

data Binding = Local Int | Global String | Arg Int
                           deriving (Eq, Ord, Show, Read)

data CodegenState = CodegenState {
  offset :: Int,
  counter :: Int,
  maxOffset :: Int,
  argumentsCount :: Int }

emptyState = CodegenState 0 0 0 0

modifyOffset :: MonadState CodegenState m => (Int -> Int) -> m ()
modifyOffset f = modify $ \s@(CodegenState{maxOffset = m, offset = o})
                          -> s{maxOffset = m `max` o, offset = f o}

resetMaxOffset :: MonadState CodegenState m => m ()
resetMaxOffset = modify $ \s -> s{maxOffset = 1}

setArgumentsCount :: MonadState CodegenState m => Int -> m ()
setArgumentsCount args = modify $ \s -> s{argumentsCount = args}

newtype Codegen a = Codegen {
  runCodegen :: State CodegenState a
  } deriving (Functor, Applicative, Monad, MonadState CodegenState)

fresh :: String -> Codegen String
fresh pref = do
  x <- gets counter
  modify (\s -> s{counter = x + 1})
  return $ pref ++ show x

freshLabel :: Codegen String
freshLabel = fresh "_label_"

freshVar :: Codegen String
freshVar = fresh "_var_"

codegen :: Program String -> [String] 
codegen p = evalState (runCodegen $ compileP p) emptyState

compileP :: Program String -> Codegen [String]
compileP (Program funs vars) = do
  dataSegNames <- sequence [freshVar | _ <- M.keys vars]
  let dataHead = ["@@@@@@@@@", ".data", ".global _start"]
      dataBody = [name ++ ": .word 0" | name <- dataSegNames]
      textVeryHead = ["", "@@@@@@@@@", ".text"]
      textHead = [realName ++ ": .word " ++ dataName | (realName, dataName) <- zip (M.keys vars) dataSegNames]
  functions <- mapM f $ M.toList funs
  return $ dataHead ++ dataBody ++ textVeryHead ++ textHead ++ concat functions
    where
    f :: (String, Function String) -> Codegen [String]
    f (name, fun) = do
      code <- compileF fun
      return $ ["", "@@@@@@@", name ++ ":"] ++ code

compileF :: Function String -> Codegen [String]
compileF (Function _ _ (Native _ code)) = return $ code ++ ["mov pc, lr"]
compileF (Function _ _ (Inner s)) = do
  let e = instantiate (return . Arg) (Global <$> s)
  resetMaxOffset
  modifyOffset (const 1)
  code <- compileE e
  off <- gets maxOffset
  return $ ["push {fp, lr}", "mov fp, sp", "sub sp, #" ++ show (off * 4)] ++ code

compileE :: Expr Binding -> Codegen [String]
compileE (Var (Local off)) = return ["ldr r0, [fp, #-" ++ show (off * 4) ++"]", "push {r0}"]
compileE (Var (Global name)) = return ["ldr r0, " ++ name, "ldr r0, [r0]", "push {r0}"]
compileE (Var (Arg arg)) = return ["ldr r0, [fp, #" ++ show (arg * 4 + 8) ++ "]", "push {r0}"]
compileE (Lit i) = return ["ldr r0, =" ++ show i, "push {r0}"]
compileE (LitBool True) = return ["mov r0, #1", "push {r0}\t\t@ true"]
compileE (LitBool False) = return ["mov r0, #0", "push {r0}\t\t@ false"]
compileE (Lam t s) = do
  v <- freshVar
  off <- gets offset
  modifyOffset (+1)
  code <- compileE $ instantiate1 (Var (Local off)) s
  modifyOffset (`subtract` 1)
  return code
compileE Empty = return []
compileE (Pop e) = do
  code <- compileE e
  return $ code ++ ["pop {r0}"]
compileE (Seq e1 e2) = (++) <$> compileE e1 <*> compileE e2
compileE (Call (Var (Global fname)) args) = do
  compiledArgs <- concat <$> reverse <$> mapM compileE args
  return $ compiledArgs ++ ["bl " ++ fname]
compileE (Call _ _) = impossible
compileE (Eq _ _) = impossible
compileE (While cond body) = do
  begin <- freshLabel
  end <- freshLabel
  cond' <- compileE cond
  body' <- compileE body
  return $ [begin ++ ": @ while"] ++ cond' ++ ["pop {r0}", "tst r0, r0", "beq " ++ end] ++ body' ++ ["b " ++ begin, end ++ ": @ endwhile"]
compileE (If cond thn els) = do
  elseLabel <- freshLabel
  endIfLabel <- freshLabel
  cond' <- compileE cond
  thn' <- compileE thn
  els' <- compileE els
  return $ cond' ++ ["pop {r0}", "tst r0, r0", "beq " ++ elseLabel]
    ++ thn' ++ ["b " ++ endIfLabel, elseLabel ++ ": @ else:"]
    ++ els' ++ [endIfLabel ++ ": @ endif"]
compileE (Assign (Var (Local off)) src) = do
  code <- compileE src
  return $ code ++ ["pop {r0}", "str r0, [fp, #-" ++ show (off * 4) ++ "]", "push {r0}"]
compileE (Assign (Var (Global name)) src) = do
  code <- compileE src
  return $ code ++ ["pop {r0}", "ldr r1, " ++ name, "str r0, [r1]", "push {r0}"]
compileE (Assign (Var (Arg arg)) src) = do
  code <- compileE src
  return $ code ++ ["pop {r0}", "str r0, [fp, #" ++ show (arg * 4 + 8) ++ "]", "push {r0}"]
compileE (Assign (Array a i) src) = do
  codea <- compileE a
  codei <- compileE i
  code <- compileE src
  return $ codea ++ codei ++ code ++ ["pop {r0}\t\t@ b", "pop {r1}\t\t@ i", "pop {r2}\t\t@ a", "str r0, [r2, r1, LSL #2]", "push {r0}"]
compileE (Assign _ _) = impossible
compileE (Array a i) = do
  codea <- compileE a
  codei <- compileE i
  return $ codea ++ codei ++ ["pop {r1}", "pop {r0}", "ldr r0, [r0, r1, LSL #2]", "push {r0}"]
compileE (Return e) = do
  code <- compileE e
  nargs <- gets argumentsCount
  return $ code ++ ["pop {r0}", "mov sp, fp", "pop {fp, lr}", "add sp, #" ++ show (nargs * 4), "push {r0}", "mov pc, lr"]
