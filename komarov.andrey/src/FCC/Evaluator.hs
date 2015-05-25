{-# LANGUAGE GeneralizedNewtypeDeriving #-}
module FCC.Evaluator (
  calc, calcF,
  EvalConfig(..),
  config,
  ) where

import FCC.Type
import FCC.Expr
import FCC.Eval
import FCC.Program
import FCC.Optimize.StdlibEval

import Bound

import Data.Foldable as F
import Control.Applicative
import Control.Monad.Except
import Control.Monad.State
import Control.Monad.Reader
import Control.Monad.Cont

import qualified Data.Set as S
import qualified Data.Map as M

data Context = Context {
  bindings :: M.Map String Value,
  counter :: Int,
  bound :: Int
  } deriving (Eq, Ord, Show, Read)


defaultTimeout = 10000

data EvalConfig = EvalConfig {
  ctxFunctions :: M.Map String (Function String),
  initialTimeout :: Int
  } deriving (Eq, Ord, Show)

newtype Evaluator r a = Evaluator {
  runEvaluator :: ExceptT () (StateT Context (ReaderT EvalConfig (Cont r))) a
  } deriving (Functor, Applicative, Monad,
              MonadError (), MonadReader EvalConfig,
              MonadState Context, MonadCont)

impossible = error "FATAL ERROR ¯\\_(ツ)_/¯"

runE :: Context -> EvalConfig -> Evaluator (Either () a) a -> Either () a
runE s r e = runCont (runReaderT (runStateT (runExceptT $ runEvaluator e) s) r) fst

calc :: EvalConfig -> Expr String -> Maybe Value
calc cfg e = case runE (Context M.empty (initialTimeout cfg) 0) cfg (callCC $ \k -> eval k e) of
  Left _ -> Nothing
  Right a -> Just a

calcF :: EvalConfig -> Function String -> [Value] -> Maybe Value
calcF cfg f args = case runE (Context M.empty (initialTimeout cfg) 0) cfg (call f args) of
  Left _ -> Nothing
  Right a -> Just a

tick :: Evaluator r ()
tick = do
  remain <- gets counter
  when (remain <= 0) $ throwError ()
  modify $ \c -> c{ counter = remain - 1 }

fresh :: Evaluator r String
fresh = do
  var <- gets bound
  modify $ \c -> c{bound = var + 1}
  return $ "_opt_var_" ++ show var

defaultVal :: Type -> Value
defaultVal TInt = VInt 0
defaultVal TBool = VBool False
defaultVal TVoid = VVoid
defaultVal (TArray _) = VArray M.empty
defaultVal (TFun _ _) = impossible

call :: Function String -> [Value] -> Evaluator r Value
call (Function _ _ (Native name _)) args = do
  tick
  case do {ev <- M.lookup name builtinsE; ev args } of
   Nothing -> throwError ()
   Just res -> return res
call (Function fargs _ (Inner s)) args = do
  tick
  names <- sequence [fresh | _ <- fargs]
  modify (\c -> c{bindings = bindings c `M.union` M.fromList (zip names args)})
  callCC $ \k -> eval k $ instantiate (Var . (names !!)) s

eval :: (Value -> Evaluator r Value) -> Expr String -> Evaluator r Value
eval k (Var v) = do
  b <- gets bindings
  case M.lookup v b of
   Nothing -> throwError ()
   Just val -> return val
eval k (Lit i) = return $ VInt i
eval k (LitBool b) = return $ VBool b
eval k (Lam t s) = do
  v <- fresh
  modify $ \c -> c{bindings = M.insert v (defaultVal t) (bindings c)}
  eval k $ instantiate1 (Var v) s
eval k Empty = return $ VVoid
eval k (Pop e) = tick >> eval k e
eval k (Seq e1 e2) = tick >> eval k e1 >> eval k e2
eval k (Call (Var fname) args) = do
  f <- asks $ (M.lookup fname) . ctxFunctions
  case f of
   Nothing -> throwError ()
   Just f' -> do
     args' <- mapM (\x -> callCC $ \r -> eval r x) args
     call f' args'
eval k (Call _ _) = impossible
--eval k (Eq _ _) = impossible
eval k e@(While cond body) = do
  g <- get
  c <- eval k cond
  case c of
   VBool b -> if b then eval k body >> eval k e else return VVoid
   _ -> impossible
eval k (If cond thn els) = do
  c <- eval k cond
  case c of
   VBool b -> if b then eval k thn else eval k els
   _ -> impossible
eval k (Assign (Var v) src) = do
  src' <- eval k src
  modify $ \c -> c{bindings = M.insert v src' (bindings c)}
  return src'
--eval k (Assign (Array a i) src) = _ -- TODO ?????? :((((((
--eval k (Assign _ _) = impossible
--eval k (Array a i) = _
--eval k (New _ _) = impossible
eval k (Return e) = do
  e' <- eval k e
  k e'
eval _ _ = throwError ()

config :: Program String -> EvalConfig
config p@(Program funs _) = EvalConfig puM defaultTimeout where
  puM = M.filterWithKey (\k v -> k `S.member` pu) funs
  pu = findPure p

findPure :: Program String -> S.Set String
findPure (Program funs vars) = allPure where
  allPure = fix' S.empty (updPure funs)

updPure :: M.Map String (Function String) -> S.Set String -> S.Set String
updPure funs ctx = ctx `S.union` S.fromList [name | (name, f) <- M.toList funs, isPure (S.insert name ctx) f]

isPure :: S.Set String -> Function String -> Bool
isPure _ (Function _ _ (Native name _)) = name `M.member` builtinsE
isPure ctx (Function _ _ (Inner s)) = F.all (`S.member` ctx) s

fix' :: Eq a => a -> (a -> a) -> a
fix' init mod = if new == init then init else fix' new mod where
  new = mod init
