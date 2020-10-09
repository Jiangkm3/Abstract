-- A document of all helper functions that convert complex
-- operations in C to Texpr and Tcons in APRON

module Operation where
import AbstractMonad
import Texpr1
import Tcons1
import Types
import Apron.Scalar
import Language.C.Syntax.AST
import Control.Monad.State.Strict (liftIO)


{- Binary Operations -}

evalBOpExpr :: CBinaryOp -> Texpr1 -> Texpr1 -> Abstract Texpr1
evalBOpExpr bop l r
  | simpleBOp bop = do
    n <- texprMakeBinOp (evalBOp bop) l r ROUND_INT ROUND_DOWN
    return n
  | otherwise = error "Not Implemented"

evalBOpCons :: CBinaryOp -> Texpr1 -> Texpr1 -> Abstract Tcons1
evalBOpCons CGrOp t1 t2 = do
  l <- texprMakeBinOp SUB_OP t1 t2 ROUND_INT ROUND_DOWN
  r <- liftIO $ constrScalar 0
  n <- tconsMake SUP_OP l r
  return n
evalBOpCons bop l r = error "Not Implemented"

constrScalar :: Int -> IO Scalar
constrScalar n = do
  s <- apScalarAlloc
  apScalarSetInt s 0
  return s

{- Simple BOp Case -}
-- True if bop has an APRON correspondence
simpleBOp :: CBinaryOp -> Bool
simpleBOp bop =
  case bop of
    CMulOp -> True
    CDivOp -> True
    CRmdOp -> True
    CAddOp -> True
    CSubOp -> True
    _      -> False

--  Convert simple BOp to their APRON correspondence
evalBOp :: CBinaryOp -> OpType
evalBOp bop =
  case bop of
    CMulOp -> MUL_OP
    CDivOp -> DIV_OP
    CRmdOp -> MOD_OP
    CAddOp -> ADD_OP
    CSubOp -> SUB_OP
    _      -> error ("Not a simple BOp" ++ show bop)


{- Assignment Operations -}

-- Convert AOp to BOp for evaluation
convertAOp :: CAssignOp -> CBinaryOp
convertAOp aop =
  case aop of
    CMulAssOp -> CMulOp
    CDivAssOp -> CDivOp
    CRmdAssOp -> CRmdOp
    CAddAssOp -> CAddOp
    CSubAssOp -> CSubOp
    CShlAssOp -> CShlOp
    CShrAssOp -> CShrOp
    CAndAssOp -> CAndOp
    CXorAssOp -> CXorOp
    COrAssOp  -> COrOp


{- Unary Operations -}

evalUOpExpr :: CUnaryOp -> Texpr1 -> Abstract Texpr1
evalUOpExpr uop r
  | isIncDec uop   = evalIncDec uop r
  | uop == CPlusOp = return r
  | uop == CMinOp  = do
    l <- texprMakeConstant $ ScalarVal $ IntValue $ -1
    n <- texprMakeBinOp MUL_OP l r ROUND_INT ROUND_DOWN
    return n
  | otherwise      = error "Not Implemented"

evalUOpCons :: CUnaryOp -> Texpr1 -> Abstract Tcons1
evalUOpCons uop t = error "Not Implemented"

{- ++ and -- Case -}
isIncDec :: CUnaryOp -> Bool
isIncDec uop =
  case uop of
    CPreIncOp  -> True
    CPreDecOp  -> True
    CPostIncOp -> True
    CPostDecOp -> True
    _          -> False

evalUOp :: CUnaryOp -> OpType
evalUOp uop =
  case uop of
    CPreIncOp  -> ADD_OP
    CPreDecOp  -> SUB_OP
    CPostIncOp -> ADD_OP
    CPostDecOp -> SUB_OP
    _          -> error "Unsupported UOp"

evalIncDec :: CUnaryOp -> Texpr1 -> Abstract Texpr1
evalIncDec uop l = do
  r <- texprMakeConstant $ ScalarVal $ IntValue $ 1
  n <- texprMakeBinOp (evalUOp uop) l r ROUND_INT ROUND_DOWN
  return n
