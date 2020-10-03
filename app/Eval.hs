-- All Helper functions are not intended to be used as standalone functions

module Eval where

import GHC.Int
import Init
import Types
import Texpr1
import Abstract1
import AbstractMonad
import Apron.Var
import Language.C.Data.Ident
import Language.C.Data.Node
import Language.C.Syntax.AST
import Language.C.Syntax.Constants
import Control.Monad.State.Strict (liftIO)

-----

{- Program Level -}
-- Get the initial state of Abstract_Top
getInitSt :: Abstract Abstract1 -> Abstract Abstract1
getInitSt st = do
  abs <- st
  abs1 <- abstractTop
  return abs1

evalProg :: CTranslationUnit AbsState -> IO (CTranslationUnit AbsState)
evalProg (CTranslUnit extDecls (State a loc)) = do
  let abs1 = getInitSt a
  let nExtDecls = evalEDLst abs1 extDecls
  return (CTranslUnit nExtDecls (State abs1 loc))

evalEDLst :: Abstract Abstract1 -> [CExternalDeclaration AbsState] -> [CExternalDeclaration AbsState]
evalEDLst preC [] = []
evalEDLst preC (ed:eds) = [newEd] ++ (evalEDLst newSt eds)
  where newEd = evalExtDecl preC ed
        newSt = getStFromED newEd

-- Just a helper function to help extract the state from ED
getStFromED :: CExternalDeclaration AbsState -> Abstract Abstract1
getStFromED (CDeclExt (CDecl _ _ (State a _))) = a
getStFromED (CFDefExt (CFunDef _ _ _ _ (State a _))) = a
getStFromED _ = error "Declaration not implemented"

evalExtDecl :: Abstract Abstract1 -> CExternalDeclaration AbsState -> CExternalDeclaration AbsState
evalExtDecl st (CDeclExt a) = CDeclExt (evalDecl st a)
evalExtDecl st (CFDefExt a) = CFDefExt (evalFunc st a)
evalExtDecl st _            = error "Not Implemented"

-----

{- Function Level -}
evalFunc :: Abstract Abstract1 -> CFunctionDef AbsState -> CFunctionDef AbsState
evalFunc preC (CFunDef a b c d (State _ loc)) = initF
  where initF = CFunDef a b c d (State preC loc)

-----

{- Declaration Level -}
-- Right now that we don't care about types, the only concern is 
-- with the initializers and expressions
evalDecl :: Abstract Abstract1 -> CDeclaration AbsState -> CDeclaration AbsState
evalDecl preC (CDecl a b (State _ loc)) = 
    CDecl a b (State (foldl evalDeclHelper preC b) loc)

absAssgHelper :: Abstract Abstract1 -> (VarName, Texpr1) -> Abstract Abstract1
absAssgHelper a (v, t) = do
  a1 <- a
  a2 <- abstractTop
  abstractAssignTexprArray a1 v t 1 a2

-- Process every variable declaration separately
evalDeclHelper :: Abstract Abstract1 -> (Maybe (CDeclarator AbsState), Maybe (CInitializer AbsState), Maybe (CExpression AbsState)) -> Abstract Abstract1
-- If it is only a declaration, no need to change the abstraction
evalDeclHelper a (_, Nothing, Nothing) = a

evalDeclHelper a (Just (CDeclr (Just (Ident var _ _)) _ _ _ _), (Just (CInitExpr expr _)), Nothing) = do
  abs1 <- a
  (texpr, pair) <- evalExpr abs1 expr
  let npair = pair ++ [(var, texpr)]
  foldl absAssgHelper a npair
  
evalDeclHelper _ _ = error "Not implemented"


{- Statements -}
-- A helper function to evaluate compounds
{-
evalCmpd :: Abstract1 -> CCompoundBlockItem AbsState -> CCommpoundBlockItem AbsState
evalCmpd abs1 (CBlockStmt cstmt)   = CBlockStmt (evalStmt abs1 cstmt)
evalCmpd abs1 (CBlockDecl cdecl)   = CBlockDecl (evalDecl abs1 cdecl)
evalCmpd abs1 (CNestedFunDef cnfd) = error "Nested Function not implemented"

evalStmt :: Abstract1 -> CStatement AbsState -> CStatement AbsState
evalStmt abs1 (CExpr Nothing st) = CExpr Nothing (setAbs1 abs1 st)
-- Disregard the actual texpr, only modify all the side effects
evalStmt abs1@(_ env) (CExpr (Just (cexpr) st) =
  CExpr (Just (cexpr) (setAbs1 nabs1 st))
  where _ vl  = evalExpr env cexpr
        nabs1 = foldl (\abs (v, t) -> abs1Assg abs v t) abs1 vl

evalStmt abs1 (CCompound ids [] st) =
  CCompound ids [] (setAbs1 abs1 st)
evalStmt abs1 (CCompound ids (cmpds:cmpd) st) =
  CCompound ids (ncmpds ++ (ncmpd nnst) (setAbs1 nnabs1 st))
  where CCompound _ ncmpds (State nabs1 _) = evalStmt abs1 (CCompound ids cmpds st)
        ncmpd nnst@(State nnabs1 _) = evalCmpd nabs1 cmpd
-}


{- Expressions -}
-- A special return type for evaluating an expression
-- An expression can generate a syntax tree, but might also involve assignments
type ExprSt = (Texpr1, [(VarName, Texpr1)])

evalVar :: Abstract Abstract1 -> VarName -> Abstract Var
evalVar a v = do
  abs <- a
  var <- getVar v
  return var

evalExpr :: Abstract1 -> CExpression AbsState -> Abstract ExprSt
evalExpr a (CAssign CAssignOp (CVar (Ident v _ _) _) rhs _) = do
  -- Technically ++a would be different but ignore it for now
  (rtexpr, rpair) <- evalExpr a rhs
  return (rtexpr, rpair ++ [(v, rtexpr)])

evalExpr a (CAssign aop (CVar (Ident v _ _) _) rhs _) = do
  (rtexpr, rpair) <- evalExpr a rhs
  ltexpr <- texprMakeLeafVar v
  ntexpr <- texprMakeBinOp (evalAOp aop) ltexpr rtexpr ROUND_INT ROUND_NEAREST
  return (ntexpr, rpair ++ [(v, ntexpr)])

evalExpr a (CVar (Ident v _ _) _) = do
  ntexpr <- texprMakeLeafVar v
  return (ntexpr, [])

evalExpr a (CConst (CIntConst n _)) = do
  ntexpr <- texprMakeConstant $ ScalarVal $ IntValue $ (fromInteger (getCInteger n) :: GHC.Int.Int32)
  return (ntexpr, [])

evalExpr _ _ = error "expression not implemented"


{- Operations -}
evalAOp :: CAssignOp -> OpType
evalAOp aop =
  case aop of
    CMulAssOp -> MUL_OP
    CDivAssOp -> DIV_OP
    CRmdAssOp -> MOD_OP
    CAddAssOp -> ADD_OP
    CSubAssOp -> SUB_OP
    CShlAssOp -> error "Unsupported AOp <<="
    CShrAssOp -> error "Unsupported AOp >>="
    CAndAssOp -> error "Unsupported AOp &="
    CXorAssOp -> error "Unsupported AOp ^="
    COrAssOp  -> error "Unsupported AOp |="
