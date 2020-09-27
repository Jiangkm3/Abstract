-- All Helper functions are not intended to be used as standalone functions

module Eval where

import Init
import Abstract1
import AbstractMonad
import Language.C.Data.Ident
import Language.C.Data.Node
import Language.C.Syntax.AST
import Control.Monad.State.Strict (liftIO)

{- Helper Functions -}
{-
abs1Assg :: Abstract1 -> Var -> Texpr1 -> Abstract1
abs1Assg org var texpr =
  ap_abstract1_assign_texpr_array_wrapper man False org [var] texpr 1 Nothing

setAbs1 :: Abstract1 -> AbsState -> AbsState
setAbs1 abs1 (State _ ni) = toState abs1 ni

getAbs1 :: AbsState -> Abstract1
getAbs1 (abs1 _) = abs1
-}

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
getStFromED (CDeclExt _) = error "Declaration not implemented"
getStFromED (CFDefExt (CFunDef _ _ _ _ (State a _))) = a
getStFromED _ = error "Declaration not implemented"

evalExtDecl :: Abstract Abstract1 -> CExternalDeclaration AbsState -> CExternalDeclaration AbsState
evalExtDecl st (CDeclExt a) = error "Declaration not implemented"
evalExtDecl st (CFDefExt a) = CFDefExt (evalFunc st a)
evalExtDecl st _            = error "Not Implemented"

-----

{- Function Level -}
evalFunc :: Abstract Abstract1 -> CFunctionDef AbsState -> CFunctionDef AbsState
evalFunc preC func@(CFunDef a b c d (State _ loc)) = initF
  where initF = CFunDef a b c d (State preC loc)

-----

{- Declaration Level -}
-- Right now that we don't care about types, the only concern is 
-- with the initializers and expressions
evalDecl :: Abstract Abstract1 -> CDeclaration AbsState -> CDeclaration AbsState
evalDecl preC cdecl@(CDecl _ _ _) = cdecl

-- Process every variable declaration separately
evalDeclHelper :: Abstract Abstract1 -> (Maybe (CDeclarator a), Maybe (CInitializer a), Maybe (CExpression a)) -> Abstract Abstract1
-- If it is only a declaration, no need to change the abstraction
evalDeclHelper abs1 (_, Nothing, Nothing) = abs1
evalDeclHelper abs1 (_, _, Nothing) = abs1
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


{- Declarations -}
{-
evalDecl :: Abstract1 -> CDeclarator AbsState -> CDeclarator AbsState
evalDecl _ _ = error "declaration not implemented"
-}


{- Expressions -}
-- A special return type for evaluating an expression
-- An expression can generate a syntax tree, but might also involve assignments
{-
type ExprSt = Texpr1 [(Var, Texpr1)]

evalExpr :: Environment -> CExpression AbsState -> ExprSt
evalExpr env (CAssign CAssignOp lhs rhs _)
-- We forget about lists for now
-- Technically ++a is different but also ignore that for now
  | lhs == (CVar id _) = rtexpr nvl1
  | otherwise          = error "invalid expression to assign to"
  where rtexpr rvl1 = evalExpr env rhs
        nvl1 = rvl1 ++ [(id, rtexpr)]
evalExpr env (CAssign aop lhs rhs _)
  | lhs == (CVar id _) = ntexpr nvl1
  | otherwise          = error "invalid expression to assign to"
  where rtexpr rvl1 = evalExpr env rhs
        ltexpr      = ap_texpr1_var env id
        ntexpr      = ap_texpr1_binop ((evalAOp aop) ltexpr rtexpr AP_RTYPE_INT AP_RDIR_NEAREST)
        nvl1        = rvl1 ++ [(id, ntexpr)]

evalExpr abs1@(_ env) (CConst (CInteger ccst _) _) =
  (ap_texpr1_cst_scalar_int env ccst) []

evalExpr _ _ = error "expression not implemented"
-}


{- Operations -}
{-
evalAOp :: CAssignOp -> TexprOp
evalAOp aop =
  case aop of
    CMulAssOp -> AP_TEXPR_MUL
    CDivAssOp -> AP_TEXPR_DIV
    CRmdAssOp -> AP_TEXPR_MOD
    CAddAssOp -> AP_TEXPR_ADD
    CSubAssOp -> AP_TEXPR_SUB
    CShlAssOp -> error "Unsupported AOp <<="
    CShrAssOp -> error "Unsupported AOp >>="
    CAndAssOp -> error "Unsupported AOp &="
    CXorAssOp -> error "Unsupported AOp ^="
    COrAssOp  -> error "Unsupported AOp |="
-}
