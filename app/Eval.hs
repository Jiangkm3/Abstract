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


{- Programs -}
evalProg :: CTranslationUnit (AbsState) -> IO (CTranslationUnit (AbsState))
evalProg (CTranslUnit extDecls a) = do
  let tu = CTranslUnit (map evalExtDecl extDecls) a
  return tu


evalExtDecl :: CExternalDeclaration (AbsState) -> CExternalDeclaration (AbsState)
evalExtDecl (CDeclExt a) = error "Declaration not implemented"
evalExtDecl (CFDefExt a) = CFDefExt (evalFunc a)
evalExtDecl _            = error "Not Implemented"


{- Functions -}
-- Initialize the state of a function:
-- All args = Top
-- All other variables = Bot
initFunc :: Abstract Abstract1 -> CFunctionDef AbsState -> Abstract Abstract1
initFunc abs1 func@(CFunDef _ (CDeclr (Just (Ident name _ _)) derived _ _ _) _ _ _) = do
  let varLst = derived >>= initFuncHelper name
  initAbstractState Intervals varLst []
  args <- abstractTop
  vars <- abs1
  nvars <- abstractMeet vars args
  return nvars

-- Find all the arguments faster
initFuncHelper :: String -> CDerivedDeclarator AbsState -> [String]
initFuncHelper fname (CFunDeclr (Right (decls, False)) _ _) = do
  (CDecl _ vars _) <- decls
  ndecl <- map (\(Just (CDeclr (Just (Ident varName _ _)) _ _ _ _), Nothing, Nothing) -> (fname ++ "@" ++ varName)) vars
  return ndecl

evalFunc :: CFunctionDef AbsState -> CFunctionDef AbsState
evalFunc func@(CFunDef a b c d (State st loc)) = initF
  where nst   = initFunc st func
        initF = CFunDef a b c d (State nst loc)

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
