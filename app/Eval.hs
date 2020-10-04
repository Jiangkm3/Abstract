-- All Helper functions are not intended to be used as standalone functions

module Eval where

import GHC.Int
import Init
import Types
import Texpr1
import Abstract1
import AbstractMonad
import Apron.Var
import Apron.Environment
import Language.C.Data.Ident
import Language.C.Data.Node
import Language.C.Syntax.AST
import Language.C.Syntax.Constants
import Control.Monad.State.Strict (liftIO)

-----

{- Program -}
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
evalEDLst preC (ed:eds) = [newED] ++ (evalEDLst newAbs eds)
  where (newAbs, newED) = evalExtDecl preC ed

evalExtDecl :: Abstract Abstract1 -> CExternalDeclaration AbsState -> (Abstract Abstract1, CExternalDeclaration AbsState)
evalExtDecl abs (CDeclExt a) = (nAbs, CDeclExt nDecl)
  where (nAbs, nDecl) = evalDecl abs "" a
evalExtDecl abs (CFDefExt a) = (nAbs, CFDefExt nFunc)
  where (nAbs, nFunc) = evalFunc abs a
evalExtDecl abs _            = error "Not Implemented"

-----

{- Functions -}
-- ignore arguments for now
evalFunc :: Abstract Abstract1 -> CFunctionDef AbsState -> (Abstract Abstract1, CFunctionDef AbsState)
evalFunc preC (CFunDef a b@(CDeclr (Just (Ident f _ _)) _ _ _ _) c stmt st) =
  (nAbs, CFunDef a b c nStmt newSt)
  where (nAbs, nStmt) = evalStmt preC f stmt
        newSt = setAbs nAbs st

-- Assume that the variable must exist
-- We only need to find if it is local or global
findScope :: String -> String -> Abstract String
findScope varName funcName
  | funcName == "" = return varName
  | otherwise = do
    let localName = funcName ++ "@" ++ varName
    l <- findVar localName
    case l of
      True  -> return localName
      False -> return varName

-----

{- Declarations -}
-- Right now that we don't care about types, the only concern is
-- with the initializers and expressions
-- Variable f for the name of the function we're in so we can determine
-- the scope. f = "" indicates that this is a global environment
evalDecl :: Abstract Abstract1 -> String -> CDeclaration AbsState -> (Abstract Abstract1, CDeclaration AbsState)
evalDecl preC f (CDecl a b (State _ loc)) = (nAbs, CDecl a b (State nAbs loc))
  where nAbs = foldl (\a b -> evalDeclHelper a f b) preC b

absAssgHelper :: Abstract Abstract1 -> (VarName, Texpr1) -> Abstract Abstract1
absAssgHelper a (v, t) = do
  a1 <- a
  a2 <- abstractTop
  abstractAssignTexprArray a1 [v] t 1 a2

-- Process every variable declaration separately
evalDeclHelper :: Abstract Abstract1 -> String -> (Maybe (CDeclarator AbsState), Maybe (CInitializer AbsState), Maybe (CExpression AbsState)) -> Abstract Abstract1
-- If it is only a declaration, no need to change the abstraction
evalDeclHelper a _ (_, Nothing, Nothing) = a

evalDeclHelper a f (Just (CDeclr (Just (Ident v _ _)) _ _ _ _), (Just (CInitExpr expr _)), Nothing) = do
  abs1 <- a
  (texpr, pair) <- evalExpr abs1 f expr
  var <- findScope v f
  let npair = pair ++ [(var, texpr)]
  foldl absAssgHelper a npair

evalDeclHelper _ _ _ = error "Not implemented"

-----

{- Statements -}
-- helper function
setAbs :: Abstract Abstract1 -> AbsState -> AbsState
setAbs a (State _ loc) = State a loc

-- A helper function to evaluate compounds
evalCBI :: Abstract Abstract1 -> String -> CCompoundBlockItem AbsState -> (Abstract Abstract1, CCompoundBlockItem AbsState)
evalCBI abs f (CBlockStmt stmt) = (nAbs, CBlockStmt nStmt)
  where (nAbs, nStmt) = evalStmt abs f stmt
evalCBI abs f (CBlockDecl decl) = (nAbs, CBlockDecl nDecl)
  where (nAbs, nDecl) = evalDecl abs f decl
evalCBI _ _ _ = error "Not Implemented"

evalCBIs :: Abstract Abstract1 -> String -> [CCompoundBlockItem AbsState] -> (Abstract Abstract1, [CCompoundBlockItem AbsState])
evalCBIs abs f [] = (abs, [])
evalCBIs abs f (cbi:cbis) = (finalAbs, [nCbi] ++ fCbis)
  where (nextAbs, nCbi)   = evalCBI abs f cbi
        (finalAbs, fCbis) = evalCBIs nextAbs f cbis

evalStmtHelper :: Abstract Abstract1 -> String -> CStatement AbsState -> Abstract Abstract1

evalStmtHelper a _ (CExpr Nothing _) = a
-- We can disregard the side effect of the expression
evalStmtHelper a f (CExpr (Just expr) st) = do
  abs1 <- a
  (_, pair) <- evalExpr abs1 f expr
  foldl absAssgHelper a pair

evalStmtHelper a f (CReturn Nothing _) = a
evalStmtHelper a f (CReturn (Just expr) st) = do
  abs1 <- a
  (texpr, pair) <- evalExpr abs1 f expr
  let npair = pair ++ [(f, texpr)]
  foldl absAssgHelper a npair

evalStmtHelper _ _ _ = error "Not Implemented"


evalStmt :: Abstract Abstract1 -> String -> CStatement AbsState -> (Abstract Abstract1, CStatement AbsState)
evalStmt a f (CCompound ids cbis st) = (nAbs, CCompound ids ncbis newSt)
  where (nAbs, ncbis) = evalCBIs a f cbis
        newSt = setAbs nAbs st
evalStmt a f stmt =
  case stmt of
    CExpr Nothing st       -> (nAbs, CExpr Nothing (newSt st))
    CExpr (Just expr) st   -> (nAbs, CExpr (Just expr) (newSt st))
    CReturn Nothing st     -> (nAbs, CReturn Nothing (newSt st))
    CReturn (Just expr) st -> (nAbs, CReturn (Just expr) (newSt st))
    _                      -> error "Not Implemented"

  where nAbs          = evalStmtHelper a f stmt
        newSt         = \a -> setAbs nAbs a

-----

{- Expressions -}
-- A special return type for evaluating an expression
-- An expression can generate a syntax tree, but might also involve assignments
type ExprSt = (Texpr1, [(VarName, Texpr1)])

evalVar :: Abstract Abstract1 -> VarName -> Abstract Var
evalVar a v = do
  abs <- a
  var <- getVar v
  return var

-- f is the name of Function we're currently in
-- Convention: only check the scope when directly referencing the variable
-- Either in assignment or variable expression
evalExpr :: Abstract1 -> String -> CExpression AbsState -> Abstract ExprSt

evalExpr a f (CAssign CAssignOp (CVar (Ident v _ _) _) rhs _) = do
  -- Technically ++a would be different but ignore it for now
  var <- findScope v f
  (rtexpr, rpair) <- evalExpr a f rhs
  return (rtexpr, rpair ++ [(var, rtexpr)])

evalExpr a f (CAssign aop (CVar (Ident v _ _) _) rhs _) = do
  var <- findScope v f
  (rtexpr, rpair) <- evalExpr a f rhs
  ltexpr <- texprMakeLeafVar var
  ntexpr <- texprMakeBinOp (evalAOp aop) ltexpr rtexpr ROUND_INT ROUND_NEAREST
  return (ntexpr, rpair ++ [(var, ntexpr)])

evalExpr a f (CVar (Ident v _ _) _) = do
  var <- findScope v f
  ntexpr <- texprMakeLeafVar var
  return (ntexpr, [])

evalExpr a f (CConst (CIntConst n _)) = do
  ntexpr <- texprMakeConstant $ ScalarVal $ IntValue $ (fromInteger (getCInteger n) :: GHC.Int.Int32)
  return (ntexpr, [])

evalExpr _ _ _ = error "expression not implemented"


{- Operations -}
evalAOp :: CAssignOp -> OpType
evalAOp aop =
  case aop of
    CMulAssOp -> MUL_OP
    CDivAssOp -> DIV_OP
    CRmdAssOp -> MOD_OP
    CAddAssOp -> ADD_OP
    CSubAssOp -> SUB_OP
    CShlAssOp -> error "Unsupported AssOp <<="
    CShrAssOp -> error "Unsupported AssOp >>="
    CAndAssOp -> error "Unsupported AssOp &="
    CXorAssOp -> error "Unsupported AssOp ^="
    COrAssOp  -> error "Unsupported AssOp |="

evalBOp ::  CBinaryOp -> OpType
evalBOp bop =
  case bop of
    CMulOp -> MUL_OP
    CDivOp -> DIV_OP
    CRmdOp -> MOD_OP
    CAddOp -> ADD_OP
    CSubOp -> SUB_OP
    _      -> error "Unsupported BinOp"
