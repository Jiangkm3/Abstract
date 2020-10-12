-- All Helper functions are not intended to be used as standalone functions
-- The main problem here is that I don't want the Abstract Monad to be wrapped
-- around the actual translation unit
-- The result is that only half of the operations are under Monad Operation,
-- while the other half operate directly above the Abstract Monad
-- The main division is during evalStmt:
-- all stmts that has sub-stmts can not be operated inside the Abstract Monad

module Eval where

import GHC.Int
import Init
import Operation
import Types
import Texpr1
import Tcons1
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

absLeqHelper :: Abstract Abstract1 -> Abstract Abstract1 -> Abstract Bool
absEqualityHelper a1 a2 = do
  abs1 <- a1
  abs2 <- a2
  b <- abstractIsLeq a1 a2
  return b

absFuncHelper :: Abstract Abstract1 -> Abstract Abstract1 -> (Abstract1 -> Abstract1 -> Abstract Abstract1) -> Abstract Abstract1
absFuncHelper a1 a2 f = do
  abs1 <- a1
  abs2 <- a2
  abs3 <- f abs1 abs2
  return abs3

--  We don't use monad here because we don't want the Translation Unit
--  to be under the Abstract Monad
--  Dealing with If, while and for
--  Maybe (Abstract Abstract1) is to record the last iteration when doing
--  fixpoint analysis
evalNestedHelper :: Abstract Abstract1 -> String -> CStatement AbsState -> Maybe (Abstract Abstract1) -> CStatement AbsState
evalNestedHelper a f (CIf cons tstmt Nothing st) _ = 
  CIf cons ntStmt Nothing nSt
  where itAbs           = evalCons a f cons False
        (ntAbs, ntStmt) = evalStmt itAbs f tstmt
        nAbs            = absFuncHelper a ntAbs abstractJoin
        nSt             = setAbs nAbs st
evalNestedHelper a f (CIf cons tstmt (Just fstmt) st) _ = 
  CIf cons ntStmt (Just nfStmt) nSt
  where itAbs           = evalCons a f cons False
        ifAbs           = evalCons a f cons True
        (ntAbs, ntStmt) = evalStmt itAbs f tstmt
        (nfAbs, nfStmt) = evalStmt ifAbs f fstmt
        nAbs            = absFuncHelper ntAbs nfAbs abstractJoin
        nSt             = setAbs nAbs st

-- DoWhile
-- evalNestedHelper a f (CWhile cond stmt True st) =
-- While
-- We want to widen the true case (while loop executed) and join it with the
-- false case (while loop not executed)
evalNestedHelper a f whileStmt@(CWhile cond stmt False st) (Just lastAbs)
  | = CWhile cond nStmt False nSt
  | otherwise          = evalNestedHelper a f whileStmt (Just nAbs)
  where itAbs          = evalCons a f cond False
        (ntAbs, nStmt) = evalStmt itAbs f stmt
        tAbs           = absFuncHelper itAbs ntAbs abstractWiden
        nAbs           = absFuncHelper a tAbs abstractJoin
		leqEval        = absLeqHelper nAbs lastAbs
        finalAbs       = evalCons joinAbs f cond True
        nSt            = setAbs finalAbs st

evalNestedHelper _ _ _ _ = error "Invalid Nested Statement"

evalStmt :: Abstract Abstract1 -> String -> CStatement AbsState -> (Abstract Abstract1, CStatement AbsState)
evalStmt a f (CCompound ids cbis st) = (nAbs, CCompound ids ncbis newSt)
  where (nAbs, ncbis) = evalCBIs a f cbis
        newSt = setAbs nAbs st
evalStmt a f stmt@(CIf _ _ _ _) = (nAbs, nStmt)
  where nStmt@(CIf _ _ _ (State nAbs _)) = evalNestedHelper a f stmt Nothing
evalStmt a f stmt@(CWhile _ _ _ _) = (nAbs, nStmt)
  where nStmt@(CWhile _ _ _ (State nAbs _)) = evalNestedHelper a f stmt (Just a)
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
-- Every constraint evaluated in evalExpr is treated as a number
-- i.e. evaluate the constraint and return 0 or 1 based on result
evalExpr :: Abstract1 -> String -> CExpression AbsState -> Abstract ExprSt

evalExpr a f (CAssign CAssignOp (CVar (Ident v _ _) _) rhs _) = do
  -- Technically ++a would be different but ignore it for now
  var <- findScope v f
  (rtexpr, rpair) <- evalExpr a f rhs
  return (rtexpr, rpair ++ [(var, rtexpr)])

evalExpr a f (CAssign aop (CVar (Ident v _ _) _) rhs _) = do
  var <- findScope v f
  ltexpr <- texprMakeLeafVar var
  (rtexpr, rpair) <- evalExpr a f rhs
  ntexpr <- evalBOpExpr (convertAOp aop) ltexpr rtexpr
  return (ntexpr, rpair ++ [(var, ntexpr)])

evalExpr a f (CVar (Ident v _ _) _) = do
  var <- findScope v f
  ntexpr <- texprMakeLeafVar var
  return (ntexpr, [])

evalExpr a f (CConst (CIntConst n _)) = do
  ntexpr <- texprMakeConstant $ ScalarVal $ IntValue $ (fromInteger (getCInteger n) :: Int32)
  return (ntexpr, [])

evalExpr a f (CBinary bop expr1 expr2 _)
  | isBOpCons bop = error "Boolean evaluation not supported"
{-
  | isBOpCons bop = do
    (ltexpr, lpair) <- evalExpr a f expr1
    (rtexpr, rpair) <- evalExpr a f expr2
    ncons <- evalBOpCons bop ltexpr rtexpr
    arr <- tconsArrayMake 1
    tconsArraySetIndex arr 0 ncons
    abs <- abstractTconsArrayMeet a arr
    b <- abstractIsBottom abs
    ntexpr <- texprMakeConstant $ ScalarVal $ IntValue $ (1 - evalBool b)
    return (ntexpr, lpair ++ rpair)
-}
  | isBOpLogic bop = error "Boolean evaluation not supported"
  | otherwise = do
    (ltexpr, lpair) <- evalExpr a f expr1
    (rtexpr, rpair) <- evalExpr a f expr2
    ntexpr <- evalBOpExpr bop ltexpr rtexpr
    return (ntexpr, lpair ++ rpair)

evalExpr a f e@(CUnary uop expr _) = do
  st@(rtexpr, rpair) <- evalExpr a f expr
  ntexpr <- evalUOpExpr uop rtexpr
  case uop of
    CPreIncOp  -> incDecHelper expr f uop ntexpr st
    CPreDecOp  -> incDecHelper expr f uop ntexpr st
    CPostIncOp -> incDecHelper expr f uop ntexpr st
    CPostDecOp -> incDecHelper expr f uop ntexpr st
    -- The Plus Operator literally does nothing
    _          -> return (ntexpr, rpair)

evalExpr _ _ _ = error "expression not impemented"

evalBool :: Bool -> Int32
evalBool b =
  case b of
    True  -> 1
    False -> 0

-- A helper function to deal with ++ and --
incDecHelper :: CExpression AbsState -> String -> CUnaryOp -> Texpr1 -> ExprSt -> Abstract ExprSt
incDecHelper (CVar (Ident v _ _) _) f uop ntexpr (rtexpr, rpair) = do
  -- expr must be in the form of CVar
  var <- findScope v f
  let npair = rpair ++ [(var, ntexpr)]
  case uop of
    CPreIncOp  -> return (ntexpr, npair) -- ++a
    CPreDecOp  -> return (ntexpr, npair) -- --a
    CPostIncOp -> return (rtexpr, npair) -- a++
    CPostDecOp -> return (rtexpr, npair) -- a--

-- Evaluate Constraints, evaluate side effects, meet constraint with abstract1
-- Bool is to determine if we want !(constraint)
-- True if we want !(constraint)
-- evalCons takes in Abstract Abstract1, as oppose to evalExpr taking Abstract1
evalCons :: Abstract Abstract1 -> String -> CExpression AbsState -> Bool -> Abstract Abstract1
evalCons abs f (CBinary bop expr1 expr2 _) neg
  | isBOpCons bop = do
    a <- abs
    (ltexpr, lpair) <- evalExpr a f expr1
    (rtexpr, rpair) <- evalExpr a f expr2
    lAbs <- foldl absAssgHelper (return a) (lpair ++ rpair)
    ntcons <- evalBOpCons bop ltexpr rtexpr neg
    arr <- tconsArrayMake 1
    tconsArraySetIndex arr 0 ntcons
    nAbs <- abstractTconsArrayMeet lAbs arr
    return nAbs
    
  | otherwise     = error "Int to Bool Conversion not supported"
evalCons a f _ _ = error "Int to Bool Conversion not supported"

-- Helper Function to determine if we are evaluating a tree expression
-- or a tree constraint
-- True if the operation is a constraint operation
isBOpCons :: CBinaryOp -> Bool
isBOpCons bop =
  case bop of
    CLeOp  -> True
    CGrOp  -> True
    CLeqOp -> True
    CGeqOp -> True
    CEqOp  -> True
    CNeqOp -> True
    _      -> False

isBOpLogic :: CBinaryOp -> Bool
isBOpLogic bop =
  case bop of
    CLndOp -> True
    CLorOp -> True
    _      -> False
