-- A module that deals with narrowing of a loop analysis.
-- Two narrowing methods are considered:
-- Delayed narrowing: bound the number of iteration of the loop
-- Threshold narrowing: give a precise terminate condition of the loop
-- Assumption: the loop will be executed at least once
-- We don't have to deal with scope in this module, as everything is in the
-- same function

module Loop where

import Init
import Abstract1
import AbstractMonad
import Texpr1
import Tcons1
import Language.C.Syntax.AST
import Language.C.Data.Ident
import Language.C.Syntax.Constants

type VarState = (String, Maybe (Bool, Integer))

-- Obtain the relative constraint from the constraint and initial value
-- i.e. init is a = 7; constraint is a < 5, then actual constraint is a < -2
-- Condition list and VarState by definition must match
initConsState :: [(String, CBinaryOp, Integer)] -> [VarState] -> [(String, CBinaryOp, Maybe Integer)]
initConsState [] [] = []
initConsState ((v, bop, i1):cs) ((_, Just(True, i2)):vs) =
  [(v, bop, Just (i1 - i2))] ++ initConsState cs vs
initConsState ((var, bop, _):cs) (v:vs) = 
  [(var, bop, Nothing)] ++ initConsState cs vs

-- Convert the varState we obtain from initialization to the one we need
-- for analysis
initVarState :: VarState -> VarState
initVarState (var, Just (True, val))  = (var, Just (False, 0))
initVarState (var, Just (False, val)) = (var, Just (False, 0))

-- Calculate the iteration required for each variable to satisfy its condition
-- 0  == the variable would never reach the condition
-- -2 == the number of iteration is undetermined
-- Condition list and VarState by definition must match
calVarIteration :: [(String, CBinaryOp, Maybe Integer)] -> [VarState] -> [(String, Integer)]
calVarIteration [] [] = []
calVarIteration ((v, bop, cons):cs) ((_, Nothing):vs) =
  [(v, -2)] ++ calVarIteration cs vs
calVarIteration ((v, bop, cons):cs) ((_, (Just (ass, change))):vs)
  | ass         = [(v, 0)] ++ calVarIteration cs vs
  | change == 0 = [(v, 0)] ++ calVarIteration cs vs
  -- If we do not know the initial value, we can still determine if the loop
  -- is non-term
  | cons == Nothing =
    case (bop, change < 0) of
      (CLeOp, True)   -> [(v, 0)] ++ calVarIteration cs vs
      (CGrOp, False)  -> [(v, 0)] ++ calVarIteration cs vs
      (CLeqOp, True)  -> [(v, 0)] ++ calVarIteration cs vs
      (CGeqOp, False) -> [(v, 0)] ++ calVarIteration cs vs
      (_, _)          -> [(v, -2)] ++ calVarIteration cs vs
 
  | otherwise =
    case (bop, change < 0) of
      (CLeOp, True)   -> [(v, 0)] ++ calVarIteration cs vs
      (CLeOp, False)  -> [(v, iNum)] ++ calVarIteration cs vs
      (CGrOp, True)   -> [(v, iNum)] ++ calVarIteration cs vs
      (CGrOp, False)  -> [(v, 0)] ++ calVarIteration cs vs
      (CLeqOp, True)  -> [(v, 0)] ++ calVarIteration cs vs
      (CLeqOp, False) -> [(v, iNum)] ++ calVarIteration cs vs
      (CGeqOp, True)  -> [(v, iNum)] ++ calVarIteration cs vs
      (CGeqOp, False) -> [(v, 0)] ++ calVarIteration cs vs
      (CNeqOp, _)     -> [(v, iNum)] ++ calVarIteration cs vs
      (_, _)          -> error "Loop Condition not supported"
  where Just n = cons  
        iNum = abs (calVarIterationHelper n change)

-- Helper function to get the correct iteration number
calVarIterationHelper :: Integer -> Integer -> Integer
calVarIterationHelper a b =
  case (c < 0) of
    True  -> floor c
    False -> ceiling c
  where c = (fromIntegral a) / (fromIntegral b)

-- Delayed narrowing:
-- The goal is to bound the number of iterations
-- The output n indicates that in the first n iterations, we would join the
-- result with the previous iteration, only after that we do widening
-- n == 0  indicates that the loop is non-term
-- n == -2 indicates that we cannot bound the iteration number
--
-- There is no real way to bound a while loop, since it is difficult to get
-- the initial state. We can however know if a while loop is non-term.
getIterationNum :: Abstract1 -> String -> (Either (Maybe (CExpression a)) (CDeclaration a)) -> CExpression a -> Maybe (CExpression a) -> CStatement a -> Abstract Integer
-- In a simple but widely used case, we deal with examples that has a condition
-- (ax1 + bx2 < c) and the vars (x1, x2) is changed linearly
getIterationNum a f init cond step stmt = do
  c1@(v, bop, i) <- getLoopCond cond
  let initSt = Just [(v, Just (False, 0))]
  let (Just inSt) = case init of
                      Left Nothing     -> initSt
                      Left (Just expr) -> fst (forwardExprCheck initSt expr)
                      Right decl       -> forwardDeclCheck initSt decl
  let consLst = initConsState [c1] inSt
  let iSt = map initVarState inSt
  let nSt = forwardCheck (Just iSt) stmt
  let fSt = case step of
              Nothing     -> nSt
              Just (expr) -> fst (forwardExprCheck nSt expr)
  let itLst = case fSt of
                (Just n) -> calVarIteration consLst n
                _        -> [("", -2)]
  return (snd (head itLst))

varStateJoin :: [VarState] -> VarState -> [VarState]
varStateJoin [] _ = []
varStateJoin ((_, Nothing):sts) st = varStateJoin sts st
varStateJoin ((cv, Just (cass, ci)):sts) st@(v, Just (ass, i))
  | (cv == v) && (ass == True) = [(cv, Just (ass, i))] ++ sts
  | cv == v                    = [(cv, Just (cass, ci + i))] ++ sts
  | otherwise = varStateJoin sts st

varAccessible :: String -> [VarState] -> Bool
varAccessible _ [] = False
varAccessible v ((cv, Nothing):sts)
  | v == cv   = False
  | otherwise = varAccessible v sts
varAccessible v ((cv, Just (_, _)):sts)
  | v == cv   = True
  | otherwise = varAccessible v sts

-- Forward-analyze a program to check the change of certain variables
-- We only aim for deterministic change
-- The state (var, bool, int) checks the change of a var in an iteration
-- The Boolean is True if the variable is assigned to a constant
-- ("a", False, +3) indicates an iteration increases a by 3
-- ("a", True, -7) indicates that a is -7 after every iteration,
-- since it would always be assigned somewhere in the loop
forwardCheck :: Maybe [VarState] -> CStatement a -> Maybe [VarState]
forwardCheck Nothing _ = Nothing
forwardCheck initSt (CExpr Nothing _) = initSt
forwardCheck initSt (CExpr (Just expr) _) = fst (forwardExprCheck initSt expr)
-- For If Statement, as long as the variable is changed the same way for
-- both cases, we are good
forwardCheck initSt (CIf cons tstmt Nothing _)
  | initSt == tSt = tSt
  | otherwise     = Nothing
  where tSt = forwardCheck initSt tstmt
forwardCheck initSt (CIf cons tstmt (Just fstmt) _)
  | tSt == fSt = tSt
  | otherwise  = Nothing
  where tSt = forwardCheck initSt tstmt
        fSt = forwardCheck initSt fstmt
-- We cannot determine if a loop would terminate, so any nested loop would
-- make analysus impossible
forwardCheck _ (CFor _ _ _ _ _) = Nothing
forwardCheck _ (CWhile _ _ _ _) = Nothing
forwardCheck initSt (CCompound _ cbis _) = foldl forwardCBICheck initSt cbis

forwardCheck _ _ = error "Unsupported statements inside a loop"

forwardCBICheck :: Maybe [VarState] -> CCompoundBlockItem a -> Maybe [VarState]
forwardCBICheck Nothing _ = Nothing
forwardCBICheck initSt (CBlockStmt stmt) = forwardCheck initSt stmt
forwardCBICheck initSt (CBlockDecl decl) = forwardDeclCheck initSt decl

forwardDeclCheck :: Maybe [VarState] -> CDeclaration a -> Maybe [VarState]
forwardDeclCheck Nothing _ = Nothing
forwardDeclCheck initSt (CDecl _ d _) = foldl forwardDeclHelper initSt d

forwardDeclHelper :: Maybe [VarState] -> (Maybe (CDeclarator a), Maybe (CInitializer a), Maybe (CExpression a)) -> Maybe [VarState]
forwardDeclHelper Nothing _ = Nothing
forwardDeclHelper initSt (_, Nothing, Nothing) = initSt
forwardDeclHelper initSt@(Just is) (Just (CDeclr (Just (Ident v _ _)) _ _ _ _), (Just (CInitExpr expr _)), Nothing)
  | varAccessible v is =
    case (nSt, nVal) of
      (Nothing, _) -> Nothing
      (Just n, Nothing) -> Just (varStateJoin n (v, Nothing))
      (Just n, Just val) -> Just (varStateJoin n (v, Just (True, val)))
  | otherwise = nSt
    where (nSt, nVal) = forwardExprCheck initSt expr
forwardDeclHelper _ _ = error "Declaration case not supported"

-- We also need to keep track of the value of the current expression
-- Nothing if the current expression does not give us an integer value
forwardExprCheck :: Maybe [VarState] -> CExpression a -> (Maybe [VarState], Maybe Integer)
forwardExprCheck Nothing _ = (Nothing, Nothing)
forwardExprCheck initSt (CVar _ _) = (initSt, Nothing)
forwardExprCheck initSt (CConst (CIntConst cint _)) =
  (initSt, Just (getCInteger cint))
-- We need to deal with ++ or --
forwardExprCheck initSt@(Just is) (CUnary uop (CVar (Ident v _ _) _) _)
  | varAccessible v is =
    case uop of
      CPreIncOp  -> (Just (varStateJoin is (v, Just (False, 1))), Nothing)
      CPostIncOp -> (Just (varStateJoin is (v, Just (False, 1))), Nothing)
      CPreDecOp  -> (Just (varStateJoin is (v, Just (False, -1))), Nothing)
      CPostDecOp -> (Just (varStateJoin is (v, Just (False, -1))), Nothing)
      _          -> (initSt, Nothing)
  | otherwise = (initSt, Nothing)
forwardExprCheck _ _ = error "expression case not implemented in loop"

getLoopCond :: CExpression a -> Abstract (String, CBinaryOp, Integer)
getLoopCond (CBinary bop (CVar (Ident v _ _) _) (CConst (CIntConst cint _)) _) = do
  let i = getCInteger cint
  return (v, bop, i)
