module Printer where

import Init
import Abstract1
import AbstractMonad
import Language.C.Data.Ident
import Language.C.Syntax.AST
import Language.C.Syntax.Constants

-- Helper function to print the varstate
printSt :: AbsState -> IO()
printSt (State st _) = astPrinter st

printTU :: CTranslationUnit AbsState -> IO ()
printTU (CTranslUnit [] _) = do
  return ()
printTU (CTranslUnit (ed:eds) a@(State b _)) = do
  printED ed
  printTU (CTranslUnit eds a)

printED :: CExternalDeclaration AbsState -> IO ()
printED (CDeclExt cdecl) = do
  printDecl cdecl
  putStrLn ""
printED (CFDefExt (CFunDef _ (CDeclr (Just (Ident name _ _)) derived _ _ _) _ cstmt st)) = do
  putStrLn ("Function " ++ name ++ ":")
  putStrLn ("Arguments:" ++ (unwords (map printDerivedDecl derived)))
  putStrLn ""
  printStmt cstmt
  putStrLn "End Function\n\n--"
  putStrLn ""
printED _ = do
  return ()

printDerivedDecl :: CDerivedDeclarator AbsState -> String
printDerivedDecl (CFunDeclr (Right (decls, False)) _ _) = unwords (map printArgs decls)
printDerivedDecl _ = ""

printArgs :: CDeclaration AbsState -> String
printArgs (CDecl _ vars _) = " " ++ (unwords (map (\(Just (CDeclr (Just (Ident varName _ _)) _ _ _ _), Nothing, Nothing) -> varName) vars))

-- Function and Statement Level

printDecl :: CDeclaration AbsState -> IO ()
printDecl (CDecl _ vars st) = do
  putStrLn ("Decl: " ++ (init (unwords (map printDeclHelper vars))))
  printSt st

printDeclHelper :: (Maybe (CDeclarator AbsState), Maybe (CInitializer AbsState), Maybe (CExpression AbsState)) -> String
printDeclHelper (Just (CDeclr (Just (Ident varName _ _)) _ _ _ _), Nothing, Nothing) = varName ++ ","
printDeclHelper (Just (CDeclr (Just (Ident varName _ _)) _ _ _ _), (Just (CInitExpr expr _)), Nothing) = varName ++ " = " ++ (printExpr expr) ++ ","
pritnDeclHelper _ = error "Declaration case not implemented"

printStmt :: CStatement AbsState -> IO ()
printStmt (CCompound _ cbis _)     = printCBIs cbis
printStmt (CReturn (Just expr) st) = do
  putStrLn ("Return: " ++ printExpr expr)
  printSt st
printStmt (CExpr Nothing _) = return()
printStmt (CExpr (Just expr) st) = do
  putStrLn ("Expr: " ++ printExpr expr)
  printSt st
printStmt (CReturn Nothing st) = do
  putStrLn "Return Void"
  printSt st
-- fstmt is of type Maybe (CStatmenet AbsState)
printStmt (CIf expr tstmt fstmt st) = do
  putStrLn ("If " ++ (printExpr expr) ++ ":\n")
  printStmt tstmt
  putStrLn "Else:\n"
  case fstmt of
    Nothing -> putStrLn "Nothing or not Evaluated\n"
    Just a -> printStmt a
  putStrLn "End If"
  printSt st
-- While Statement
printStmt (CWhile expr stmt False st) = do
  putStrLn ("While " ++ (printExpr expr) ++ ":\n")
  printStmt stmt
  putStrLn "End While\n"
  printSt st
-- Do-While Statement
printStmt (CWhile expr stmt True st) = do
  putStrLn "Do:\n"
  printStmt stmt
  putStrLn ("While " ++ (printExpr expr) ++ "\n")
  putStrLn "End Do-While"
  printSt st
printStmt (CFor init bound step stmt st) = do
  putStrLn "For:"
  case init of
    Left Nothing           -> putStrLn "Init: None"
    Left (Just expr)       -> putStrLn ("Init: " ++ (printExpr expr))
    Right decl             -> printDecl decl
  case bound of
    Nothing   -> putStrLn "Bound: None"
    Just expr -> putStrLn ("Bound: " ++ (printExpr expr))
  case step of
    Nothing   -> putStrLn "Step: None"
    Just expr -> putStrLn ("Step: " ++ (printExpr expr))
  putStrLn ""
  printStmt stmt
  putStrLn "End For"
  printSt st
printStmt _ = error "Statement Case Not Implemented"

printCBIs :: [CCompoundBlockItem AbsState] -> IO ()
printCBIs [] = return ()
printCBIs ((CBlockStmt stmt):cbis) = do
  printStmt stmt
  putStrLn ""
  printCBIs cbis
printCBIs ((CBlockDecl decl):cbis) = do
  printDecl decl
  putStrLn ""
  printCBIs cbis
printCBIs _ = error "Nested Function not Implemented"

-- Expression Level

printExpr :: CExpression AbsState -> String
printExpr (CConst (CIntConst cint _)) = show (getCInteger cint)
printExpr (CVar (Ident n _ _) _) = n
printExpr (CBinary bop expr1 expr2 _) = str1 ++ " " ++ strop ++ " " ++ str2
  where str1  = printExpr expr1
        strop = printBop bop
        str2  = printExpr expr2
printExpr (CUnary unop expr _) =
  case (isPrefixOp unop) of
    True  -> strop ++ str
    False -> str ++ strop
  where strop = printUnop unop
        str   = printExpr expr
printExpr (CAssign assop expr1 expr2 _) = "Assign: " ++ str1 ++ " " ++ strop ++ " " ++ str2
  where str1 = printExpr expr1
        strop = printAssop assop
        str2 = printExpr expr2
printExpr _ = error "Expression Case Not Implemented"

isPrefixOp :: CUnaryOp -> Bool
isPrefixOp unop = 
  case unop of
    CPostIncOp -> False
    CPostDecOp -> False
    _         -> True

printBop :: CBinaryOp -> String
printBop bop =
  case bop of
    CMulOp -> "*"
    CDivOp -> "/"
    CRmdOp -> "%"
    CAddOp -> "+"
    CSubOp -> "-"
    CShlOp -> "<<"
    CShrOp -> ">>"
    CLeOp  -> "<"
    CGrOp  -> ">"
    CLeqOp -> "<="
    CGeqOp -> ">="
    CEqOp  -> "=="
    CNeqOp -> "!="
    CAndOp -> "&"
    CXorOp -> "^"
    COrOp  -> "|"
    CLndOp -> "&&"
    CLorOp -> "||"

printAssop ::  CAssignOp -> String
printAssop assop =
  case assop of
    CAssignOp -> "="
    CMulAssOp -> "*="
    CDivAssOp -> "/="
    CRmdAssOp -> "%="
    CAddAssOp -> "+="
    CSubAssOp -> "-="
    CShlAssOp -> "<<="
    CShrAssOp -> ">>="
    CAndAssOp -> "&="
    CXorAssOp -> "^="
    COrAssOp  -> "|="

printUnop :: CUnaryOp -> String
printUnop unop =
  case unop of
    CPreIncOp  -> "++"
    CPreDecOp  -> "--"
    CPostIncOp -> "++"
    CPostDecOp -> "--"
    CAdrOp     -> "&"
    CIndOp     -> "*"
    CPlusOp    -> "+"
    CMinOp     -> "-"
    CCompOp    -> "~"
    CNegOp     -> "!"
