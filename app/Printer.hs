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
  error "PrintDecl not implemented"
printED (CFDefExt (CFunDef _ (CDeclr (Just (Ident name _ _)) derived _ _ _) _ cstmt st)) = do
  putStrLn ("Function " ++ name ++ ":")
  putStrLn ("Arguments:" ++ (unwords (map printDerivedDecl derived)))
  printSt st
  putStrLn ""
  printStmt cstmt
  putStrLn "--"
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
  putStrLn ("Declaration: " ++ (init (unwords (map printDeclHelper vars))))
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
  putStrLn (printExpr expr)
  printSt st
printStmt (CReturn Nothing st) = do
  putStrLn "Return Void"
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
  where str1 = printExpr expr1
        strop = printBop bop
        str2 = printExpr expr2
printExpr (CAssign assop expr1 expr2 _) = "Assign: " ++ str1 ++ " " ++ strop ++ " " ++ str2
  where str1 = printExpr expr1
        strop = printAssop assop
        str2 = printExpr expr2
printExpr _ = error "Expression Case Not Implemented"

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
