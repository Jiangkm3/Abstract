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
  putStrLn ("Func " ++ name ++ ":")
  putStrLn ("Arguments:" ++ (unwords (map printDerivedDecl derived)))
  printSt st
  putStrLn ""
  printStmt cstmt
  putStrLn "--"
  putStrLn ""
printED _                = do
  return ()

printDerivedDecl :: CDerivedDeclarator AbsState -> String
printDerivedDecl (CFunDeclr (Right (decls, False)) _ _) = unwords (map printArgs decls)
printDerivedDecl _ = ""

printArgs :: CDeclaration AbsState -> String
printArgs (CDecl _ vars _) = " " ++ (unwords (map (\(Just (CDeclr (Just (Ident varName _ _)) _ _ _ _), Nothing, Nothing) -> varName) vars))

printDecl :: CDeclaration AbsState -> IO ()
printDecl (CDecl _ vars st) = do
  putStrLn ("Declaration: " ++ (unwords (map (\(Just (CDeclr (Just (Ident varName _ _)) _ _ _ _), Nothing, Nothing) -> varName) vars)))
  printSt st

printStmt :: CStatement AbsState -> IO ()
printStmt (CCompound _ cbis _)     = printCBIs cbis
printStmt (CReturn (Just expr) st) = do
  putStrLn ("Return: " ++ printExpr expr)
  printSt st
printStmt (CReturn Nothing st)     = do
  putStrLn "Return Void"
  printSt st
printStmt _                        = error "Not Implemented"

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

printExpr :: CExpression AbsState -> String
printExpr (CConst (CIntConst cint _)) = show (getCInteger cint)
printExpr (CBinary bop expr1 expr2 _) = str1 ++ " " ++ strop ++ " " ++ str2
  where str1 = printExpr expr1
        strop = printBop bop
        str2 = printExpr expr2
printExpr _ = error "Not Implemented"

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
    
