module Printer where

import Init
import Abstract1
import AbstractMonad
import Language.C.Data.Ident
import Language.C.Syntax.AST


printTU :: CTranslationUnit AbsState -> IO ()
printTU (CTranslUnit [] _) = do
  return ()
printTU (CTranslUnit (ed:eds) a) = do
  printED ed
  printTU (CTranslUnit eds a)

printED :: CExternalDeclaration AbsState -> IO ()
printED (CDeclExt cdecl) = do
  error "PrintDecl not implemented"
printED (CFDefExt (CFunDef _ (CDeclr (Just (Ident name _ _)) derived _ _ _) _ cstmt (State st _))) = do
  print ("Func " ++ name ++ ":")
  print ("Arguments: " ++ (unwords (map printDerivedDecl derived)))
  astPrinter st
printED _                = do
  return ()

printDerivedDecl :: CDerivedDeclarator AbsState -> String
printDerivedDecl (CFunDeclr (Right (decls, False)) _ _) = unwords (map printDecl decls)
printDerivedDecl _ = ""

printDecl :: CDeclaration AbsState -> String
printDecl (CDecl _ vars _) = (unwords (map (\(Just (CDeclr (Just (Ident varName _ _)) _ _ _ _), Nothing, Nothing) -> varName) vars)) ++ ";"
