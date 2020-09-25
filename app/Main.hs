import Init
import Example
import AbstractMonad
import Abstract1
import Eval
import Printer

main = do
  iast <- analyzeAST "/home/jiangkm3/apron-bindings/app/test.c"
  print("Initialized")
  nast <- evalProg iast
  printTU nast
  print("Analyzed")
