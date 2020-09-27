import Init
import Example
import AbstractMonad
import Abstract1
import Eval
import Printer

main = do
  iast <- analyzeAST "/home/jiangkm3/apron-bindings/app/test.c"
  nast <- evalProg iast
  printTU nast
