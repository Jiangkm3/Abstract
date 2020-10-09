import Init
import AbstractMonad
import Abstract1
import Eval
import Printer

main = do
  iast <- analyzeAST "/home/jiangkm3/peppersieve/app/test.c"
  nast <- evalProg iast
  printTU nast
