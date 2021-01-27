import Control.Monad
import Init
import AbstractMonad
import Abstract1
import Eval
import Printer
import System.Console.GetOpt
import System.Environment
import System.Exit
import System.IO
import Text.Printf

main = getArgs >>= parse 

parse [fileName] = analyze fileName >> exitSuccess

parse _ = die "Usage: apron-bindings-exe <C input file>" 

analyze fileName = do
  iast <- analyzeAST fileName
  let nast = evalProg iast
  initPrinter nast fileName
