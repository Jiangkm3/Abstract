module Init where
import           Language.C.Data.Ident
import           Language.C.Data.Node
import           Language.C.Syntax.AST
import           Parser
import           Symbol
import           Abstract1
import           Abstract
import           AbstractMonad

-- | A simple user-defined AST annotation type
-- You can extend this if it would be helpful
-- For now it perserves source code location info
data State a = State { stInfo  :: a
                     , locInfo :: NodeInfo
                     }
  deriving (Eq, Ord, Show)


toState :: a -> NodeInfo -> State a
toState = State

-- | Dummy state
type PostState = Abstract1

printSt :: Abstract Abstract1 -> IO String
printSt abs1 = do
  return "State"

-- | Uses language-c's built-in (nice) annotation support
-- See here for more info:
-- https://hackage.haskell.org/package/language-c-0.8.3/docs/Language-C-Syntax-AST.html#g:9
initTo :: a -> CTranslUnit -> CTranslationUnit (State a)
initTo abs1 t = toState abs1 <$> t

-- | Initialize everything to a start state and then print the AST
analyzeAST :: String -> IO ()
analyzeAST name = do
  symT <- getSymT name
  return (initAbstractState Intervals symT [])
  abstract <- return abstractBottom
  tu <- parseC name
  print $ initTo abstract tu
