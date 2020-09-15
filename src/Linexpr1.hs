module Linexpr1 ( Linexpr1
                , linexprMake
                , linexprMinimize
                , linexprCopy
                -- * Tests
                , linexprIsInteger
                , linexprIsReal
                , linexprIsLinear
                , linexprIsQuasilinear
                -- * Access
                , linexprGetConstant
                , linexprGetCoeff
                -- * Setters
                , linexprSetConstant
                , linexprSetCoeffs
                , linexprSetCoeff
                ) where
import           AbstractMonad
import           Apron.Coeff
import           Apron.Linexpr1
import           Coeff
import           Control.Monad.State.Strict (liftIO)
import           Data.Int                   (Int32)
import           Data.Word
import           Types

-- | Build a linear expressions with by default coefficients of type SCALAR and DOUBLE.
-- If lin_discr selects a dense representation, the size of the expression is the size
-- of the environment.
-- Otherwise, the initial size is given by size and the expression may be resized lazily.
linexprMake :: LinexprDescrip -> Word32 -> Abstract Linexpr1
linexprMake d size = do
  env <- getEnvironment
  liftIO $ apLinexpr1MakeWrapper env d $ fromIntegral size

-- | In case of sparse representation, remove zero coefficients.
linexprMinimize :: Linexpr1 -> Abstract ()
linexprMinimize = liftIO . apLinexpr1MinimizeWrapper

-- | Make a copy of the linear expression.
linexprCopy :: Linexpr1 -> Abstract Linexpr1
linexprCopy = liftIO . apLinexpr1CopyWrapper

-- Tests

-- | Does the expression depends only on integer variables?
linexprIsInteger :: Linexpr1 -> Abstract Bool
linexprIsInteger = liftIO . apLinexpr1IsIntegerWrapper

-- | Does the expression depends only on real variables ?
linexprIsReal :: Linexpr1 -> Abstract Bool
linexprIsReal = liftIO . apLinexpr1IsRealWrapper

-- | Return true iff all involved coefficients are scalars.
linexprIsLinear :: Linexpr1 -> Abstract Bool
linexprIsLinear = liftIO . apLinexpr1IsLinearWrapper

-- | Return true iff all involved coefficients but the constant are scalars.
linexprIsQuasilinear :: Linexpr1 -> Abstract Bool
linexprIsQuasilinear = liftIO . apLinexpr1IsQuasilinearWrapper

-- Accesses

-- | Get a reference to the constant. Do not free it.
linexprGetConstant :: Linexpr1 -> Abstract Coeff
linexprGetConstant = liftIO . apLinexpr1CstrefWrapper

-- | Get a reference to the coefficient associated to the variable.
-- In case of sparse representation, possibly induce the addition of a new linear term.
-- Return NULL if var is unknown in the environment.
linexprGetCoeff :: Linexpr1 -> VarName -> Abstract Coeff
linexprGetCoeff e v = do
  var <- getVar v
  liftIO $ apLinexpr1CoeffrefWrapper e var

-- Setters

-- | Set the linear expression to a constant or interval of constants.
linexprSetConstant :: Linexpr1 -> Value -> Abstract ()
linexprSetConstant e v = do
  c <- coeffMake v
  liftIO $ apLinexpr1SetCstWrapper e c

-- | Set the coefficient of variables var in the expression.
-- Return true if any var is unknown in the environment.
linexprSetCoeffs :: Linexpr1 -> [(VarName, Value)] -> Abstract Bool
linexprSetCoeffs e vs = do
  succs <- mapM (uncurry $ linexprSetCoeff e) vs
  return $ or succs

-- | Set the coefficient of variable var in the expression.
-- Return true if var is unknown in the environment.
linexprSetCoeff :: Linexpr1 -> VarName -> Value -> Abstract Bool
linexprSetCoeff e name v = do
  c <- coeffMake v
  var <- getVar name
  liftIO $ apLinexpr1SetCoeffWrapper e var c