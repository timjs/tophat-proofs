module Control.Monad.Supply

%default total

||| A computation which has access to freshly generated data
public export
interface Monad m => MonadSupply supplyType m | m where
  supply : m supplyType
