-- | This package defines many abstract machines, so we define a type
-- to work with them.
module LAM.IsLAM (IsLAM(..), runTrace, evalPrint, evalHnf) where

-- | A record that holds initialization and step functions for an
-- abstract machine.
data IsLAM m e s t = IsLAM { step :: s -> m (Either e s), initS :: t -> s }

-- | Run the abstract machine and return the terminal state.
run :: Monad m => IsLAM m e s t -> s -> m s
run l@(IsLAM step _) s = do
  t <- step s
  case t of
    (Left _)   -> return s
    (Right s') -> run l s'

-- | Run the abstract machine and return a trace of the whole
-- execution.
runTrace :: Monad m => IsLAM m e s t -> t -> m [s]
runTrace l = runTrace' l . initS l
  where
    runTrace' :: Monad m => IsLAM m e s t -> s -> m [s]
    runTrace' l@(IsLAM step _) s = do
      s' <- step s
      case s' of
        (Left _)    -> return []
        (Right s'') -> (s :) <$> runTrace' l s''

-- | Run the abstract machine and print the final state.
evalPrint :: Show s => IsLAM IO e s t -> t -> IO ()
evalPrint l t = run l (initS l t) >>= print

-- | Run the abstract machine and convert the final state back to a
-- term using the supplied conversion function.
evalHnf :: Monad m => IsLAM m e s t -> (s -> m t) -> t -> m t
evalHnf l conv t = run l (initS l t) >>= conv
