-- | This package defines many abstract machines, so we define a type
-- to work with them.
module LAM.IsLAM (IsLAM(..), runTrace, runTraceFinite, evalPrint, evalHnf) where

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

runTrace' :: Monad m => Maybe Word -> IsLAM m e s t -> t -> m [s]
runTrace' x l = go x l . initS l
  where
    go :: Monad m => Maybe Word -> IsLAM m e s t -> s -> m [s]
    go (Just 0) _                s = return []
    go x        l@(IsLAM step _) s = do
      s' <- step s
      case s' of
        (Left _)    -> return []
        (Right s'') -> (s :) <$> go ((\y -> y - 1) <$> x) l s''

-- | Run the abstract machine to the final state and return a trace of
-- the whole execution.
runTrace :: Monad m => IsLAM m e s t -> t -> m [s]
runTrace = runTrace' Nothing

-- | Run the abstract machine a given number of steps and return a
-- trace of the whole execution.
runTraceFinite :: Monad m => Word -> IsLAM m e s t -> t -> m [s]
runTraceFinite = runTrace' . Just

-- | Run the abstract machine and print the final state.
evalPrint :: Show s => IsLAM IO e s t -> t -> IO ()
evalPrint l t = run l (initS l t) >>= print

-- | Run the abstract machine and convert the final state back to a
-- term using the supplied conversion function.
evalHnf :: Monad m => IsLAM m e s t -> (s -> m t) -> t -> m t
evalHnf l conv t = run l (initS l t) >>= conv
