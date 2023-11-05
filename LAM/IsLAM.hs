module LAM.IsLAM where

data IsLAM m e s t = IsLAM { step :: s -> m (Either e s), initS :: t -> s }

step' :: Monad m => IsLAM m e s t -> s -> m s
step' l@(IsLAM step _) s = do
  s' <- step s
  case s' of
    (Left _)    -> return s
    (Right s'') -> step' l s''

runTrace :: Monad m => IsLAM m e s t -> s -> m [s]
runTrace l@(IsLAM step _) s = do
  s' <- step s
  case s' of
    (Left _)    -> return []
    (Right s'') -> (s :) <$> runTrace l s''

run :: Monad m => IsLAM m e s t -> s -> m s
run l@(IsLAM step _) s = do
  t <- step s
  case t of
    (Left _)   -> return s
    (Right s') -> run l s'

runTrace' :: Monad m => IsLAM m e s t -> t -> m [s]
runTrace' l = runTrace l . initS l

evalPrint :: Show s => IsLAM IO e s t -> t -> IO ()
evalPrint l@(IsLAM _ initS) t = step' l (initS t) >>= print

evalHnf :: Monad m => IsLAM m e s t -> (s -> m t) -> t -> m t
evalHnf l conv t = run l (initS l t) >>= conv
