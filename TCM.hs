module TCM
    ( TCM(..)
    , liftTCM2, liftTCM2'
    , ask, askIndex, askCtx, local
    , liftEDocM, errorTCM
    ) where

import qualified Data.Map as M

import ErrorDoc
import Syntax.Term
import Value

newtype TCM a = TCM { runTCM :: DBIndex -> [String] -> M.Map String DBIndex -> Ctx -> EDocM a }

instance Functor TCM where
    fmap f (TCM m) = TCM $ \a b c d -> fmap f (m a b c d)

instance Monad TCM where
    return x = TCM $ \_ _ _ _ -> return x
    TCM f >>= k = TCM $ \a b c d -> f a b c d >>= \r -> runTCM (k r) a b c d

liftTCM2' :: (a -> b -> c) -> TCM a -> TCM b -> TCM c
liftTCM2' f (TCM m1) (TCM m2) = TCM $ \a b c d -> liftErr2 f (m1 a b c d) (m2 a b c d)

liftTCM2 :: (a -> b -> TCM c) -> TCM a -> TCM b -> TCM c
liftTCM2 f m1 m2 = do
    (r1,r2) <- liftTCM2' (,) m1 m2
    f r1 r2

ask :: TCM (DBIndex, [String], M.Map String DBIndex, Ctx)
ask = TCM $ \a b c d -> return (a, b, c, d)

askIndex :: TCM DBIndex
askIndex = TCM $ \a _ _ _ -> return a

askCtx :: TCM Ctx
askCtx = TCM $ \_ _ _ -> return

local :: (DBIndex -> [String] -> M.Map String DBIndex -> Ctx -> (DBIndex, [String], M.Map String DBIndex, Ctx))
    -> TCM a -> TCM a
local f (TCM m) = TCM $ \a b c d ->
    let (a',b',c',d') = f a b c d
    in m a' b' c' d'

liftEDocM :: EDocM a -> TCM a
liftEDocM m = TCM $ \_ _ _ _ -> m

errorTCM :: EMsg -> TCM a
errorTCM e = liftEDocM $ Left [e]
