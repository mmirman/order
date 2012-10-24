{-# LANGUAGE 
 MultiParamTypeClasses,
 Rank2Types,
 DataKinds,
 KindSignatures,
 ConstraintKinds,
 FlexibleInstances,
 FunctionalDependencies,
 FlexibleContexts
 #-}
module CategoryTheory where

import Control.Monad ((>=>))

class Category obj arr | arr -> obj where 
  one :: obj a => arr a a
  (**) :: (obj c, obj a, obj b) =>  arr b c -> arr a b -> arr a c  

class Category obj arr => Product obj arr a b c | obj arr a b -> c where
  piL :: (obj c , obj a) => arr c a 
  piR :: (obj c , obj b) => arr c b
  productUMP :: forall z . (obj c , obj a , obj b , obj z ) => arr z a -> arr z b -> arr z c
  -- (productUMP pi1' pi2') . pi1 == pi1'
  -- (productUMP pi1' pi2') . pi2 == pi2'
  
class Category obj arr => Coproduct obj arr a b c | obj arr a b -> c where
  inL :: (obj c , obj a) => arr a c
  inR :: (obj c , obj b) => arr b c
  coproductUMP :: forall z . (obj c , obj a , obj b , obj z) => arr a z -> arr b z -> arr c z
  -- inL . (coproductUMP inL' inR')  == inL'
  -- inR . (coproductUMP inL' inR')  == inR'

class Types a -- Sets
instance Types a -- definition of sets.

instance Category Types (->) where
  one = id
  (**) = (.)

instance Product Types (->) a b (a,b) where
  piL = fst
  piR = snd
  productUMP fZA fZB z = (fZA z, fZB z)
  
instance Coproduct Types (->) a b (Either a b) where
  inL = Left
  inR = Right
  coproductUMP fAZ fBZ eAB = case eAB of
    Left a -> fAZ a
    Right b -> fBZ b
    
data Monadic a b = Monadic { mo :: forall m . Monad m => a -> m b }

instance Category Types Monadic where
  one = Monadic return
  (**) (Monadic a) (Monadic b) = Monadic $ (b >=> a)
