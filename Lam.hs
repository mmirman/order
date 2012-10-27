{-# LANGUAGE
 KindSignatures,
 TypeOperators,
 RankNTypes,
 UndecidableInstances, 
 DataKinds,
 TypeFamilies
 #-}
module Lam where

infixr 0 :->
infixr 0 :+
data Tp = Tp :-> Tp | Unit deriving Eq
data InC = F Tp | U deriving Eq
data C = InC :+ C | End

type family IfEq (a :: Tp) (a' :: Tp) (f :: C) (s :: C) :: C 
type instance IfEq Unit Unit f s = f
type instance IfEq (a :-> b) Unit f s = s
type instance IfEq Unit (a :-> b) f s = s
type instance IfEq (a :-> b) (a' :-> b') f s = IfEq a a' (IfEq b b' f s) s

type family Use (a :: Tp) (b :: C) :: C
type instance Use a (F a':+ h) = IfEq a a' (U :+ h) (F a' :+ (Use a h))
type instance Use a (U :+ h) = U :+ (Use a h)

class Semantics (rep :: C -> C -> Tp -> *) where
  app :: rep hi h (a :-> b) -> rep h ho a -> rep hi ho b
  nil :: rep hi hi Unit
  lam :: ((forall h . rep h (Use a h) a) -> rep (F a :+ hi) (U :+ ho) b) 
         -> rep hi ho (a :-> b)
    
data LL a = LL { runLam :: forall rep. Semantics rep => rep End End a}

test :: LL ((Unit :-> Unit) :-> Unit :-> Unit)
test = LL $ lam $ \f -> lam $ \y -> app f y
