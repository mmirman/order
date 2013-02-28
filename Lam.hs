{-# LANGUAGE
 KindSignatures,
 TypeOperators,
 Rank2Types,
 UndecidableInstances, 
 DataKinds,
 TypeFamilies,
 GeneralizedNewtypeDeriving,
 GADTs
 #-}
module Lam where
import Control.Monad

import qualified Pi as Pi

infixr 0 :->
infixr 0 :+
data Tp = Top 
        | One
        | Zero
        | Bang Tp
        | Tp :-> Tp 
        | Tp :*: Tp
        | Tp :+: Tp
        | Tp :&: Tp
        | Forall (Tp -> Tp)

data Type (a :: Tp) where
  T_Top :: Type Top
  T_One :: Type One
  T_Zero :: Type Zero
  T_Bang :: Type a -> Type (Bang a)
  (::->) :: Type a -> Type b -> Type (a :-> b)
  (::*:) :: Type a -> Type b -> Type (a :*: b)
  (::&:) :: Type a -> Type b -> Type (a :&: b)
  (::+:) :: Type a -> Type b -> Type (a :+: b)
  T_Forall :: (forall a . Type a -> Type (f a)) -> Type (Forall f)

data InC = F Tp | U
data C = InC :+ C | End

data K = Bin String | Mon String | Un String deriving (Eq)
-- until the GHC gets proper pattern matching for type families, this output the cases for IfEq
produce :: IO ()
produce = do
  let tps = (map Bin [":+:", ":*:", ":&:", ":->"])++(map Mon ["Top", "One", "Zero"])++(map Un ["Bang"])
      pairs = [ (t,t') | t <- tps, t' <- filter (t /=) tps]
      
      display (Bin f) s = "(a"++s++" "++f++" b"++s++")"
      display (Un f) s = "("++f++" a"++s++")"
      display (Mon f) _ = f
  forM_ pairs $ \(t,t') -> 
    putStrLn $ "type instance IfEq "++display t ""++" "++display t' "'"++" f s = s"


type family IfEq (a :: Tp) (a' :: Tp) (f :: C) (s :: C) :: C 
type instance IfEq Top Top f s = f
type instance IfEq Zero Zero f s = f
type instance IfEq One One f s = f
type instance IfEq (a :-> b) (a' :-> b') f s = IfEq a a' (IfEq b b' f s) s
type instance IfEq (a :&: b) (a' :&: b') f s = IfEq a a' (IfEq b b' f s) s
type instance IfEq (a :+: b) (a' :+: b') f s = IfEq a a' (IfEq b b' f s) s
type instance IfEq (a :*: b) (a' :*: b') f s = IfEq a a' (IfEq b b' f s) s
type instance IfEq (a :+: b) (a' :*: b') f s = s
type instance IfEq (a :+: b) (a' :&: b') f s = s
type instance IfEq (a :+: b) (a' :-> b') f s = s
type instance IfEq (a :+: b) Top f s = s
type instance IfEq (a :+: b) One f s = s
type instance IfEq (a :+: b) Zero f s = s
type instance IfEq (a :+: b) (Bang a') f s = s
type instance IfEq (a :*: b) (a' :+: b') f s = s
type instance IfEq (a :*: b) (a' :&: b') f s = s
type instance IfEq (a :*: b) (a' :-> b') f s = s
type instance IfEq (a :*: b) Top f s = s
type instance IfEq (a :*: b) One f s = s
type instance IfEq (a :*: b) Zero f s = s
type instance IfEq (a :*: b) (Bang a') f s = s
type instance IfEq (a :&: b) (a' :+: b') f s = s
type instance IfEq (a :&: b) (a' :*: b') f s = s
type instance IfEq (a :&: b) (a' :-> b') f s = s
type instance IfEq (a :&: b) Top f s = s
type instance IfEq (a :&: b) One f s = s
type instance IfEq (a :&: b) Zero f s = s
type instance IfEq (a :&: b) (Bang a') f s = s
type instance IfEq (a :-> b) (a' :+: b') f s = s
type instance IfEq (a :-> b) (a' :*: b') f s = s
type instance IfEq (a :-> b) (a' :&: b') f s = s
type instance IfEq (a :-> b) Top f s = s
type instance IfEq (a :-> b) One f s = s
type instance IfEq (a :-> b) Zero f s = s
type instance IfEq (a :-> b) (Bang a') f s = s
type instance IfEq Top (a' :+: b') f s = s
type instance IfEq Top (a' :*: b') f s = s
type instance IfEq Top (a' :&: b') f s = s
type instance IfEq Top (a' :-> b') f s = s
type instance IfEq Top One f s = s
type instance IfEq Top Zero f s = s
type instance IfEq Top (Bang a') f s = s
type instance IfEq One (a' :+: b') f s = s
type instance IfEq One (a' :*: b') f s = s
type instance IfEq One (a' :&: b') f s = s
type instance IfEq One (a' :-> b') f s = s
type instance IfEq One Top f s = s
type instance IfEq One Zero f s = s
type instance IfEq One (Bang a') f s = s
type instance IfEq Zero (a' :+: b') f s = s
type instance IfEq Zero (a' :*: b') f s = s
type instance IfEq Zero (a' :&: b') f s = s
type instance IfEq Zero (a' :-> b') f s = s
type instance IfEq Zero Top f s = s
type instance IfEq Zero One f s = s
type instance IfEq Zero (Bang a') f s = s
type instance IfEq (Bang a) (a' :+: b') f s = s
type instance IfEq (Bang a) (a' :*: b') f s = s
type instance IfEq (Bang a) (a' :&: b') f s = s
type instance IfEq (Bang a) (a' :-> b') f s = s
type instance IfEq (Bang a) Top f s = s
type instance IfEq (Bang a) One f s = s
type instance IfEq (Bang a) Zero f s = s

type family Use (a :: Tp) (b :: C) :: C
type instance Use a (F a':+ h) = IfEq a a' (U :+ h) (F a' :+ (Use a h))
type instance Use a (U :+ h) = U :+ (Use a h)

class LinLam (rep :: C -> C -> Tp -> *) where
  (#) :: rep hi h (a :-> b) -> rep h ho a -> rep hi ho b
  zero :: rep hi hi Zero
  lam :: (rep h (Use a h) a -> rep (F a :+ hi) (U :+ ho) b) 
         -> rep hi ho (a :-> b)
    
  bang :: rep End End a -> rep End End (Bang a) 

  letBang :: rep hi h (Bang a)
          -> (rep h' h' a -> rep h ho b) 
          ->  rep hi ho b

  (*) :: rep hi h a 
      -> rep h ho b
      -> rep hi ho (a :*: b)

  lett :: rep hi h (a :*: b) 
       -> (rep h' (Use a h') a -> rep h'' (Use b h'') b -> rep (F a :+ F b :+ h) (U :+ U :+ ho) c)
       -> rep hi ho c
          
  embed :: IO () -> rep h h One
  
  inLeft :: rep hi ho a -> rep hi ho (a :+: b)
  inRight :: rep hi ho b -> rep hi ho (a :+: b)

  caseOf :: rep hi h (a :+: b) 
         -> (rep h' (Use a h') a -> rep (F a :+ h) (U :+ ho) c) 
         -> (rep h' (Use b h') b -> rep (F b :+ h) (U :+ ho) c) 
         -> rep hi ho c

  (&) :: rep hi ho a
      -> rep hi ho b
      -> rep hi ho (a :&: b)

  getLeft  :: rep hi ho (a :&: b)
           -> rep hi ho a
  getRight :: rep hi ho (a :&: b)
           -> rep hi ho b

  gen :: (forall a . rep hi ho (f a)) 
      -> Type (Forall f)
      -> rep hi ho (Forall f)
  (!) :: rep hi ho t
      -> Type t
      -> rep hi ho t
  (!>) :: rep hi ho (Forall f)
       -> Type a
       -> rep hi ho (f a)

  
newtype Fantom p (a :: C) (b :: C) (c :: Tp) = Fantom { toLL :: p } 

instance Pi.LLSemantics p => LinLam (Fantom p) where
  a # b = Fantom $ toLL a Pi.# toLL b
  zero = Fantom $ Pi.zero
  lam f = Fantom $ Pi.lam $ \x -> toLL $ f $ Fantom x
  bang p = Fantom $ Pi.bang $ toLL p
  letBang p f = Fantom $ Pi.letBang (toLL p) $ \x -> toLL $ f $ Fantom x
  a * b = Fantom $ toLL a Pi.* toLL b
  lett p f = Fantom $ Pi.lett (toLL p) $ \x y -> toLL $ f (Fantom x) (Fantom y)
  embed io = Fantom $ Pi.embed io
  
  inLeft p = Fantom $ Pi.inLeft $ toLL p
  inRight p = Fantom $ Pi.inRight $ toLL p
  caseOf p fL fR = Fantom $ Pi.caseOf (toLL p) (\x -> toLL $ fL (Fantom x)) (\x -> toLL $ fR (Fantom x))
  
  a & b = Fantom $ toLL a Pi.& toLL b
  getLeft p = Fantom $ Pi.getLeft $ toLL p
  getRight p = Fantom $ Pi.getRight $ toLL p

  a ! t = a
  
  
data LL a = LL { runLam :: forall rep. LinLam rep => rep End End a}

runLL :: LL Top -> IO ()
runLL s = Pi.new $ \n -> (toLL $ runLam s) n

test :: LL ((Top :-> Top) :-> Top :-> Top)
test = LL $ lam $ \f -> lam $ \y -> f # y

test2 :: LL ((Top :-> Top) :-> (Top :-> Top) :-> Top :-> Top)
test2 = LL $ lam $ \f -> lam $ \g -> lam $ \y -> g # (f # y)
