{-# LANGUAGE 
 Rank2Types, 
 TypeFamilies, 
 FlexibleInstances, 
 GADTs, 
 TypeOperators,
 DataKinds,
 UndecidableInstances
 #-}
module Pi where

import Control.Concurrent
import Prelude hiding ((*),(+))

class Embedable p where
  embed :: IO () -> p

class Embedable p => PiSemantics p where
  type Name p :: *
  forward :: Name p -> Name p -> p     
  new :: (Name p -> p) -> p     
  out :: Name p -> Name p -> p -> p
  (|||) :: p -> p -> p
  inn :: Name p -> (Name p -> p) -> p
  rep :: p -> p
  nil :: p
  
  piCase :: Name p -> (p, p) -> p
  piInL :: Name p -> p -> p
  piInR :: Name p -> p -> p
  
newtype Nu f = Nu { nu :: f (Nu f)}   

type MWrite a = MVar (a -> IO ())

data EChan a = ELeft {chan :: Chan a , write :: MWrite a} 
             | ERight {chan :: Chan a, write ::MWrite a }

fork :: IO () -> IO ()
fork a = forkIO a >> return ()

forever :: IO a -> IO a
forever p = fo where fo = p >> fo

say :: PiSemantics p => String -> p 
say s = embed $ putStr s

getChanel = chan . nu
newChanel l = do
  e <- newChan 
  m <- newMVar $ writeChan e
  return $ Nu $ l e m
writeChanel x y = withMVar (write (nu x)) ($ y)
readChanel = readChan . getChanel

instance Embedable (IO ()) where
  embed = id
instance PiSemantics (IO ()) where
  type Name (IO ()) = Nu EChan
  forward (Nu x) (Nu y) = do
    xw <- takeMVar $ write x
    yw <- takeMVar $ write y
    
    putMVar (write x) yw
    putMVar (write y) xw
  
  new f = newChanel ELeft >>= f
  a ||| b = forkIO a >> fork b
  inn x f = readChanel x >>= fork . f 
  out x y b = writeChanel x y >> b
  rep = forever
  nil = return ()  
  
  piCase x (p,q) = inn x $ \v -> case nu v of 
    ELeft _ _ -> p
    ERight _ _ -> q
  piInL x p = newChanel ELeft >>= (\y -> out x y p)
  piInR x p = newChanel ERight >>= (\y -> out x y p)
  
  
(?) :: PiSemantics p => p -> p -> Name p -> p
p ? q = \x -> new $ \y -> out x y $ p ||| q

getTensor :: PiSemantics p => Name p -> (Name p -> p) -> p
getTensor = inn

newtype Pi = Pi { runPi :: forall a . PiSemantics a => a }

example = Pi (new $ \z -> (new $ \x -> (out x z $ say "hi\n")
                                   ||| (inn x $ \y -> out y x $ inn x $ \_ -> say "he\n")) 
               ||| inn z (\v -> out v v $ say "ho\n"))

run :: Pi -> IO ()
run (Pi p) = p
         
type Nm = Integer

class Embedable p => LLSemantics p where
  lam :: (p -> p) -> p
  (#) :: p -> p ->  p
  bang :: p -> p
  letBang :: p -> (p -> p) ->  p
  
  (*) :: p -> p ->  p
  lett :: p -> (p -> p -> p) -> p
  
  inLeft :: p ->  p
  inRight :: p ->  p
  caseOf :: p -> (p ->  p) -> (p ->  p) ->  p
  
  (&) :: p -> p ->  p
  getLeft  :: p ->  p
  getRight :: p ->  p
  
  zero :: p

instance Embedable (Nu EChan -> IO ()) where
  embed a _ = a
  
var y = \y' -> forward y y'
instance LLSemantics (Nu EChan -> IO ()) where
  lam f x = inn x $ \y -> f (var y) x
  (#) m n w = new $ \x -> m x ||| (new $ \y -> out x y (n y ||| forward x w))
  
  bang m x = rep $ inn x $ \y -> m y
  letBang m n w = new $ \x -> m x ||| n (var x) w
  
  (*) m n x = new $ \y -> out x y $ m y ||| n x
  lett m n w = new $ \x -> m x ||| (inn x $ \y -> n (var y) (var x) w)
  
  (&) m n x = piCase x (m x, n x)
  getLeft m w = new $ \x -> m x ||| piInL x (forward x w)
  getRight m w = new $ \x -> m x ||| piInR x (forward x w)
  
  inLeft p x = piInL x (p x)
  inRight p x = piInR x (p x)
  caseOf p f f' z = new $ \x -> p x ||| piCase x (f (var z) x, f' (var z) x)
  
  zero _ = nil
data LinLam = LinLam { runLinLam :: forall a . LLSemantics a => a }
              
runLL :: LinLam -> IO ()
runLL (LinLam t) = new $ \n -> t n

  
{-  
 G |- P : A
---------------------
G |- inLeft P : A + B

 G |- E : A + B   G' , x : A |- F : C     G' , y : B |- F' : C
-------------------------------------------------------------
          G,G' |- caseOf E (\x.F) (\y.F') :: C

                             G', x:A |- P::z:C   G', x:B |- Q::z:C
                            ---------------------------------------
 G |- R :: x : A + B         G, x : A + B |- x.case(P,Q) :: z : C
-----------------------------------------------------------------
           G,G' |- #x.(R |x.case(P,Q) ) :: z : C


       G |- P :: x : A
  ---------------------------
  G |- x.inl; P :: x : A + B


-}