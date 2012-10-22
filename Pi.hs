{-# LANGUAGE 
 Rank2Types, 
 TypeFamilies, 
 FlexibleInstances, 
 GADTs, 
 TypeOperators,
 DataKinds
 #-}
module Pi where
import Control.Applicative
import Control.Concurrent
import Prelude hiding ((*),(+))

class Embedable p where
  embed :: IO () -> p

class Embedable p => PiSemantics p where
  type Name p :: *
  new :: (Name p -> p) -> p     
  out :: Name p -> Name p -> p -> p
  (|||) :: p -> p -> p
  inn :: Name p -> (Name p -> p) -> p
  rep :: p -> p
  nil :: p
  
  (?) :: p -> p -> p
  
newtype Nu f = Nu { nu :: f (Nu f)}   

fork :: IO () -> IO ()
fork a = forkIO a >> return ()

forever :: IO a -> IO a
forever p = fo where fo = p >> fo

say :: PiSemantics p => String -> p 
say s = embed $ putStr s

instance Embedable (IO ()) where
  embed = id
instance PiSemantics (IO ()) where
  type Name (IO ()) = Nu Chan
  new f = Nu <$> newChan >>= f
  a ||| b = forkIO a >> fork b
  inn (Nu x) f = readChan x >>= fork . f
  out (Nu x) y b = writeChan x y >> b
  rep = forever
  nil = return ()  


newtype Pi = Pi { runPi :: forall a . PiSemantics a => a }

example = Pi (new $ \z -> (new $ \x -> (out x z nil ||| say "hi\n")
                                   ||| (inn x $ \y -> out y x nil ||| (inn x $ \y -> say "he\n"))) 
               ||| inn z (\v -> out v v nil ||| say "ho\n"))

newtype Pretty = Pretty { runPretty :: [String] -> Int -> ShowS }

instance Embedable Pretty where
  embed io = Pretty $ \_ _ -> showString "{IO}"
instance PiSemantics Pretty where
     type Name Pretty = String
     new f = Pretty $ \(v:vs) n ->
         showParen (n > 10) $
             showString "nu " . showString v . showString ". " .
             runPretty (f v) vs 10
     out x y b = Pretty $ \vs n ->
         showParen (n > 10) $
             showString x . showChar '<' . showString y . showString ">" .
             runPretty b vs 10 
     inn x f = Pretty $ \(v:vs) n ->
         showParen (n > 10) $
             showString x . showChar '(' . showString v . showString ")." .
             runPretty (f v) vs 10
     p ||| q = Pretty $ \vs n ->
         showParen (n > 4) $
             runPretty p vs 5 .
             showString " | " .
             runPretty q vs 4
     rep p = Pretty $ \vs n ->
         showParen (n > 10) $
             showString "!" .
             runPretty p vs 10
     nil = Pretty $ \_ _ -> showChar '0'

instance Show Pi where
     showsPrec n (Pi p) = runPretty p vars n
         where
             vars = fmap return vs ++
                    [i : show j | j <- [1..], i <- vs] where
             vs = ['a'..'z']

type NuChan = Nu Chan
          
run :: Pi -> IO ()
run (Pi p) = p
         
type Nm = Integer

data PTm = New (Nm -> PTm)
          | Out Nm Nm PTm
          | In Nm (Nm -> PTm)
          | Nil
          | Rep PTm
          | PTm :|: PTm
          | Forward Nm Nm
          | Embed (IO ())

instance Embedable PTm where
  embed = Embed
instance PiSemantics PTm where
  type Name PTm = Integer
  new = New 
  (|||) = (:|:)
  out = Out
  inn = In
  rep = Rep
  nil = Nil
  

class Embedable p => LLSemantics p where
  lam :: (p -> p) -> p
  (#) :: p -> p -> p
  bang :: p -> p
  letBang :: p -> (p -> p) -> p
  
  (*) :: p -> p -> p
  lett :: p -> (p -> p -> p) -> p
  
  inLeft :: p -> p
  inRight :: p -> p
  caseOf :: p -> (p -> p) -> (p -> p) -> p
  
  (&) :: p -> p -> p
  getLeft  :: p -> p
  getRight :: p -> p
  
data LinLam = LinLam {runLinLam :: forall a . LLSemantics a => a }
{-
instance LLSemantics (IO ()) where
  lam f = -}