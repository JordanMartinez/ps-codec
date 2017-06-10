module Control.Monad.Codec where

import Prelude

import Control.Alternative (class Alt, class Alternative, class Plus, empty, (<|>))
import Control.Monad.Reader (ReaderT(..), ask, runReaderT, mapReaderT)
import Control.Monad.Writer (Writer, writer, execWriter, runWriter)
import Control.Monad.Trans.Class (lift)
import Data.Functor.Invariant (class Invariant, imapF)
import Data.Profunctor (class Profunctor, lmap)
import Data.Tuple (Tuple(..))

-- | A general type for codecs.
data GCodec m n a b = GCodec (m b) (a -> n b)

instance functorGCodec :: (Functor m, Functor n) => Functor (GCodec m n a) where
  map f (GCodec dec enc) =
    GCodec (map f dec) (map f <$> enc)

instance invariantGCodec :: (Functor m, Functor n) => Invariant (GCodec m n a) where
  imap = imapF

instance applyGCodec :: (Apply m, Apply n) => Apply (GCodec m n a) where
  apply (GCodec decf encf) (GCodec decx encx) =
    GCodec (decf <*> decx) (\c -> encf c <*> encx c)

instance applicativeGCodec :: (Applicative m, Applicative n) => Applicative (GCodec m n a) where
  pure x = GCodec (pure x) (const (pure x))

instance bindGCodec :: (Bind m, Bind n) => Bind (GCodec m n a) where
  bind (GCodec dec enc) f =
    GCodec
      (dec >>= \x -> case f x of GCodec dec' _ -> dec')
      (\c -> enc c >>= \x -> case f x of GCodec _ enc' -> enc' c)

instance monadGCodec :: (Monad m, Monad n) => Monad (GCodec m n a)

instance profunctorGCodec :: (Functor m, Functor n) => Profunctor (GCodec m n) where
  dimap f g (GCodec dec enc) = GCodec (map g dec) (map g <<< enc <<< f)

instance altGCodec :: (Alt m, Alt n) => Alt (GCodec m n a) where
  alt (GCodec decx encx) (GCodec decy ency) =
    GCodec (decx <|> decy) (\a -> encx a <|> ency a)

instance plusGCodec :: (Plus m, Plus n) => Plus (GCodec m n a) where
  empty = GCodec empty (const empty)

instance alternativeGCodec :: (Alternative m, Alternative n) => Alternative (GCodec m n a)

-- | Extracts the decoder part of a `GCodec`
decoder :: forall m n a b. GCodec m n a b -> m b
decoder (GCodec f _) = f

-- | Extracts the encoder part of a `GCodec`
encoder :: forall m n a b. GCodec m n a b -> a -> n b
encoder (GCodec _ f) = f

-- | Changes the `m` and `n` functors used in the codec using the specified
-- | natural transformations.
bihoistGCodec
  :: forall m m' n n' a b
   . (m ~> m')
  -> (n ~> n')
  -> GCodec m n a b
  -> GCodec m' n' a b
bihoistGCodec f g (GCodec dec enc) = GCodec (f dec) (map g enc)

-- | `GCodec` is defined as a `Profunctor` so that `lmap` can be used to target
-- | specific fields when defining a codec for a product type. This operator
-- | is a convenience for that:
-- |
-- | ``` purescript
-- | tupleCodec =
-- |   Tuple
-- |     <$> fst ~ fstCodec
-- |     <*> snd ~ sndCodec
-- | ```
infixl 5 lmap as ~

type Codec m a b c d = GCodec (ReaderT a m) (Writer b) c d

decode :: forall m a b c d. Codec m a b c d -> a -> m d
decode = runReaderT <<< decoder

encode :: forall m a b c d. Codec m a b c d -> c -> b
encode codec = execWriter <<< encoder codec

composeCodec
  :: forall a d f b e c m
   . Bind m
  => Codec m d c e f
  -> Codec m a b c d
  -> Codec m a b e f
composeCodec (GCodec decf encf) (GCodec decg encg) =
  GCodec
    (ReaderT \x -> runReaderT decf =<< runReaderT decg x)
    (\c ->
      let (Tuple w x) = runWriter (encf c)
      in writer $ Tuple w (execWriter (encg x)))

hoistCodec
  :: forall m m' a b c d
   . (m ~> m')
  -> Codec m a b c d
  -> Codec m' a b c d
hoistCodec f = bihoistGCodec (mapReaderT f) id

type BasicCodec m a b = Codec m a a b b

basicCodec
  :: forall m a b
   . Monad m
  => (a -> m b)
  -> (b -> a)
  -> BasicCodec m a b
basicCodec f g =
  GCodec
    (lift <<< f =<< ask)
    (\x -> writer $ Tuple x (g x))
