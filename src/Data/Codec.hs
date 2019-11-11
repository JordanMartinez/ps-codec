{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE UnicodeSyntax #-}
{-# LANGUAGE TypeOperators #-}
module Data.Codec
  ( GCodec(..)
  , decoder
  , encoder
  , bihoistGCodec
  , Codec
  , decode
  , encode
  , mapCodec
  , composeCodec
  , (<~<)
  , composeCodecFlipped
  , (>~>)
  , hoistCodec
  , BasicCodec
  , basicCodec
  ) where

-- import Prelude
import Control.Applicative (Applicative, pure, (<*>))
import Data.Function (($), flip)
-- See 'import Control.Monad' line

-- import Control.Alternative (Alt, Alternative, Plus, empty, (<|>))
import Control.Applicative (Alternative, (<|>), empty)
import Data.Functor.Plus (Plus, zero)
import Data.Functor.Alt (Alt, (<!>))
-- import Control.Monad.Reader (ReaderT(..), mapReaderT, runReaderT)
-- import Control.Monad.Writer (Writer, writer, execWriter, runWriter)
import Control.Monad.Reader (ReaderT(..), mapReaderT, runReaderT)
import Control.Monad.Trans.Writer.Strict (Writer, writer, execWriter, runWriter)
-- import Control.MonadPlus (class MonadPlus)
-- import Control.MonadZero (class MonadZero)
import Control.Monad (Functor, fmap, Monad, (>>=), return, (=<<), MonadPlus)
-- import Data.Functor.Invariant (class Invariant, imapF)
-- invmapFunctor in Haskell is iMapF in PureScript
import Data.Functor.Invariant (Invariant, invmap, invmapFunctor)
-- import Data.Newtype (un)
-- Decided to use `unStar` since Star doesn't have a Newtype instance
-- import Data.Profunctor (class Profunctor, dimap, lcmap)
-- import Data.Profunctor.Star (Star(..))
import Data.Profunctor (Profunctor, dimap, Star(..))
-- import Data.Tuple (Tuple(..))
import Data.Functor.Apply as Apply ((<.>), Apply)
import Data.Functor.Bind as Bind ((>>-), Bind)
import Control.Category as C
import Data.Semigroupoid (Semigroupoid, o)
import Control.Natural (type (~>))

-- -- | A general type for codecs.
-- data GCodec m n a b = GCodec (m b) (Star n a b)
-- | A general type for codecs.
data GCodec m n a b = GCodec (m b) (Star n a b)

-- instance functorGCodec ∷ (Functor m, Functor n) ⇒ Functor (GCodec m n a) where
--   map f (GCodec dec enc) =
--     GCodec (map f dec) (map f enc)
instance (Functor m, Functor n) ⇒ Functor (GCodec m n a) where
  fmap f (GCodec dec enc) =
    GCodec (fmap f dec) (fmap f enc)

-- instance invariantGCodec ∷ (Functor m, Functor n) ⇒ Invariant (GCodec m n a) where
--   imap = imapF
instance (Functor m, Functor n) ⇒ Invariant (GCodec m n a) where
  invmap = invmapFunctor

-- instance applyGCodec ∷ (Apply m, Apply n) ⇒ Apply (GCodec m n a) where
--   apply (GCodec decf encf) (GCodec decx encx) =
--     GCodec (decf <*> decx) (encf <*> encx)

instance (Apply.Apply m, Apply.Apply n) ⇒ Apply.Apply (GCodec m n a) where
  (<.>) (GCodec decf encf) (GCodec decx encx) =
    GCodec (decf <.> decx) (encf `starApply` encx)
    where
      starApply (Star x) (Star y) = Star (\a -> x a <.> y a)

-- instance applicativeGCodec ∷ (Applicative m, Applicative n) ⇒ Applicative (GCodec m n a) where
--   pure x =
--     GCodec (pure x) (pure x)

instance (Applicative m, Applicative n) ⇒ Applicative (GCodec m n a) where
  pure x =
    GCodec (pure x) (pure x)

  (<*>) (GCodec decf encf) (GCodec decx encx) =
    GCodec (decf <*> decx) (encf <*> encx)

-- instance bindGCodec ∷ (Bind m, Bind n) ⇒ Bind (GCodec m n a) where
--   bind (GCodec dec enc) f =
--     GCodec (dec >>= f >>> decoder) (enc >>= f >>> encoder)

instance (Bind.Bind m, Bind.Bind n) ⇒ Bind.Bind (GCodec m n a) where
  (>>-) (GCodec dec enc) f =
    GCodec (dec >>- (f C.>>> decoder)) (enc `starBind` (f C.>>> encoder))
    where
      starBind (Star m) f' = Star
        \x -> m x >>- \a -> case f' a of Star g -> g x

-- instance monadGCodec ∷ (Monad m, Monad n) ⇒ Monad (GCodec m n a)

instance (Monad m, Monad n) ⇒ Monad (GCodec m n a) where
  (>>=) (GCodec dec enc) f =
    GCodec (dec >>= (f C.>>> decoder)) (enc >>= (f C.>>> encoder))

  return = pure

-- instance profunctorGCodec ∷ (Functor m, Functor n) ⇒ Profunctor (GCodec m n) where
--   dimap f g (GCodec dec enc) =
--     GCodec (map g dec) (dimap f g enc)

instance (Functor m, Functor n) ⇒ Profunctor (GCodec m n) where
  dimap f g (GCodec dec enc) =
    GCodec (fmap g dec) (dimap f g enc)

-- instance altGCodec ∷ (Alt m, Alt n) ⇒ Alt (GCodec m n a) where
--   alt (GCodec decx encx) (GCodec decy ency) =
--     GCodec (decx <|> decy) (encx <|> ency)

instance (Alt m, Alt n) ⇒ Alt (GCodec m n a) where
  (<!>) (GCodec decx encx) (GCodec decy ency) =
    GCodec (decx <!> decy) (encx `starAlt` ency)
    where
      starAlt (Star f) (Star g) = Star (\a -> f a <!> g a)

-- instance plusGCodec ∷ (Plus m, Plus n) ⇒ Plus (GCodec m n a) where
--   empty = GCodec empty empty

instance (Plus m, Plus n) ⇒ Plus (GCodec m n a) where
  zero = GCodec zero (Star \_ -> zero)

-- instance alternativeGCodec ∷ (Alternative m, Alternative n) ⇒ Alternative (GCodec m n a)

instance (Alternative m, Alternative n) ⇒ Alternative (GCodec m n a) where
  (<|>) (GCodec decx encx) (GCodec decy ency) =
    GCodec (decx <|> decy) (encx <|> ency)

  empty = GCodec empty empty

-- instance monadZeroGCodec ∷ (MonadZero m, MonadZero n) ⇒ MonadZero (GCodec m n a)
-- instance monadPlusGCodec ∷ (MonadPlus m, MonadPlus n) ⇒ MonadPlus (GCodec m n a)
instance (MonadPlus m, MonadPlus n) ⇒ MonadPlus (GCodec m n a)

-- instance semigroupoidGCodec ∷ Bind n ⇒ Semigroupoid (GCodec m n) where
--   compose (GCodec decx encx) (GCodec decy ency) =
--     GCodec decx (compose encx ency)

instance Monad n ⇒ Semigroupoid (GCodec m n) where
  o (GCodec decx encx) (GCodec _ ency) =
    GCodec decx (encx C.<<< ency)

-- | Extracts the decoder part of a `GCodec`
decoder ∷ ∀ m n a b. GCodec m n a b → m b
decoder (GCodec f _) = f

-- | Extracts the encoder part of a `GCodec`
encoder ∷ ∀ m n a b. GCodec m n a b → Star n a b
encoder (GCodec _ f) = f

-- | Changes the `m` and `n` functors used in the codec using the specified
-- | natural transformations.
bihoistGCodec
  ∷ ∀ m m' n n' a b
   . (m ~> m')
  → (n ~> n')
  → GCodec m n a b
  → GCodec m' n' a b
-- bihoistGCodec f g (GCodec dec (Star h)) = GCodec (f dec) (Star (g <<< h))
bihoistGCodec f g (GCodec dec (Star h)) = GCodec (f dec) (Star (g C.<<< h))

-- | `GCodec` is defined as a `Profunctor` so that `lmap` can be used to target
-- | specific fields when defining a codec for a product type. This operator
-- | is a convenience for that:
-- |
-- | ```haskell
-- | tupleCodec =
-- |   (,)
-- |     <$> fst ~ fstCodec
-- |     <*> snd ~ sndCodec
-- | ```
-- (~) ∷ Profunctor p => (a -> b) -> p b c -> p a c
-- (~) = lmap
-- infixl 5 ~

type Codec m a b c d = GCodec (ReaderT a m) (Writer b) c d

decode ∷ ∀ m a b c d. Codec m a b c d → a → m d
-- decode = runReaderT <<< decoder
decode = runReaderT C.<<< decoder

encode ∷ ∀ m a b c d. Codec m a b c d → c → b
-- encode codec = execWriter <<< un Star (encoder codec)
encode codec = execWriter C.<<< unStar (encoder codec)

mapCodec
  ∷ ∀ m a b c d
  -- . Bind m -- PureScript version
  . Monad m
  ⇒ (a → m b)
  → (b → a)
  → Codec m c d a a
  → Codec m c d b b
mapCodec f g (GCodec decf encf) = GCodec dec enc
  where
  dec = ReaderT \x → f =<< runReaderT decf x
  enc = Star \a →
    let (_, x) = runWriter (unStar encf (g a))
    in writer (a, x)

composeCodec
  ∷ ∀ a d f b e c m
  -- . Bind m -- PureScript version
  . Monad m
  ⇒ Codec m d c e f
  → Codec m a b c d
  → Codec m a b e f
composeCodec (GCodec decf encf) (GCodec decg encg) =
  GCodec
    (ReaderT \x → runReaderT decf =<< runReaderT decg x)
    (Star \c →
      let (w, x) = runWriter (unStar encf c)
      in writer $ (w, (execWriter (unStar encg x))))

(<~<) ∷ ∀ a d f b e c m
      . Monad m
      ⇒ Codec m d c e f
      → Codec m a b c d
      → Codec m a b e f
(<~<) = composeCodec

infixr 8 <~<

composeCodecFlipped
  ∷ ∀ a d f b e c m
  -- . Bind m -- PureScript version
  . Monad m
  ⇒ Codec m a b c d
  → Codec m d c e f
  → Codec m a b e f
composeCodecFlipped = flip composeCodec

(>~>)
  ∷ ∀ a d f b e c m
  . Monad m
  ⇒ Codec m a b c d
  → Codec m d c e f
  → Codec m a b e f
(>~>) = composeCodecFlipped
infixr 8 >~>

hoistCodec ∷ ∀ m m' a b c d. (m ~> m') → Codec m a b c d → Codec m' a b c d
-- hoistCodec f = bihoistGCodec (mapReaderT f) identity
hoistCodec f = bihoistGCodec (mapReaderT f) C.id

type BasicCodec m a b = Codec m a a b b

basicCodec ∷ ∀ m a b. (a → m b) → (b → a) → BasicCodec m a b
-- basicCodec f g = GCodec (ReaderT f) (Star \x → writer $ Tuple x (g x))
basicCodec f g = GCodec (ReaderT f) (Star \x → writer (x, (g x)))

-- Deal with Star not having a Newtype instance
unStar :: ∀ f d c. Star f d c -> (d -> f c)
unStar (Star f) = f
