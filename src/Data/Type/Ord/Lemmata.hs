
-- --< Header >-- {{{

{-# LANGUAGE GADTs, FlexibleContexts #-}


{- |

Description : Lemmata for easier use of "Data.Type.Ord"
Copyright   : (c) L. S. Leary, 2025

Lemmata for easier use of "Data.Type.Ord".

\(\newcommand{\ldot}{.\,\,}\)

-}

-- }}}

-- --< Exports >-- {{{

module Data.Type.Ord.Lemmata (

  -- * Equivalence
  symEq,
  symNeq,
  transEq,

  -- * Ordering

  -- ** Reflection
  leqToGeq,
  geqToLeq,

  -- ** Transitivity
  transLt,
  transGt,
  transGeq,

  -- ** Properties of Min
  minDefl1,
  minDefl2,
  minMono,
  minSym,

  -- ** Properties of Max
  maxInfl1,
  maxInfl2,
  maxMono,
  maxSym,

) where

-- }}}

-- --< Imports >-- {{{

-- base
import Data.Type.Equality ((:~:)(..))
import Data.Type.Ord (OrderingI(..), Min, Max)

-- ord-axiomata
import Data.Type.Ord.Relations
import Data.Type.Ord.Axiomata

-- }}}

-- --< Equivalence >-- {{{

{- |

Symmetry of equivalence.

\[
  \forall a, b \ldot
    a = b \iff b = a
\]

-}
symEq
  :: (Equivalence e, a == b)
  => Sing e a -> Sing e b {- ^ -}
  -> Proof (b == a)
symEq a b = case sub a b of
  Refl -> QED

{- |

Symmetry of inequivalence.

\[
  \forall a, b \ldot
    a \neq b \iff b \neq a
\]

-}
symNeq
  :: (TotalOrder e, a /= b)
  => Sing e a -> Sing e b {- ^ -}
  -> Proof (b /= a)
symNeq a b = case antiSym b a of
  Refl -> case a <|=|> b of
    LTI -> QED
    GTI -> QED

{- |

Transitivity of equivalence.

\[
  \forall a, b, c \ldot
    a = b \land b = c \implies a = c
\]

-}
transEq
  :: (Equivalence e, a == b, b == c)
  => Sing e a -> Sing e b -> Sing e c {- ^ -}
  -> Proof (a == c)
transEq a b c = case sub a b of
  Refl -> case sub b c of
    Refl -> QED

-- }}}

-- --< Ordering: Reflection >-- {{{

{- |

Anti-symmetry of \( \leq \) and \( \geq \).

\[
  \forall a, b \ldot
    a \leq b \implies b \geq a
\]

-}
leqToGeq
  :: (TotalOrder o, a <= b)
  => Sing o a -> Sing o b
  -> Proof (b >= a)
leqToGeq a b = case antiSym b a of
  Refl -> case a <|=|> b of
    LTI -> QED
    EQI -> QED

{- |

Anti-symmetry of \( \geq \) and \( \leq \).

\[
  \forall a, b \ldot
    a \geq b \implies b \leq a
\]

-}
geqToLeq
  :: (TotalOrder o, a >= b)
  => Sing o a -> Sing o b
  -> Proof (b <= a)
geqToLeq a b = case antiSym b a of
  Refl -> case a <|=|> b of
    EQI -> QED
    GTI -> QED

-- }}}

-- --< Ordering: Transitivity >-- {{{

{- |

Transitivity of \( \lt \).

\[
  \forall a, b, c \ldot
    a \lt b \land b \lt c \implies a \lt c
\]

-}
transLt
  :: (TotalOrder o, a < b, b < c)
  => Sing o a -> Sing o b -> Sing o c {- ^ -}
  -> Proof (a < c)
transLt a b c = case transLeq a b c of
  QED -> case a <|=|> c of
    LTI -> QED
    EQI -> case antiSym a b of

{- |

Transitivity of \( \gt \).

\[
  \forall a, b, c \ldot
    a \gt b \land b \gt c \implies a \gt c
\]

-}
transGt
  :: (TotalOrder o, a > b, b > c)
  => Sing o a -> Sing o b -> Sing o c {- ^ -}
  -> Proof (a > c)
transGt a b c = case antiSym c b of
  Refl -> case antiSym b a of
    Refl -> case transLt c b a of
      QED -> case antiSym a c of
        Refl -> QED

{- |

Transitivity of \( \geq \).

\[
  \forall a, b, c \ldot
    a \geq b \land b \geq c \implies a \geq c
\]

-}
transGeq
  :: (TotalOrder o, a >= b, b >= c)
  => Sing o a -> Sing o b -> Sing o c {- ^ -}
  -> Proof (a >= c)
transGeq a b c = case geqToLeq b c of
  QED -> case geqToLeq a b of
    QED -> case transLeq c b a of
      QED -> case leqToGeq c a of
        QED -> QED

-- }}}

-- --< Ordering: Properties of Min >-- {{{

{- |

'Min' is deflationary in its first argument.

\[
  \forall a, b \ldot
    \mathrm{min} \, a \, b \leq a
\]

-}
minDefl1
  :: TotalOrder o
  => Sing o a -> Sing o b {- ^ -}
  -> Proof (Min a b <= a)
minDefl1 a b = case a <|=|> b of
  LTI -> case refl a of
    QED -> QED
  EQI -> QED
  GTI -> case antiSym b a of
    Refl -> QED

{- |

'Min' is deflationary in its second argument.

\[
  \forall a, b \ldot
    \mathrm{min} \, a \, b \leq b
\]

-}
minDefl2
  :: TotalOrder o
  => Sing o a -> Sing o b {- ^ -}
  -> Proof (Min a b <= b)
minDefl2 a b = case a <|=|> b of
  LTI -> case refl b of
    QED -> QED
  EQI -> QED
  GTI -> case refl b of
    QED -> QED

{- |

'Min' is monotonic in both arguments.

\[
  \forall a, b, c, d \ldot
    a \leq c \land b \leq d
      \implies \mathrm{min} \, a \, b \leq \mathrm{min} \, c \, d
\]

-}
minMono
  :: (TotalOrder o, a <= c, b <= d)
  => Sing o a -> Sing o b -> Sing o c -> Sing o d {- ^ -}
  -> Proof (Min a b <= Min c d)
minMono a b c d = case c <|=|> d of
  LTI -> case minDefl1 a b of
    QED -> transLeq (minTO a b) a c
  EQI -> case minDefl1 a b of
    QED -> transLeq (minTO a b) a c
  GTI -> case minDefl2 a b of
    QED -> transLeq (minTO a b) b d

{- |

'Min' is symmetric.

\[
  \forall a, b \ldot
    \mathrm{min} \, a \, b \sim \mathrm{min} \, b \, a
\]

-}
minSym
  :: TotalOrder o
  => Sing o a -> Sing o b {- ^ -}
  -> Min a b :~: Min b a
minSym a b = case antiSym b a of
  Refl -> case a <|=|> b of
    LTI -> Refl
    EQI -> Refl
    GTI -> Refl

-- }}}

-- --< Ordering: Properties of Max >-- {{{

{- |

'Max' is inflationary in its first argument.

\[
  \forall a, b \ldot
    a \leq \mathrm{max} \, a \, b
\]

-}
maxInfl1
  :: TotalOrder o
  => Sing o a -> Sing o b {- ^ -}
  -> Proof (a <= Max a b)
maxInfl1 a b = case a <|=|> b of
  LTI -> QED
  EQI -> QED
  GTI -> case refl a of
    QED -> QED

{- |

'Max' is inflationary in its second argument.

\[
  \forall a, b \ldot
    b \leq \mathrm{max} \, a \, b
\]

-}
maxInfl2
  :: TotalOrder o
  => Sing o a -> Sing o b {- ^ -}
  -> Proof (b <= Max a b)
maxInfl2 a b = case a <|=|> b of
  LTI -> case refl b of
    QED -> QED
  EQI -> QED
  GTI -> case antiSym b a of
    Refl -> QED

{- |

'Max' is monotonic in both arguments.

\[
  \forall a, b, c, d \ldot
    a \leq c \land b \leq d
      \implies \mathrm{max} \, a \, b \leq \mathrm{max} \, c \, d
\]

-}
maxMono
  :: (TotalOrder o, a <= c, b <= d)
  => Sing o a -> Sing o b -> Sing o c -> Sing o d {- ^ -}
  -> Proof (Max a b <= Max c d)
maxMono a b c d = case a <|=|> b of
  LTI -> case maxInfl2 c d of
    QED -> transLeq b d (maxTO c d)
  EQI -> case maxInfl2 c d of
    QED -> transLeq b d (maxTO c d)
  GTI -> case maxInfl1 c d of
    QED -> transLeq a c (maxTO c d)

{- |

'Max' is symmetric.

\[
  \forall a, b \ldot
    \mathrm{max} \, a \, b \sim \mathrm{max} \, b \, a
\]

-}
maxSym
  :: TotalOrder o
  => Sing o a -> Sing o b {- ^ -}
  -> Max a b :~: Max b a
maxSym a b = case antiSym b a of
  Refl -> case a <|=|> b of
    LTI -> Refl
    EQI -> Refl
    GTI -> Refl

-- }}}

