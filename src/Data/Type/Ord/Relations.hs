
-- --< Header >-- {{{

{-#
LANGUAGE
  GADTs, DataKinds, MultiParamTypeClasses, FlexibleInstances, FlexibleContexts
#-}

{- |

Description : Equivalence and order relations
Copyright   : (c) L. S. Leary, 2025

@'Compare' \@O@ should give rise to an equivalence relation and a total ordering on @O@.
In particular, we can define relations:

\[
\begin{align}
  a  <   b &\iff \mathtt{Compare} \, a \, b \sim \mathtt{LT} \\
  a  =   b &\iff \mathtt{Compare} \, a \, b \sim \mathtt{EQ} \\
  a  >   b &\iff \mathtt{Compare} \, a \, b \sim \mathtt{GT} \\
  a \leq b &\iff a < b \lor a = b                            \\
  a \neq b &\iff a < b \lor a > b                            \\
  a \geq b &\iff a = b \lor a > b
\end{align}
\]

These aren't consistent by construction, however—that's why we need axiomata.

N.B. We use and provide fixed versions of these relations from "Data.Type.Ord" as per [#26190](https://gitlab.haskell.org/ghc/ghc/-/issues/26190).

-}

-- }}}

-- --< Exports >-- {{{

module Data.Type.Ord.Relations (

  -- * Assert
  Assert,
  AssertEq,

  -- ** Precise Relations
  type (<),
  type (==),
  type (>),

  -- * Elem
  (:<),
  (:<<)(..),
  which,

  -- ** Imprecise Relations
  type (<=), ltOrEq,
  type (/=), ltOrGt,
  type (>=), gtOrEq,

) where

-- }}}

-- --< Imports >-- {{{

-- GHC/base
import GHC.TypeError (Unsatisfiable, ErrorMessage(..))

-- base
import Data.Kind (Type)
import Data.Type.Ord (Compare, OrdCond, type (<=?), type (>=?))

-- }}}

-- --< Assert >-- {{{

type Assert = AssertEq True

type AssertEq = AssertEq_

class a ~ b => AssertEq_ a b (msg :: ErrorMessage)

instance {-# OVERLAPPING  #-}                      AssertEq_ a a msg
instance {-# OVERLAPPABLE #-} Unsatisfiable msg => AssertEq_ a b msg

-- }}}

-- --< Precise Relations >-- {{{

type x <  y = AssertEq (Compare x y) LT (Msg x "<" y)
type x == y = AssertEq (Compare x y) EQ (Msg x "=" y)
type x >  y = AssertEq (Compare x y) GT (Msg x ">" y)

-- }}}

-- --< Elem >-- {{{

type (:<) = (~:<)
infix 4 :<

which :: p :< ps => p :<< ps
which = which_

data (:<<) :: k -> [k] -> Type where
  InZ ::               p :<< p:rs
  InS :: p :<< r:ss -> p :<< q:r:ss
infix 4 :<<

class p ~:< ps where
  which_ :: p :<< ps
infix 4 ~:<

instance {-# OVERLAPPING  #-}                          p ~:< p:ps where
  which_ = InZ
instance {-# OVERLAPPABLE #-} (ps ~ r:ss, p ~:< ps) => p ~:< q:ps where
  which_ = InS which_

-- }}}

-- --< Imprecise Relations >-- {{{

type x <= y =
  ( Compare x y :< [LT, EQ]
  , Assert (x <=? y) (Msg x "<=" y)
  )

ltOrEq
  :: Compare x y :< [LT, EQ]
  => proxy1 x -> proxy2 y -> Compare x y :<< [LT, EQ]
ltOrEq _ _ = which


type x /=? y = OrdCond (Compare x y) True False True

type x /= y =
  ( Compare x y :< [LT, GT]
  , Assert (x /=? y) (Msg x "/=" y)
  )

ltOrGt
  :: Compare x y :< [LT, GT]
  => proxy1 x -> proxy2 y -> Compare x y :<< [LT, GT]
ltOrGt _ _ = which


type x >= y =
 ( Compare x y :< [GT, EQ]
 , Assert (x >=? y) (Msg x ">=" y)
 )

gtOrEq
  :: Compare x y :< [GT, EQ]
  => proxy1 x -> proxy2 y -> Compare x y :<< [GT, EQ]
gtOrEq _ _ = which

-- }}}

-- --< Util >-- {{{

type Msg x op y =
  Text "Cannot satisfy: " :<>: ShowType x
  :<>: Text " " :<>: Text op :<>: Text " "
  :<>: ShowType y

-- }}}

