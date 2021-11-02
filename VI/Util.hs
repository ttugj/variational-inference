{-# LANGUAGE UnicodeSyntax, DataKinds, TypeApplications, RankNTypes, ScopedTypeVariables, TypeOperators, PolyKinds, NoStarIsType, AllowAmbiguousTypes, TypeFamilies #-}

{-# OPTIONS_GHC -fplugin GHC.TypeLits.Extra.Solver #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise #-}

module VI.Util ( 
        -- |
        -- This module collects certain data that actually needs to be computed.
                 ixM, ixΣ, ixLo, lixM, lixΣ, lixLo, basisH 
               , fromLtoR, fromRtoL
               ) where

import Data.Maybe
import Data.Proxy
import GHC.TypeLits
import GHC.TypeLits.Extra
import Data.Functor
import Control.Monad
import qualified Numeric.LinearAlgebra.Static as LA
import qualified Numeric.LinearAlgebra        as LA'

import qualified Data.List                    as L
import qualified Data.Vector.Generic          as G
import qualified Data.Vector.Generic.Mutable  as GM

ixM ∷ Int → Int → Int → Int
ixM n i j = n*i + j

ixΣ ∷ Int → Int → Int → Int
ixΣ n i j | j <= i    = fromJust $ ixLo n i j
          | otherwise = fromJust $ ixLo n j i

ixLo ∷ Int → Int → Int → Maybe Int
ixLo n i j | j <= i      = let d = i-j
                               k = n-d
                            in Just $ n*(n+1) `div` 2 - k*(k+1) `div` 2 + j 
           | otherwise   = Nothing

lixM ∷ Int → Int → [(Int,Int)]
lixM n m = [(i,j) | i ← [0..n-1], j ← [0..m-1]]

lixΣ, lixLo ∷ Int → [(Int,Int)]
lixLo n = [(e+d,e) | d ← [0..n-1], e ← [0..n-1-d]]
lixΣ    = lixLo

basisH ∷ ∀ n. KnownNat n ⇒ LA.L (n + 1) n 
basisH = let n      = fromInteger (natVal (Proxy ∷ Proxy n))
             f k i | i < k  = 1
                   | i == k = negate . fromIntegral $ k
                   | i > k  = 0
             nrm k  = sqrt $ fromIntegral (k*(k+1))
             c k    = G.map (/ nrm k) $ G.generate (n+1) (f k)
             a'     = LA'.fromColumns $ c <$> [1..n]
             Just a = LA.create a'
          in a

fromLtoR ∷ ∀ m n. (KnownNat m, KnownNat n) ⇒ LA.L m n → LA.R (m * n)
fromLtoR = fromJust . LA.create . LA'.flatten . LA.extract

fromRtoL ∷ ∀ m n. (KnownNat m, KnownNat n) ⇒ LA.R (m * n) → LA.L m n
fromRtoL = fromJust . LA.create . LA'.reshape (fromInteger $ natVal (Proxy ∷ Proxy n)) . LA.extract
