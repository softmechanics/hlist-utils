{-# LANGUAGE MultiParamTypeClasses
           , FunctionalDependencies
           , FlexibleContexts
           , FlexibleInstances
           , UndecidableInstances
           , TypeFamilies
           #-}
module Data.HList.Utils where

import Data.HList
import Control.Applicative

-- | HFoldl missing from HList
class HFoldl f v l r | f v l -> r where
  hFoldl :: f -> v -> l -> r
  
instance HFoldl f v HNil v where  
  hFoldl _ v _ = v
  
instance (Apply f (v,e) v'
         ,HFoldl f v' l r
         ) => HFoldl f v (HCons e l) r where
  hFoldl f v (HCons e l) = hFoldl f (apply f (v,e)) l
  

-- | Left-fold an HList using <*>
data ApplicativeF = ApplicativeF

instance (a ~ a'
         ,b ~ b'
         ,f ~ f'
         ,f ~ f''
         ,Applicative f
         ) => Apply ApplicativeF (f (a -> b) , f' a') (f'' b') where
  apply _ (f,e) = f <*> e

-- | Turn an n-element HList of unary functions into an n-ary function that evaluates
-- to an n-element hlist of values
class (CombineFs' HNil funcs r) => CombineFs funcs r | funcs -> r where
  combineFs :: funcs -> r
  combineFs = combineFs' HNil

class CombineFs' accum funcs r | accum funcs -> r where
  combineFs' :: accum -> funcs -> r

instance (HReverse l l'
         ) => CombineFs' l HNil l' where
  combineFs' l _ = hReverse l

instance (CombineFs' (HCons e l) fs r
         ) => CombineFs' l (HCons (v -> e) fs) (v -> r) where
  combineFs' l (HCons f fs) v = combineFs' (HCons (f v) l) fs

