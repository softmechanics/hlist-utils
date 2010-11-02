{-# LANGUAGE MultiParamTypeClasses
           , FunctionalDependencies
           , FlexibleContexts
           , FlexibleInstances
           , UndecidableInstances
           , TypeFamilies
           , ScopedTypeVariables
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

-- | HMap instance for Records
instance (HMap f r r') => HMap f (Record r) (Record r') where
  hMap f (Record r) = Record $ hMap f r

-- | HReverse instance for Records
instance (HReverse r r') => HReverse (Record r) (Record r') where
  hReverse (Record r) = Record $ hReverse r

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
class CombineFs funcs r | funcs -> r where
  combineFs :: funcs -> r

instance (CombineFs' HNil (HCons e l) l') => CombineFs (HCons e l) l' where
  combineFs = combineFs' HNil

instance (CombineFs' (Record HNil) r r') => CombineFs (Record r) r' where
  combineFs (Record r) = combineFs' emptyRecord r

class CombineFs' accum funcs r | accum funcs -> r where
  combineFs' :: accum -> funcs -> r

instance (HReverse l l'
         ) => CombineFs' l HNil l' where
  combineFs' l _ = hReverse l

instance ( HExtend e l l'
         , CombineFs' l' fs r
         ) => CombineFs' l (HCons (v -> e) fs) (v -> r) where
  combineFs' l (HCons f fs) v = combineFs' ((f v) .*. l) fs

-- | Sequence an hlist of monadic actions into an hlist of their results
class HSequence l l' | l -> l' where
  hSequence :: l -> l'

instance (Monad m) => HSequence (HCons (m e) HNil) (m (HCons e HNil)) where
  hSequence (HCons e _) = do e' <- e
                             return (HCons e' HNil)

instance (Monad m
         ,HSequence (HCons e2 l) (m l')
         ) => HSequence (HCons (m e) (HCons e2 l)) (m (HCons e l')) where
  hSequence (HCons e l) = do e' <- e
                             l' <- hSequence l
                             return (HCons e' l')

-- | Apply a function at a label
class ApplyAtLabel f lbl l l' | f lbl l -> l' where
  applyAtLabel :: f -> lbl -> l -> l'

instance ApplyAtLabel f lbl HNil HNil where
  applyAtLabel _ _ _ = HNil

instance (HEq lbl lbl' eq
         ,ApplyIfTrue eq f v v'
         ,ApplyAtLabel f lbl l l'
         ) => ApplyAtLabel f lbl (HCons (LVPair lbl' v) l) (HCons (LVPair lbl' v') l') where
  applyAtLabel f lbl (HCons (LVPair v) l) = HCons (LVPair v') l'
      where v' = applyIfTrue (undefined::eq) f v
            l' = applyAtLabel f lbl l

-- | Conditional function application
class ApplyIfTrue b f v v' | b f v -> v' where
  applyIfTrue :: b -> f -> v -> v'

instance (Apply f v v') => ApplyIfTrue HTrue f v v' where
  applyIfTrue _ f v = apply f v

instance ApplyIfTrue HFalse f v v where
  applyIfTrue _ _ v = v

-- | HAll: HTrue if f evaluates to HTrue at every v in vs
class HAll f vs r | f vs -> r
instance HAll f HNil HTrue
instance (Apply f v b
         ,HAll' b f vs r
         ) => HAll f (HCons v vs) r

class HAll' b f vs r | b f vs -> r
instance HAll' HFalse f vs HFalse
instance (HAll f vs r) => HAll' HTrue f vs r

-- | HAssertAll: Similar to HAll, but will produce a type error if f evaluates to HFalse at any v in vs
class HAssertAll f vs
instance HAssertAll f HNil
instance (Apply f v r 
         ,r ~ HTrue
         ,HAssertAll f vs
         ) => HAssertAll f (HCons v vs)

-- | Class to construct values based solely on type information
class Construct a where
  construct :: a

instance Construct HTrue where
  construct = hTrue

instance Construct HFalse where
  construct = hFalse

