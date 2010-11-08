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

-- | Type-level function for HAppend
data HAppendF = HAppendF

instance (HAppend l1 l2 l3) => Apply HAppendF (l1,l2) l3 where
  apply _ (l1,l2) = hAppend l1 l2

-- | Concatenate an HList of HLists
class (HFoldr HAppendF HNil ls l) => HConcat ls l | ls -> l where
  hConcat :: ls -> l

instance (HFoldr HAppendF HNil ls l) => HConcat ls l where
  hConcat = hFoldr (undefined::HAppendF) HNil

-- | Left-fold an HList using <*>
data ApplicativeF = ApplicativeF

instance (a ~ a'
         ,f ~ f'
         ,f ~ f''
         ,b ~ b'
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

instance (ApplyIfLabeled f lbl e e'
         ,ApplyAtLabel f lbl l l'
         ) => ApplyAtLabel f lbl (HCons e l) (HCons e' l') where
  applyAtLabel f lbl (HCons e l) = HCons e' l'
      where e' = applyIfLabeled f lbl e
            l' = applyAtLabel f lbl l

-- | Apply a function to a single element if labeled
class ApplyIfLabeled f lbl e e' where
  applyIfLabeled :: f -> lbl -> e -> e'

instance (Labeled lbl e eq
         ,ExtractLabeled e v
         ,ApplyIfTrue eq f v v'
         ,UpdateLabeled e v' e'
         ) => ApplyIfLabeled f lbl e e' where
  applyIfLabeled f lbl e = updateLabeled e $ applyIfTrue (undefined::eq) f $ extractLabeled e

-- | Label equality, abstracts away LVPair implementation
class Labeled lbl t b | lbl t -> b
instance HEq lbl lbl' eq => Labeled lbl (LVPair lbl' v) eq

-- | Labeled value extraction, abstracts away LVPair implementation
class ExtractLabeled t v | t -> v where
  extractLabeled :: t -> v
instance ExtractLabeled (LVPair l v) v where
  extractLabeled (LVPair v) = v

-- | Labeled value update, abstracts away LVPair implementation
class UpdateLabeled t v t' | t v -> t' where
  updateLabeled :: t -> v -> t'

instance UpdateLabeled (LVPair l v) v' (LVPair l v') where
  updateLabeled _ = LVPair

-- | Conditional function application
class ApplyIfTrue b f v v' | b f v -> v' where
  applyIfTrue :: b -> f -> v -> v'

instance (Apply f v v') => ApplyIfTrue HTrue f v v' where
  applyIfTrue _ f v = apply f v

instance ApplyIfTrue HFalse f v v where
  applyIfTrue _ _ v = v

-- | Conditional HList prepend
class PrependIfTrue b e l l' | b e l -> l' where
  prependIfTrue :: b -> e -> l -> l'

instance PrependIfTrue HFalse e l l where
  prependIfTrue _ _ l = l

instance PrependIfTrue HTrue e l (HCons e l) where
  prependIfTrue _ e l = HCons e l

-- | Filter an HList
class (HFoldr (HFilterF f) HNil l l'
      ) => HFilter f l l' | f l -> l' where
  hFilter :: f -> l -> l'

instance (HFoldr (HFilterF f) HNil l l'
         ) => HFilter f l l' where
  hFilter f l = hFoldr (HFilterF f) HNil l

newtype HFilterF f = HFilterF f

instance (Apply f e b
         ,HBool b
         ,PrependIfTrue b e l l'
         ) => Apply (HFilterF f) (e,l) l' where
  apply (HFilterF f) (e,l) = prependIfTrue (apply f e) e l

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

instance Construct HNil where
  construct = hNil

instance (Construct e
         ,Construct l
         ) => Construct (HCons e l) where
  construct = HCons (construct::e) (construct::l)

instance (Construct l
         ,HRLabelSet l
         ) => Construct (Record l) where
  construct = mkRecord (construct::l)

-- | Variant of Construct, which defaults to undefined
class ConstructSpine a where
  constructSpine :: a
  constructSpine = undefined

instance ConstructSpine HNil where
  constructSpine = hNil

instance (ConstructSpine e
         ,ConstructSpine l
         ) => ConstructSpine (HCons e l) where
  constructSpine = HCons (constructSpine :: e) (constructSpine :: l)

instance (ConstructSpine l
         ,HRLabelSet l
         ) => ConstructSpine (Record l) where
  constructSpine = mkRecord (constructSpine :: l) 

instance ConstructSpine (LVPair l v)

-- | Function type wrapper around HTMember
newtype HTMemberOf l = HTMemberOf l

instance (HTMember e l b) => Apply (HTMemberOf l) e b where
  apply (HTMemberOf l) e = hTMember e l

-- | Like HTMemberOf, but produces a type error if HFalse
newtype AssertHTMemberOf l = AssertHTMemberOf l

instance (HTMember e l b
         ,HTMemberOfAssertion b e l
         ) => Apply (AssertHTMemberOf l) e b

class HTMemberOfAssertion b e l
instance HTMemberOfAssertion HTrue e l
instance (NotMemberOf e l) => HTMemberOfAssertion HFalse e l

-- | Error message to display if AssertHTMemberOf evaluates to HFalse.  Intentionally no instances
class NotMemberOf e l

