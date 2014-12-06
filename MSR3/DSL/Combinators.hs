{-# OPTIONS_GHC -XMultiParamTypeClasses -XFunctionalDependencies -XFlexibleInstances -XExistentialQuantification -XGADTs -XBangPatterns -XTypeSynonymInstances -fth #-}

module MSR3.DSL.Combinators where

import System.IO.Unsafe
import Data.IORef
-- import Language.Haskell.TH
-- import Language.Haskell.TH.Syntax
import qualified Data.ByteString.Lazy.Char8 as BS


import MSR3.DSL.Base

-- Term Combinators

wild :: Term a
wild = WildCard

new_term :: () -> Term a
new_term _ = Variable Forall (unsafePerformIO $ newIORef ())

for_all :: () -> Term a
for_all _ = Variable Forall (unsafePerformIO $ newIORef ())

exist :: () -> Term a
exist _ = Variable Exist (unsafePerformIO $ newIORef ())

-- Lift functions. Note that Term x arguments are 'dummies'. Simply passed in to retain typing information to allow the compiler
-- to infer the actual type instance of the given function, while the lift function 'wraps' the given function with a 'typeless' 
-- shell.
lift_func_1 :: (Read a,Show b) => (a -> b) -> Term a -> [BS.ByteString] -> Maybe BS.ByteString
lift_func_1 func _ = \bs -> case bs of
                             a:_ -> Just $ term_encode (func (term_decode a))
                             _   -> Nothing

lift_func_2 :: (Read a,Read b,Show c) => (a -> b -> c) -> Term a -> Term b -> [BS.ByteString] -> Maybe BS.ByteString
lift_func_2 func _ _ = \bs -> case bs of
                               a:b:_ -> Just $ term_encode (func (term_decode a) (term_decode b))
                               _     -> Nothing

lift_func_3 :: (Read a,Read b,Read c,Show d) => (a -> b -> c -> d) -> Term a -> Term b -> Term c -> [BS.ByteString] -> Maybe BS.ByteString
lift_func_3 func _ _ _ = \bs -> case bs of
                                 a:b:c:_ -> Just $ term_encode (func (term_decode a) (term_decode b) (term_decode c))
                                 _       -> Nothing


(.+.) :: (Show a,Read a,Num a) => Term a -> Term a -> Term a
t1 .+. t2 = FuncApp (lift_func_2 (+) t1 t2) [term_arg t1,term_arg t2]
(.-.) :: (Show a,Read a,Num a) => Term a -> Term a -> Term a
t1 .-. t2 = FuncApp (lift_func_2 (-) t1 t2) [term_arg t1,term_arg t2]
(.*.) :: (Show a,Read a,Num a) => Term a -> Term a -> Term a
t1 .*. t2 = FuncApp (lift_func_2 (*) t1 t2) [term_arg t1,term_arg t2]
(./.) :: (Show a,Read a,Num a,Fractional a) => Term a -> Term a -> Term a
t1 ./. t2 = FuncApp (lift_func_2 (/) t1 t2) [term_arg t1,term_arg t2]
(.:.) :: (Show a,Read a) => Term a -> Term [a] -> Term [a]
t1 .:. t2 = FuncApp (lift_func_2 (:) t1 t2) [term_arg t1,term_arg t2]

-- Predicate Combinators

predicate :: BasePredicate p => p -> Predicate p
predicate p = Predicate Linear p 0

class Bangable b where
  bang :: b -> b

instance Bangable (Predicate p) where
  bang (Predicate _ p i) = Predicate Unrestricted p i

instance Bangable (Rule p) where
  bang (Rule _ lhs rhs) = Rule Unrestricted lhs rhs

{-
-- Quantifier Combinators

class QuantifierBinder elem where
  (%) :: BasePredicate p => Quantifier -> elem p -> ContextElement p

instance QuantifierBinder Predicate where
  qf % p = QuantifiedElement [qf] [PredicateElement p]
instance QuantifierBinder Rule where
  qf % r = QuantifiedElement [qf] [RuleElement r]
instance QuantifierBinder LRHSComponents where
  qf % (LRHSComponents ps _ cs) = QuantifiedElement [qf] $ (map (\p -> PredicateElement p) ps) ++ cs
instance QuantifierBinder ContextElement where
  qf % (QuantifiedElement qfs cs) = QuantifiedElement (qf:qfs) cs
  qf % (PredicateElement p) = QuantifiedElement [qf] [PredicateElement p]
  qf % (RuleElement r) = QuantifiedElement [qf] [RuleElement r]

infixr 3 %
-}

-- Rule Combinators

data LRHSComponents p = LRHSComponents [Predicate p] [RuleGuard p] [ContextElement p] deriving Show


guard :: Term Bool -> RuleGuard p
guard bexp = RuleGuard bexp

(.=.) :: (Show a,Read a,Eq a) => Term a -> Term a -> Term Bool
t1 .=. t2 = FuncApp (lift_func_2 (==) t1 t2) [term_arg t1,term_arg t2]
(.!=.) :: (Show a,Read a,Eq a) => Term a -> Term a -> Term Bool
t1 .!=. t2 = FuncApp (lift_func_2 (/=) t1 t2) [term_arg t1,term_arg t2]
(.>.) :: (Show a,Read a,Ord a) => Term a -> Term a -> Term Bool
t1 .>. t2 = FuncApp (lift_func_2 (>) t1 t2) [term_arg t1,term_arg t2]
(.<.) :: (Show a,Read a,Ord a) => Term a -> Term a -> Term Bool
t1 .<. t2 = FuncApp (lift_func_2 (<) t1 t2) [term_arg t1,term_arg t2]
(.>=.) :: (Show a,Read a,Ord a) => Term a -> Term a -> Term Bool
t1 .>=. t2 = FuncApp (lift_func_2 (>=) t1 t2) [term_arg t1,term_arg t2]
(.<=.) :: (Show a,Read a,Ord a) => Term a -> Term a -> Term Bool
t1 .<=. t2 = FuncApp (lift_func_2 (<=) t1 t2) [term_arg t1,term_arg t2]

class LRHSBinder elem1 elem2 where
  (/\) :: BasePredicate p => elem1 p -> elem2 p -> LRHSComponents p

instance LRHSBinder Predicate Predicate where
  p1 /\ p2 = LRHSComponents [p1,p2] [] []
instance LRHSBinder Predicate RuleGuard where
  p /\ g = LRHSComponents [p] [g] []
instance LRHSBinder RuleGuard Predicate where
  g /\ p = LRHSComponents [p] [g] []
instance LRHSBinder RuleGuard RuleGuard where
  g1 /\ g2 = LRHSComponents [] [g1,g2] []

instance LRHSBinder Predicate ContextElement where
  p /\ c = LRHSComponents [p] [] [c]
instance LRHSBinder ContextElement Predicate where
  c /\ p = LRHSComponents [p] [] [c]
instance LRHSBinder ContextElement ContextElement where
  c1 /\ c2 = LRHSComponents [] [] [c1,c2]


instance LRHSBinder Predicate LRHSComponents where
  p /\ (LRHSComponents ps gs cs) = LRHSComponents (p:ps) gs cs
instance LRHSBinder RuleGuard LRHSComponents where
  g /\ (LRHSComponents ps gs cs) = LRHSComponents ps (g:gs) cs
instance LRHSBinder ContextElement LRHSComponents where
  c /\ (LRHSComponents ps gs cs) = LRHSComponents ps gs (c:cs)

infixr 2 /\
--infixr 3 .=.
--infixr 3 .?.

class RuleBinder lhs rhs where
  (.=>.) :: BasePredicate p => lhs p -> rhs p -> Rule p

instance RuleBinder Predicate Predicate where
  lp .=>. rp = Rule Linear (RuleLHS [lp] []) (RuleRHS [PredicateElement rp])
instance RuleBinder LRHSComponents LRHSComponents where
  (LRHSComponents lps lgs _) .=>. (LRHSComponents rps _ rcs) = Rule Linear (RuleLHS lps lgs) (RuleRHS ((map (\p -> PredicateElement p) rps) ++ rcs))
instance RuleBinder Predicate LRHSComponents where
  lp .=>. (LRHSComponents rps _ rcs) = Rule Linear (RuleLHS [lp] []) (RuleRHS ((map (\p -> PredicateElement p) rps) ++ rcs))
instance RuleBinder LRHSComponents Predicate where
  (LRHSComponents lps lgs _) .=>. rp = Rule Linear (RuleLHS lps lgs) (RuleRHS [PredicateElement rp])
instance RuleBinder Predicate Rule where
  lp .=>. rr = Rule Linear (RuleLHS [lp] []) (RuleRHS [RuleElement rr])
instance RuleBinder LRHSComponents Rule where
  (LRHSComponents lps lgs _) .=>. rr = Rule Linear (RuleLHS lps lgs) (RuleRHS [RuleElement rr])
instance RuleBinder Predicate ContextElement where
  lp .=>. rc = Rule Linear (RuleLHS [lp] []) (RuleRHS [rc])
instance RuleBinder LRHSComponents ContextElement where
  (LRHSComponents lps lgs _) .=>. rc = Rule Linear (RuleLHS lps lgs) (RuleRHS [rc])

{-
(.=>.) :: LRHSComponents p -> LRHSComponents p -> Rule p
(LRHSComponents lps lgs lcs) .=>. (LRHSComponents rps rgs rcs) = Rule Linear (RuleLHS lps lgs) (RuleRHS ((map (\p -> PredicateElement p) rps) ++ rcs))
-}

infixr 1 .=>.

