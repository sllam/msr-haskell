{-# OPTIONS_GHC -XMultiParamTypeClasses -XFunctionalDependencies -XFlexibleInstances -XExistentialQuantification -XGADTs -XBangPatterns -XDeriveDataTypeable #-}

module MSR3.DSL.Base where

import Data.Typeable
import Data.Generics
import Data.List
import Data.IORef
import qualified Data.ByteString.Lazy.Char8 as BS

import MSR3.Misc.Pretty

-- Terms
type VarId = IORef ()
data Quantifier = Exist | Forall deriving (Typeable,Data)

-- data FuncArg = VarArg VarId | ExpArg BS.ByteString | FuncArg FuncAppExp
-- data FuncAppExp = FuncAppExp ([BS.ByteString] -> Maybe BS.ByteString) [Term BS.ByteString]
data Term a = Variable Quantifier VarId | Literal a | FuncApp ([BS.ByteString] -> Maybe BS.ByteString) [Term BS.ByteString] | WildCard deriving (Typeable,Data)

instance Eq a => Eq (Term a) where
  (Variable _ r1) == (Variable _ r2) = (==) r1 r2
  (Literal l1)  == (Literal l2)  = l1 == l2
  _ == _ = False

instance Show a => Show (Term a) where
  show (Variable _ s) = "var"
  show (Literal a)  = show a
  show (FuncApp f args) = "func:" ++ (show $ length args)
  show WildCard = "_"

instance Show a => Pretty (Term a) where
  pretty env (Variable _ r) = pretty_var env r
  pretty env (FuncApp _ fs) = 
    let (env',args) = pretty (env { delimiter="," }) fs
    in (env' {delimiter=(delimiter env)},"func(" ++ args ++ ")")
  pretty env (Literal a) = (env,show a)
  pretty env WildCard    = (env,"_")

instance Pretty (IORef ()) where
  pretty env ref = pretty_var env ref

is_ground_term :: Term a -> Bool
is_ground_term (Variable _ _) = False
is_ground_term (Literal _)  = True
is_ground_term (FuncApp _ args) = length args == 0 
is_ground_term WildCard = False

ground_terms :: [Term a] -> [Term a]
ground_terms ts = filter is_ground_term ts

term_value :: Term a -> a
term_value (Literal a) = a
term_value _ = error "Tried to retrieve value non-ground term"

term_ref :: Term a -> Maybe (IORef ())
term_ref (Variable _ ref) = Just ref
term_ref _ = Nothing
 
term_encode :: Show a => a -> BS.ByteString
term_encode a = BS.pack (show a)

term_decode :: Read a => BS.ByteString -> a
term_decode bs = read (BS.unpack bs)

term_arg :: Show a => Term a -> Term BS.ByteString
term_arg (Variable q ref) = Variable q ref
term_arg (Literal a)      = Literal (term_encode a)
term_arg (FuncApp f args) = FuncApp f args
term_arg WildCard         = WildCard

to_bs :: Show a => Term a -> Term BS.ByteString
to_bs = term_arg

from_bs :: Read a => Term BS.ByteString -> Term a
from_bs (Variable q ref) = Variable q ref
from_bs (Literal a)      = Literal (term_decode a)
from_bs (FuncApp f args) = FuncApp f args
from_bs WildCard         = WildCard

-- Predicates

data ContextType = Linear | Unrestricted deriving Eq

-- Base definition of a class of predicates
class BasePredicate p where
  symbol :: p -> Term String
  sym_id :: p -> Int
  num_of_preds :: [p] -> Int

data Predicate p where
  Predicate :: BasePredicate p => ContextType -> p -> Int -> Predicate p

pred_id :: Predicate p -> Int
pred_id (Predicate _ _ i) = i

pred_base :: Predicate p -> p
pred_base (Predicate _ p _) = p

instance Eq (Predicate p) where
  p1 == p2 = pred_id p1 == pred_id p2

instance Show p => Show (Predicate p) where
  show (Predicate cont p i) = let cont_text = case cont of
                                               Linear       -> ""
                                               Unrestricted -> "!"
                                  is = if i > 0 then "#" ++ (show i)
                                                else ""
                              in cont_text ++ (show p) ++ is

instance Pretty p => Pretty (Predicate p) where
  pretty env (Predicate cont p i) = let cont_text = case cont of
                                               Linear       -> ""
                                               Unrestricted -> "!"
                                        is = if i > 0 then "#" ++ (show i)
                                                      else ""
                                        (env',ps) = pretty env p
                                    in (env',cont_text ++ ps ++ is)

data HomoPredicate a = HomoPredicate (Term String) [Term a]

instance BasePredicate (HomoPredicate a) where
  symbol (HomoPredicate x _) = x
  sym_id _ = 1
  num_of_preds _ = 1

instance Show a => Show (HomoPredicate a) where
  show (HomoPredicate x as) =  filter (\c -> c /= '\"') $ (show x) ++ "(" ++ (foldl (++) "" (intersperse "," (map show as))) ++ ")"
 

-- Quantifiers

data ContextElement p = PredicateElement (Predicate p)
                      | RuleElement (Rule p)

instance Show p => Show (ContextElement p) where
  show (PredicateElement p) = show p
  show (RuleElement r) = show r

instance Pretty p => Pretty (ContextElement p) where
  pretty env (PredicateElement p) = pretty env p
  pretty env (RuleElement r) = pretty env r

-- Rules

-- data RuleGuard p = forall a. Show a => EqGuard (Term a) (Term a)
--                  | PredGuard (Predicate p)

data RuleGuard p = RuleGuard (Term Bool)
data RuleLHS p = RuleLHS [Predicate p] [RuleGuard p]
data RuleRHS p = RuleRHS [ContextElement p]
data Rule p = Rule ContextType (RuleLHS p) (RuleRHS p)

instance Show (RuleGuard p) where
  show (RuleGuard fapp)   = "?(" ++ (show fapp) ++ ")"
instance Show p => Show (RuleLHS p) where
  show (RuleLHS ps []) = (foldl (++) "" (intersperse "," (map show ps))) 
  show (RuleLHS ps gs) = (foldl (++) "" (intersperse "," (map show ps))) ++ "," ++ (foldl (++) "" (intersperse "," (map show gs)))
instance Show p => Show (RuleRHS p) where
  show (RuleRHS cs) = (foldl (++) "" (intersperse "," (map show cs)))
instance Show p => Show (Rule p) where
  show (Rule cont lhs rhs) =
   let cont_text = case cont of
                    Linear       -> ""
                    Unrestricted -> "!"
   in cont_text ++ "(" ++ (show lhs) ++ "=>" ++ (show rhs) ++ ")"

instance Pretty p => Pretty (RuleGuard p) where
  pretty env (RuleGuard g) = pretty env g
instance Pretty p => Pretty (RuleLHS p) where
  pretty env (RuleLHS ps gs) = let (env',s1)  = pretty (env{delimiter=","}) ps
                                   (env'',s2) = pretty (env'{delimiter=","}) gs
                               in if length s2 > 0
                                  then (env''{delimiter=delimiter env},s1 ++ "," ++ s2)
                                  else (env''{delimiter=delimiter env},s1)
instance Pretty p => Pretty (RuleRHS p) where
  pretty env (RuleRHS cs) = let (env',ss) = pretty (env{delimiter=","}) cs
                            in (env'{delimiter=delimiter env},ss)
instance Pretty p => Pretty (Rule p) where
  pretty env (Rule cont lhs rhs) =
   let cont_text = case cont of
                    Linear       -> ""
                    Unrestricted -> "!"
       (env',ls)  = pretty env lhs
       (env'',rs) = pretty env' rhs
   in (env'', cont_text ++ "(" ++ ls ++ "=>" ++ rs ++ ")")

class HasContextType p where
  context_type :: p -> ContextType

instance HasContextType (Predicate p) where
  context_type (Predicate cont_type _ _) = cont_type

instance HasContextType (Rule p) where
  context_type (Rule cont_type _ _) = cont_type

-- Roles

data Role p = Role ([ContextElement p])




