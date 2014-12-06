
module MSR3.Runtime.Base where

import Data.IORef
import qualified Data.ByteString.Lazy.Char8 as BS

import MSR3.DSL.Base
import MSR3.DSL.Combinators

import MSR3.Compiler.Base

type Env = [(VarId,Term BS.ByteString)]

lookup_value :: Read a => VarId -> Env -> Maybe (Term a)
lookup_value ref env =
  case lookup ref env of
   Just t -> case t of
              Literal bs   -> Just $ Literal (read $ BS.unpack bs)
              Variable q i -> Just (Variable q i)
              FuncApp func args -> Just (FuncApp func args)
   Nothing -> Nothing

base_apply :: Env -> Term BS.ByteString -> Term BS.ByteString
base_apply env (FuncApp func args) =
  let loop (inarg:inargs) outargs = 
        case inarg of
         Literal bs    -> loop inargs (outargs ++ [bs]) 
         Variable _ id -> case lookup id env of
                           Just t  -> case t of
                                       Literal bs -> loop inargs (outargs ++ [bs])
                                       _          -> Nothing
                           Nothing -> Nothing
         FuncApp _ _   -> case base_apply env inarg of
                           Literal bs -> loop inargs (outargs ++ [bs]) 
                           _          -> Nothing
      loop [] outargs = Just outargs
  in case loop args [] of
      Just outargs -> case func outargs of
                       Just bs -> Literal bs
                       _       -> FuncApp func args
      Nothing      -> FuncApp func args
base_apply env (Variable q ref) = 
  case lookup ref env of
   Just t  -> case t of
               Literal bs -> Literal bs
               _          -> Variable q ref 
   Nothing -> Variable q ref
base_apply _ (Literal bs) = Literal bs

term_apply :: Read a => Env -> Term a -> Term a
term_apply _ (Literal a) = Literal a
term_apply env (Variable q ref) = 
   case base_apply env (Variable q ref) of
    Literal bs     -> Literal $ read (BS.unpack bs)
    Variable q ref -> Variable q ref 
term_apply env (FuncApp func args) =
   case base_apply env (FuncApp func args) of
    Literal bs -> Literal $ read (BS.unpack bs)
    FuncApp func args -> FuncApp func args

guard_apply :: Env -> RuleGuard p -> Bool
guard_apply env (RuleGuard t) =
   case term_apply env t of
    Literal b -> b
    _         -> False

class HasTerm telem where
   is_ground :: telem -> Bool
   apply :: Env -> telem -> telem

instance Read a => HasTerm (Term a) where
   is_ground t = is_ground_term t
   apply env t = term_apply env t

instance HasTerm a => HasTerm [a] where
   is_ground ts = and $ map is_ground ts
   apply env ts = map (apply env) ts

instance HasTerm p => HasTerm (Predicate p) where
   is_ground p = is_ground $ pred_base p
   apply env (Predicate cont_type p i) = Predicate cont_type (apply env p) i

instance HasTerm p => HasTerm (RuleGuard p) where
   is_ground (RuleGuard g) = is_ground g
   apply env (RuleGuard g) = RuleGuard $ apply env g

instance HasTerm p => HasTerm (ExecStep p) where
   is_ground (MatchPredicate t p) = is_ground p
   is_ground (CheckGuard g)     = is_ground g
   apply env (MatchPredicate t p) = MatchPredicate t $ apply env p
   apply env (CheckGuard g)     = CheckGuard $ apply env g

instance HasTerm p => HasTerm (RuleExec p) where
   is_ground re = and $ [is_ground (match_predicate re),is_ground (execution_steps re),is_ground (rule_rhs re)]
   apply env (RuleExec cont_type t p esteps rhs i) = RuleExec cont_type t (apply env p) (apply env esteps) (apply env rhs) i

instance HasTerm p => HasTerm (CompContextElement p) where
   is_ground (CompPredicateElement p) = is_ground p
   is_ground (CompRuleElement res)    = is_ground res
   apply env (CompPredicateElement p) = CompPredicateElement $ apply env p
   apply env (CompRuleElement res)    = CompRuleElement $ apply env res


