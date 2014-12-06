
module MSR3.Runtime.Match where

import MSR3.DSL.Base

import MSR3.Runtime.Base
import MSR3.Runtime.Context

term_match :: (Read a,Show a,Eq a) => Env -> Term a -> Term a -> Maybe Env
term_match env (Literal a) (Literal b) = 
   if a == b then Just env
             else Nothing
term_match env (v1@(Variable _ r1)) t2 = 
   case lookup_value r1 env of
     Nothing -> Just ((r1,to_bs t2):env)
     Just t1 -> term_match env t1 t2
term_match env WildCard _ = Just env

class Match p where
  match :: Env -> p -> p -> Maybe Env

instance (Read a,Show a,Eq a) => Match (Term a) where
  match = term_match

instance Match p => Match (Predicate p) where
  match env (Predicate _ p _) (Predicate _ p' _) = match env p p'

{-
data Context p = Context { l_context   :: [[Predicate p]]
                         , u_context   :: [[Predicate p]]
                         , l_rules     :: [RuleExec p]
                         , u_rules     :: [RuleExec p]
                         , environment :: Env
                         , next_id     :: Int }
-}

get_matching_candidates :: (BasePredicate p,Match p) => Env -> Predicate p -> Context p -> [(Env,Predicate p)]
get_matching_candidates env p context = 
  let candidates = ((l_context context) !! (sym_id $ pred_base p)) ++ ((u_context context) !! (sym_id $ pred_base p))
      loop (can:cans) outputs =
        case match env p can of
         Just env' -> loop cans ((env',can):outputs)
         Nothing   -> loop cans outputs
      loop [] outputs = outputs
  in loop candidates []

