
module MSR3.Runtime.Rewrite where

import Data.List

import MSR3.DSL.Base
import MSR3.Compiler.Base 

import MSR3.Runtime.Base
import MSR3.Runtime.Goals
import MSR3.Runtime.Context
import MSR3.Runtime.Match

data RuleMatch p = RuleMatch { rule_actual   :: RuleExec p
                             , rule_matched  :: Int
                             , lhs_matched   :: [Int]
                             , matching_env  :: Env }

init_context :: (Eq p, Match p, HasTerm p, BasePredicate p) => [Predicate p] -> [Rule p] -> (Goals p,Context p)
init_context preds rules =
   let cont_elems = (map PredicateElement preds) ++ (map RuleElement rules)
       (next_id,comp_cont_elems) = label_context_elements 1 (map compile_context_elem cont_elems)
       (new_preds,new_rules)     = unfold_context_elements comp_cont_elems
       empty_context             = replicate (num_of_preds $ map pred_base new_preds) []
       (l_context,u_context)     = add_predicates (empty_context,empty_context) new_preds
       (l_rules,u_rules)         = add_rules ([],[]) new_rules
   in (new_preds,Context l_context u_context l_rules u_rules [] next_id)

run :: (Eq p, Match p, HasTerm p, BasePredicate p) => Int -> (Goals p,Context p) -> (Goals p,Context p)
run 0 (goals,context) = (goals,context)
run n (goals,context) = 
   case rewrite_step (goals,context) of 
    (_,goals',context'):_ -> run (n-1) (goals',context')
    []                    -> ([],context)

rewrite_step :: (Eq p, Match p, HasTerm p, BasePredicate p) => (Goals p,Context p) -> [(RuleMatch p,Goals p,Context p)]
rewrite_step (goals,context) = 
   let all_choices = map (\goal -> foldl (++) [] $ map (\re -> execute_rule goal re goals context) ((l_rules context) ++ (u_rules context))) goals
   in merge_choices all_choices [] 
   where
     merge_choices (choice:choices) choice' = merge_choices choices (union_choice choice choice' [])
     merge_choices [] choice = choice
     union_choice (ch:chs) choice' rest = 
        if choice_elem ch choice'
        then union_choice chs choice' rest
        else union_choice chs choice' (rest ++ [ch])
     union_choice [] choice' rest = rest ++ choice'
     choice_elem (rmt,gs,ctxt) ((rmt',_,_):choice) =
        if rule_matched rmt == rule_matched rmt'
        then if (sort $ lhs_matched rmt) == (sort $ lhs_matched rmt')
             then True
             else choice_elem (rmt,gs,ctxt) choice
        else choice_elem (rmt,gs,ctxt) choice
     choice_elem _ [] = False


execute_rule :: (Eq p,Match p,BasePredicate p,HasTerm p) => Predicate p -> RuleExec p -> Goals p -> Context p -> [(RuleMatch p,Goals p,Context p)]
execute_rule p re goals context =
   case match (environment context) (match_predicate re) p of
    Just env' -> map apply_rule_head $ match_rule_heads (env',[(match_type re,pred_id p)]) (execution_steps re)
    Nothing   -> []
   where
     match_rule_heads (env,match_infos) (estep:esteps) =
      case estep of
       MatchPredicate t p -> let choices = filter (\(_,p) -> notElem (pred_id p) (map snd match_infos)) $ get_matching_candidates env p context
                             in foldl (++) [] $ map (\(env',p) -> match_rule_heads (env',match_infos ++ [(t,pred_id p)]) esteps) choices
       CheckGuard g -> if guard_apply env g
                       then match_rule_heads (env,match_infos) esteps
                       else []
     match_rule_heads (env,match_infos) [] = [(env,match_infos)]
     apply_rule_head (env,match_infos) =
       let -- Apply substituition to rule rhs and label the new predicates
           (next_id',l_rule_rhs) = label_context_elements (next_id context) (map (apply env) (rule_rhs re))
           (new_preds,new_rules) = unfold_context_elements l_rule_rhs
           -- Delete linear predicates (that matched simplified LHS) and linear rule
           l_context' = delete_predicates (l_context context) (map snd $ filter (\(t,_) -> t == Simp) match_infos)
           l_rules'   = delete_rules (l_rules context) [rule_id re] 
           -- Add new predicates and rules to context
           (l_context'',u_context'') = add_predicates (l_context',u_context context) new_preds
           (l_rules'',u_rules'')     = add_rules (l_rules',u_rules context) new_rules
           -- Derive new goals
           react_preds = reactivate_rule_predicates (l_context',u_context context) new_rules
           goals'  = union new_preds $ filter (\g -> notElem (pred_id g) (map snd $ filter (\(t,_) -> t == Simp) match_infos)) goals 
           goals'' = union goals' react_preds
       in (RuleMatch re (rule_id re) (map snd match_infos) env,goals'',Context l_context'' u_context'' l_rules'' u_rules'' (environment context) next_id')

