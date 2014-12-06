
module MSR3.Compiler.Base where

import MSR3.Misc.Pretty

import MSR3.DSL.Base

data LHSType = Simp | Prop deriving (Show,Eq)

data ExecStep p = MatchPredicate LHSType (Predicate p)
                | CheckGuard (RuleGuard p)
data RuleExec p = RuleExec { rule_context    :: ContextType
                           , match_type      :: LHSType
                           , match_predicate :: Predicate p
                           , execution_steps :: [ExecStep p]
                           , rule_rhs :: [CompContextElement p]
                           , rule_id  :: Int }

data CompContextElement p = CompPredicateElement (Predicate p)
                          | CompRuleElement [RuleExec p]

instance Pretty p => Pretty (ExecStep p) where
   pretty env (MatchPredicate t p) = let (env',s) = pretty env p
                                     in (env', s ++ "-" ++ (show t))
   pretty env (CheckGuard g)       = pretty env g
instance Pretty p => Pretty (RuleExec p) where
   pretty env (RuleExec cont t mp es rhs i) =
     let cont_text = case cont of
                    Linear       -> ""
                    Unrestricted -> "!"
         (env1,mps)  = pretty env mp
         (env2,ess)  = pretty (env1{delimiter=","}) es
         (env3,rhss) = pretty (env2{delimiter=","}) rhs
     in (env3{delimiter=delimiter env},cont_text ++ "<" ++ mps ++ "-" ++ (show t) ++ "|" ++ ess ++ "=>" ++ rhss ++ ">" ++ "#" ++ (show i))
instance Pretty p => Pretty (CompContextElement p) where
   pretty env (CompPredicateElement p) = pretty env p
   pretty env (CompRuleElement res) = let (env',ress) = pretty env res
                                      in (env',"[" ++ ress ++ "]") 

instance HasContextType (RuleExec p) where
  context_type re = rule_context re

-- data RuleGuard p = RuleGuard (Term Bool)
-- data RuleLHS p = RuleLHS [Predicate p] [RuleGuard p]
-- data RuleRHS p = RuleRHS [ContextElement p]
-- data Rule p = Rule ContextType (RuleLHS p) (RuleRHS p)
-- data ContextElement p = PredicateElement (Predicate p)
--                       | RuleElement (Rule p)

compile_rule :: Eq p => Rule p -> [RuleExec p]
compile_rule (Rule cont_type (RuleLHS ps gs) (RuleRHS cs)) = 
   let gen_rule_execs ps (p:ps') gs ccs rexecs = 
         let exec_steps = (map (\p -> MatchPredicate Simp p) (ps ++ ps')) ++ (map (\g -> CheckGuard g) gs)
             rexec      = RuleExec cont_type Simp p exec_steps ccs 0
         in gen_rule_execs (ps ++ [p]) ps' gs ccs (rexec:rexecs)
       gen_rule_execs _ [] _ _ rexecs = rexecs
       intro_propagation (RuleExec cont_type t p exec_steps ccs i) =
          let ((MatchPredicate t' p'):exec_steps',ccs') = intro_propagation' ((MatchPredicate t p):exec_steps)  ([],ccs)
          in RuleExec cont_type t' p' exec_steps' ccs' i
       intro_propagation' (es:ess) (ess',comp_context_elems) =
         case es of
          MatchPredicate _ p -> case subsumed_in p comp_context_elems of
                                 Just comp_context_elems' -> intro_propagation' ess (ess' ++ [MatchPredicate Prop p],comp_context_elems')
                                 Nothing -> intro_propagation' ess (ess' ++ [es],comp_context_elems)
          CheckGuard g       -> intro_propagation' ess (ess' ++ [es],comp_context_elems)
         where
          subsumed_in p (cp:cps) =
           case cp of
            CompPredicateElement p' -> if pred_base p == pred_base p' 
                                       then Just cps
                                       else case subsumed_in p cps of
                                             Just cps' -> Just (cp:cps')
                                             Nothing   -> Nothing
            CompRuleElement _ -> case subsumed_in p cps of
                                  Just cps' -> Just (cp:cps')
                                  Nothing   -> Nothing
          subsumed_in p [] = Nothing
       intro_propagation' [] (ess,comp_context_elems) = (ess,comp_context_elems)
   in map intro_propagation $ gen_rule_execs [] ps gs (map compile_context_elem cs) []

compile_context_elem :: Eq p => ContextElement p -> CompContextElement p
compile_context_elem (PredicateElement p) = CompPredicateElement p
compile_context_elem (RuleElement r) = CompRuleElement $ compile_rule r



