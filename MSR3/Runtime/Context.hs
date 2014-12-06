
module MSR3.Runtime.Context where

import Data.IORef

import MSR3.Misc.Pretty

import MSR3.DSL.Base
import MSR3.DSL.Combinators

import MSR3.Compiler.Base

import MSR3.Runtime.Base

data Context p = Context { l_context   :: [[Predicate p]]
                         , u_context   :: [[Predicate p]]
                         , l_rules     :: [RuleExec p]
                         , u_rules     :: [RuleExec p]
                         , environment :: Env
                         , next_id     :: Int }

instance Pretty p => Pretty (Context p) where
  pretty env context =
    let (env1,lps) = pretty env  $ l_context context
        (env2,ups) = pretty env1 $ u_context context
        (env3,lrs) = pretty env2 $ l_rules context
        (env4,urs) = pretty env3 $ u_rules context
        (env5,ens) = pretty env4 $ environment context
        conts = "\n======= Linear Predicates =======\n" ++ lps ++ 
                "\n==== Unrestricted Predicates ====\n" ++ ups ++
                "\n========= Linear Rules ==========\n" ++ lrs ++
                "\n====== Unrestricted Rules =======\n" ++ urs ++ 
                "\n======= Substitution Env ========\n" ++ ens ++
                "\n======= Next Id : " ++ (show $ next_id context) ++ "=======\n"
    in (env5,conts)

unfold_context_elements :: [CompContextElement p] -> ([Predicate p],[RuleExec p])
unfold_context_elements (c:cs) = 
   let (ps,rss) = unfold_context_elements cs
   in case c of
       CompPredicateElement p -> (p:ps,rss)
       CompRuleElement rs     -> (ps,rs ++ rss)
unfold_context_elements [] = ([],[])

new_context :: Context p
new_context = Context [] [] [] [] [] 1

label_context_elements :: Int -> [CompContextElement p] -> (Int,[CompContextElement p])
label_context_elements i cs =
  let loop j (ic:ics) ocs =
       case ic of
        CompPredicateElement (Predicate l p _) ->  loop (j+1) ics ((CompPredicateElement $ Predicate l p j):ocs)
        CompRuleElement rs -> loop (j+1) ics ((CompRuleElement $ map (\r -> r { rule_id = j }) rs):ocs)
      loop j [] ocs = (j,ocs)
  in loop i cs []

add_predicates :: BasePredicate p => ([[Predicate p]],[[Predicate p]]) -> [Predicate p] -> ([[Predicate p]],[[Predicate p]])
add_predicates (lpreds,upreds) ps =
  let loop (p:ps) (lpreds',upreds') =
       case context_type p of
        Linear        -> loop ps (add_predicate p (sym_id $ pred_base p) lpreds' [],upreds')
        Unrestricted  -> loop ps (lpreds',add_predicate p (sym_id $ pred_base p) upreds' [])
      loop [] output = output
  in loop ps (lpreds,upreds)
  where
    add_predicate p 0 (cs:css) css' = css' ++ ((p:cs):css)
    add_predicate p n (cs:css) css' = add_predicate p (n-1) css (css' ++ [cs])

add_rules :: BasePredicate p => ([RuleExec p],[RuleExec p]) -> [RuleExec p] -> ([RuleExec p],[RuleExec p])
add_rules (lrules,urules) rs =
   let loop (r:rs) (lrs,urs) =
        case context_type r of
         Linear       -> loop rs (r:lrs,urs)
         Unrestricted -> loop rs (lrs,r:urs)
       loop [] output = output
   in loop rs (lrules,urules)

-- TODO: Refine this
reactivate_rule_predicates :: ([[Predicate p]],[[Predicate p]]) -> [RuleExec p] -> [Predicate p]
reactivate_rule_predicates (lpreds,upreds) _ = (foldl (++) [] lpreds) ++ (foldl (++) [] upreds)

delete_predicates :: BasePredicate p => [[Predicate p]] -> [Int] -> [[Predicate p]]
delete_predicates lpss is = map (\lps -> filter (\p -> notElem (pred_id p) is) lps) lpss

delete_rules :: [RuleExec p] -> [Int] -> [RuleExec p]
delete_rules lrs is = filter (\r -> notElem (rule_id r) is) lrs

get_candidates :: Context p -> Int -> (Predicate p -> Bool) -> [Predicate p]
get_candidates context symbol_id match_func =
   filter match_func $ ((l_context context) !! symbol_id) ++ ((u_context context) !! symbol_id)
   

