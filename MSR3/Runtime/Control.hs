 
module MSR3.Runtime.Control where

import Data.IORef

import MSR3.Misc.Pretty

import MSR3.DSL.Base
import MSR3.Compiler.Base 

import MSR3.Runtime.Base
import MSR3.Runtime.Goals
import MSR3.Runtime.Context
import MSR3.Runtime.Match
import MSR3.Runtime.Rewrite

---------------------------------------------
 
data ControlState p = ControlState { current_goals   :: IORef (Goals p)
                                   , current_context :: IORef (Context p)
                                   , current_choices :: IORef [(RuleMatch p,Goals p,Context p)] }

msr_init :: (Eq p, Match p, HasTerm p, BasePredicate p) => [Predicate p] -> [Rule p] -> IO (ControlState p)
msr_init preds rules = do
   { let (goals,context) = init_context preds rules
         choices = rewrite_step (goals,context)
   ; goals_ref   <- newIORef goals
   ; context_ref <- newIORef context
   ; choices_ref <- newIORef choices
   ; return $ ControlState goals_ref context_ref choices_ref }

msr_show :: (Eq p, Match p, HasTerm p, BasePredicate p, Pretty p) => ControlState p -> IO ()
msr_show cstate = do
   { context <- readIORef $ current_context cstate
   ; putStrLn $ pprint context }

msr_choices :: (Eq p, Match p, HasTerm p, BasePredicate p, Pretty p) => ControlState p -> IO ()
msr_choices cstate = do
   { current <- readIORef $ current_context cstate
   ; choices <- readIORef $ current_choices cstate
   ; if length choices > 0
     then format_rule_match current 0 choices
     else putStrLn "No choices available, state is terminal." }
   where
     format_rule_match current n ((rmt,goals,context):choices) = do
        { let rule_instance = apply (matching_env rmt) (rule_actual rmt)
              lhs_preds = filter (\p -> elem (pred_id p) (lhs_matched rmt)) $ (foldl (++) [] (l_context current)) ++ (foldl (++) [] (u_context current))
              s = "===== Choice " ++ (show n) ++ " =====\n" ++ "Rule Instance: " ++ (pprint rule_instance) ++ "\n" ++ "Matched predicates: " ++ (pprint lhs_preds) ++ "\n"
        ; putStrLn s 
        ; format_rule_match current (n+1) choices }
     format_rule_match _ _ [] = return ()

msr_choose :: (Eq p, Match p, HasTerm p, BasePredicate p, Pretty p) => ControlState p -> Int -> IO ()
msr_choose cstate choice_index = do
   { choices <- readIORef $ current_choices cstate
   ; if choice_index < length choices
     then do { let (rmt,new_goals,new_context) = choices !! choice_index
                   new_choices = rewrite_step (new_goals,new_context)      
             ; writeIORef (current_goals cstate) new_goals
             ; writeIORef (current_context cstate) new_context
             ; writeIORef (current_choices cstate) new_choices 
             ; let rule_instance = apply (matching_env rmt) (rule_actual rmt)
             ; putStrLn $ "Applied rule instance: " ++ (pprint rule_instance) ++ "\n" }
     else putStrLn $ "Choice " ++ (show choice_index) ++ " does not exist! Try another!" }

msr_run :: (Eq p, Match p, HasTerm p, BasePredicate p, Pretty p) => ControlState p -> Int -> IO ()
msr_run cstate 0 = putStrLn "Done!"
msr_run cstate n = do
   { choices <- readIORef $ current_choices cstate
   ; if length choices > 0
     then do { msr_choose cstate 0
             ; msr_run cstate (n-1) }
     else putStrLn "Done!" }


