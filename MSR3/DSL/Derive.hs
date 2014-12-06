{-# OPTIONS_GHC -fth -XMultiParamTypeClasses -XFunctionalDependencies -XFlexibleInstances -XExistentialQuantification -XGADTs -XBangPatterns -XTypeSynonymInstances -XDeriveDataTypeable -XDeriveFunctor -XDeriveFoldable -XDeriveTraversable -XScopedTypeVariables #-}

module MSR3.DSL.Derive where

import Data.Char

import Language.Haskell.TH
import Language.Haskell.TH.Syntax
import Control.Monad

import MSR3.DSL.Base
import MSR3.DSL.Combinators

import MSR3.Runtime.Base
import qualified MSR3.Runtime.Match as M

import MSR3.Misc.Pretty

derive_predicate t assumed_derives gen_wrapper_funcs = do
  { show_instance   <- derive_predicate_show t assumed_derives
  ; pretty_instance <- derive_predicate_pretty t assumed_derives
  ; base_pred_instance <- derive_predicate_base_predicate t assumed_derives
  ; has_term_instance <- derive_predicate_has_term t assumed_derives
  ; match_instance <- derive_predicate_match t assumed_derives
  ; wrapper_funcs <- if gen_wrapper_funcs
                     then derive_predicate_wrappers t assumed_derives
                     else return []
  ; return $ [show_instance,pretty_instance,base_pred_instance,has_term_instance,match_instance] ++ wrapper_funcs }

match_assumed_derives name (data_name:data_names) =
    if nameBase name == data_name
    then True
    else match_assumed_derives name data_names 
match_assumed_derives _ [] = False

derive_predicate_show t assumed_derives = do
  { TyConI (DataD _ _ _ constructors _)  <-  reify t
  ; let showClause (NormalC name fields) =
           if not $ match_assumed_derives name assumed_derives
           then do { let constructorName = nameBase name
                   ; (pats,vars) <- genPE (length fields) "x"
                   ; let f []       = [| "" |]
                         f [v]      = [| show $v |]
                         f (v:vars) = [| show $v ++ "," ++ $(f vars) |]
                   ; clause [conP name pats]                                 -- (A x1 x2)
                            (normalB [| constructorName ++ "(" ++ $(f vars) ++ ")" |]) []  -- "A "++show x1++" "++show x2
                   }
           else do { let constructorName = nameBase name
                   ; ([pat],[var]) <- genPE 1 "x"
                   ; clause [conP name [pat]]                                 -- (A x1 x2)
                            (normalB [| show $var |]) []  -- "A "++show x1++" "++show x2
                   }
  ; showbody <- mapM showClause constructors
  ; return $ InstanceD [] (AppT (ConT $ mkName "Show") (ConT t)) [FunD (mkName "show") showbody]
  }

derive_predicate_pretty t assumed_derives = do
  { TyConI (DataD _ _ _ constructors _)  <-  reify t
  ; let showClause (NormalC name fields) = 
           if not $ match_assumed_derives name assumed_derives 
           then do { let constructorName = nameBase name
                   ; (pats,vars)         <- genPE (length fields) "x"
                   ; (env_pat:env_pats,env_vars) <- genPE (1 + length fields) "env"
                   ; (s_pats,s_vars)     <- genPE (length fields) "s"
                   ; let f []       = [| "" |]
                         f [v]      = [| $v |]
                         f (v:vars) = [| $v ++ "," ++ $(f vars) |]
                         gen_let_daisies _ [env_var] _ _ cons = [| ($env_var,$cons) |]
                         gen_let_daisies (env_pat:env_pats) (env_var:env_vars) (var:vars) (s_pat:s_pats) cons = 
                             letE [valD (tupP [env_pat,s_pat]) (normalB [| pretty $env_var $var |]) []] 
                                  (gen_let_daisies env_pats env_vars vars s_pats cons)
                   ; clause [env_pat,conP name pats]                                 
                            (normalB (gen_let_daisies (env_pats ++ [env_pat]) env_vars vars s_pats ([| constructorName ++ "(" ++ $(f s_vars) ++ ")" |]))) []
                   }
           else do { let constructorName = nameBase name
                   ; ([env_pat],[env_var]) <- genPE 1 "env"
                   ; ([p_pat],[p_var]) <- genPE 1 "p"
                   ; clause [env_pat,conP name [p_pat]]    
                            (normalB [| pretty $env_var $p_var |]) [] 
                   }
  ; showbody <- mapM showClause constructors
  ; return $ InstanceD [] (AppT (ConT $ mkName "Pretty") (ConT t  )) [FunD (mkName "pretty") showbody]
  }

derive_predicate_base_predicate t assumed_derives = do
  { TyConI (DataD _ _ _ constructors _)  <-  reify t
  ; let symbolClause (NormalC name fields) =
           if not $ match_assumed_derives name assumed_derives
           then do { let constructorName = nameBase name
                   ; clause [conP name (replicate (length fields) $ return WildP)]
                            (normalB [| Literal constructorName |]) [] }
           else do { let constructorName = nameBase name
                   ; ([p_pat],[p_var]) <- genPE 1 "p"
                   ; clause [conP name [p_pat]]
                            (normalB [| symbol $p_var |]) [] }
  ; let symIdClauses ((mb,NormalC name fields):constructors) n = do
          { let clause_pat = case mb of
                              Just name' -> conP name' [conP name (replicate (length fields) $ return WildP)]
                              Nothing    -> conP name (replicate (length fields) $ return WildP)
          ; c  <- clause [clause_pat] (normalB $ return (LitE (IntegerL $ toInteger n))) []
          ; cs <- symIdClauses constructors (n+1) 
          ; return $ c:cs }
        symIdClauses [] _ = return []
  ; symbol_body <- mapM symbolClause constructors
  ; all_constructors <- unroll_constructors Nothing constructors 
  ; sym_id_body <- symIdClauses all_constructors 0
  ; let num = length all_constructors
  ; num_of_pred_body <- clause [return WildP] (normalB $ return (LitE (IntegerL $ toInteger num))) []
  ; return $ InstanceD [] (AppT (ConT $ mkName "BasePredicate") (ConT t  )) [FunD (mkName "symbol") symbol_body
                                                                            ,FunD (mkName "sym_id") sym_id_body
                                                                            ,FunD (mkName "num_of_preds") [num_of_pred_body]]
  }
  where
    unroll_constructors mb ((NormalC name fields):constructors) =
       if not $ match_assumed_derives name assumed_derives
       then do { cons <- unroll_constructors mb constructors
               ; return $ (mb,NormalC name fields):cons }
       else case fields of
             (_,ConT t):_ -> do { TyConI (DataD _ _ _ constructors' _)  <-  reify t
                                ; cons' <- unroll_constructors (Just name) constructors'
                                ; cons  <- unroll_constructors mb constructors
                                ; return $ cons' ++ cons }
             [] -> unroll_constructors mb constructors
    unroll_constructors _ [] = return []

derive_predicate_has_term t assumed_derives = do
  { TyConI (DataD _ _ _ constructors _)  <-  reify t
  ; let isGroundClause (NormalC name fields) =
           if not $ match_assumed_derives name assumed_derives
           then do { let constructorName = nameBase name
                   ; if length fields > 0
                     then do { (pats,vars) <- genPE (length fields) "x"
                             ; let f [v]      = [| is_ground $v |]
                                   f (v:vars) = [| (is_ground $v) && $(f vars) |]
                             ; clause [conP name pats] (normalB [| $(f vars) |]) [] }
                     else clause [conP name []] (normalB [| True |]) []  
                   }
           else do { ([pat],[var]) <- genPE 1 "x"
                   ; clause [conP name [pat]] (normalB [| is_ground $var |]) []  
                   }
  ; let applyClause (NormalC name fields) =
           if not $ match_assumed_derives name assumed_derives
           then do { let constructorName = nameBase name
                   ; ([env_pat],[env_var]) <- genPE 1 "env"
                   ; (pats,vars) <- genPE (length fields) "x"
                   ; let f _ [] exp = exp
                         f env_var (v:vars) exp = f env_var vars [| $exp (apply $env_var $v) |]
                   ; clause [env_pat,conP name pats]                              
                            (normalB (f env_var vars (return (ConE $ mkName constructorName)) ) ) []  
                   }
           else do { let constructorName = nameBase name
                   ; ([env_pat],[env_var]) <- genPE 1 "env"
                   ; ([pat],[var]) <- genPE 1 "p"
                   ; clause [env_pat,conP name [pat]]              
                            (normalB [| $(return $ ConE (mkName constructorName)) (apply $env_var $var) |]) []  
                   }
  ; is_ground_body <- mapM isGroundClause constructors
  ; apply_body     <- mapM applyClause constructors
  ; return $ InstanceD [] (AppT (ConT $ mkName "HasTerm") (ConT t)) [FunD (mkName "is_ground") is_ground_body
                                                                    ,FunD (mkName "apply") apply_body]
  }

derive_predicate_match t assumed_derives = do
  { TyConI (DataD _ _ _ constructors _)  <-  reify t
  ; let matchClause (NormalC name fields) = 
           if not $ match_assumed_derives name assumed_derives 
           then do { let constructorName = nameBase name
                   ; if length fields > 0
                     then do { (pats,vars)   <- genPE (length fields) "x"
                             ; (pats',vars') <- genPE (length fields) "y"
                             ; (env_pat:env_pats,env_vars) <- genPE (length fields) "env"
                             ; let gen_case_daisies _ [env_var] [var] [var'] = [| M.match $env_var $var $var' |]
                                   gen_case_daisies (env_pat:env_pats) (env_var:env_vars) (var:vars) (var':vars') = 
                                         caseE ([| M.match $env_var $var $var' |])  
                                               [match (conP (mkName "Just") [env_pat]) (normalB (gen_case_daisies env_pats env_vars vars vars')) []
                                               ,match (conP (mkName "Nothing") []) (normalB (conE $ mkName "Nothing")) []]
                             ; clause [env_pat,conP name pats,conP name pats']                            
                                      (normalB (gen_case_daisies env_pats env_vars vars vars')) []
                             }
                     else do { ([env_pat],[env_var]) <- genPE 1 "env"
                             ; clause [env_pat,conP name [],conP name []] (normalB [| Just $env_var |]) [] }
                   }
           else do { let constructorName = nameBase name
                   ; ([env_pat],[env_var]) <- genPE 1 "env"
                   ; ([p_pat],[p_var])   <- genPE 1 "p"
                   ; ([p_pat'],[p_var']) <- genPE 1 "q"
                   ; clause [env_pat,conP name [p_pat],conP name [p_pat']]    
                            (normalB [| M.match $env_var $p_var $p_var' |]) [] 
                   }
  ; match_body <- mapM matchClause constructors
  ; last_body  <- clause [return WildP,return WildP, return WildP] (normalB $ conE (mkName "Nothing")) []
  ; return $ InstanceD [] (AppT (ConT $ mkName "Match") (ConT t  )) [FunD (mkName "match") (match_body ++ [last_body])]
  }

derive_predicate_wrappers t assumed_derives = do
  { TyConI (DataD _ _ _ constructors _)  <-  reify t
  ; let wrapper_func (mb,NormalC name fields) = do
          { (pats,vars) <- genPE (length fields) "x"
          ; let pred_cons vars = case mb of
                                  Just name' -> [| $(return $ ConE name') $(pred_cons' vars (return $ ConE name)) |]
                                  Nothing    -> pred_cons' vars (return $ ConE name)
                pred_cons' (var:vars) exp = pred_cons' vars [| $exp $var |]
                pred_cons' [] exp = exp
          ; func_clause <- clause [tupP pats] (normalB [| predicate $(pred_cons vars) |]) []
          ; return $ FunD (mkName $ map toLower (nameBase name)) [func_clause] }
  ; all_constructors <- unroll_constructors Nothing constructors
  ; mapM wrapper_func all_constructors
  } 
  where
    unroll_constructors mb ((NormalC name fields):constructors) =
       if not $ match_assumed_derives name assumed_derives
       then do { cons <- unroll_constructors mb constructors
               ; return $ (mb,NormalC name fields):cons }
       else case fields of
             (_,ConT t):_ -> do { TyConI (DataD _ _ _ constructors' _)  <-  reify t
                                ; cons' <- unroll_constructors (Just name) constructors'
                                ; cons  <- unroll_constructors mb constructors
                                ; return $ cons' ++ cons }
             [] -> unroll_constructors mb constructors
    unroll_constructors _ [] = return []

-- Generate n unique variables and return them in form of patterns and expressions

data Dummy = Dummy
data T2 a = T2 a

genPE n x = do { 
  ; ids <- replicateM n (newName x)
  ; return (map varP ids, map varE ids) }


