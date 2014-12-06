
module MSR3.Misc.Pretty where

import Data.IORef

data PrettyEnv = PrettyEnv { penv      :: [(IORef (),String)]
                           , new_ids   :: [String] 
                           , delimiter :: String } 

pretty_var :: PrettyEnv -> IORef () -> (PrettyEnv,String)
pretty_var env v =
  case lookup v (penv env) of
   Just s  -> (env,s)
   Nothing -> let (s:new_ids') = new_ids env
                  penv'        = (v,s):(penv env)
              in (PrettyEnv penv' new_ids' (delimiter env),s)
 
class Pretty a where
  pprint :: a -> String
  pretty :: PrettyEnv -> a -> (PrettyEnv,String)

  pprint a =
    let init_penv = PrettyEnv [] (["x","y","z","w","v","m","n","p","q","a","b","c","d","e","f"] ++ (new_vars 1)) ","
    in snd $ pretty init_penv a
    where
      new_vars n = ("v"++(show n)):(new_vars $ n+1)

instance Pretty a => Pretty [a] where
  pretty env (a:as) =
    let (env',s)   = pretty env a
        (env'',ss) = pretty env' as
    in if (length s > 0) && (length ss > 0)
       then (env'',s ++ (delimiter env) ++ ss)
       else if length s > 0 then (env'',s)
                            else (env'',ss)
  pretty env [] = (env,"")

instance (Pretty a,Pretty b) => Pretty (a,b) where
  pretty env (a,b) =
    let (env',as)  = pretty env a
        (env'',bs) = pretty env' b
    in (env'',as ++ (delimiter env) ++ bs)

instance (Pretty a,Pretty b,Pretty c) => Pretty (a,b,c) where
  pretty env (a,b,c) =
    let (env',as)   = pretty env a
        (env'',bs)  = pretty env' b
        (env''',cs) = pretty env'' c
    in (env''',as ++ (delimiter env) ++ bs ++ (delimiter env) ++ cs)

instance (Pretty a,Pretty b,Pretty c,Pretty d) => Pretty (a,b,c,d) where
  pretty env (a,b,c,d) =
    let (env',as)    = pretty env a
        (env'',bs)   = pretty env' b
        (env''',cs)  = pretty env'' c
        (env'''',ds) = pretty env''' d
    in (env'''',as ++ (delimiter env) ++ bs ++ (delimiter env) ++ cs ++ (delimiter env) ++ ds)


