
module MSR3.Runtime.Goals where

import Data.IORef

import MSR3.DSL.Base
import MSR3.Compiler.Base
import MSR3.Runtime.Base

type Goals p = [Predicate p]

add_goals :: [Predicate p] -> Goals p -> Goals p
add_goals ps' ps = ps' ++ ps

next_goal :: Goals p -> (Maybe (Predicate p),Goals p)
next_goal (p:ps) = (Just p,ps)
next_goal []     = (Nothing,[])

