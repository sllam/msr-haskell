{-# OPTIONS_GHC -XScopedTypeVariables -fth #-}

import MSR3.Misc.Pretty

import MSR3.DSL.Base
import MSR3.DSL.Combinators
import MSR3.DSL.Derive

import MSR3.Runtime.Base
import MSR3.Runtime.Match
import MSR3.Runtime.Rewrite
import MSR3.Runtime.Control

data MGcd = MGcd (Term Int) | MTrue deriving Eq

$(derive_predicate ''MGcd [] True)

gcd_rules :: [Rule MGcd]
gcd_rules = [bang $ mgcd(Literal 0) .=>. mtrue()
            ,let (m :: Term Int) = for_all ()
                 (n :: Term Int) = for_all ()
             in bang $ mgcd(m) /\ mgcd(n) /\ guard(n.>.(Literal 0)) /\ guard(m.>=.n) .=>. mgcd(m.-.n) /\ mgcd(n)
            ]

gcd_eg1 = [mgcd(Literal 10),mgcd(Literal 5),mgcd(Literal 20)]

