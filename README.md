
MSR3 prototype implementation: Beta v0.95

This is a poor man's implementation of MSR3 in Haskell. Currently, it includes the following:

   - Combinator library that micmicks MSR style syntax in Haskell.
   - Mini MSR rule interpreter and runtime system
   - MSR execution control library
   - Small palmful of examples to get started

This prototype is still work in progress, so there are some limitations:

   - Currently does only matching, unification not supported
   - Allows use of existential and forall quantified variables and ungrounded terms in context, but
     still generally untested.. use at own risk. =P
   - No indexing and other MSR optimizations, just uses basic iterations in matching

System requirements:

   - GHC 7 (Glasgow Haskell Compiler) and above
   - Any system which supports GHC

To get started:

   Run example (say Gcd.hs) with GHC interpreter:

       ghci Gcd.hs

   In GHC interpreter shell, create an instance of the rewrite system initial state:

       > cst <- msr_init gcd_eg1 gcd_rules

   Once this is done, you can run the following operations on state 'cst' :

       > msr_show cst          -- Display current rewrite state

       > msr_choices cst       -- Display all choices available from current rewrite state
 
       > msr_choose cst <c>    -- execute rewriting corresponding to choice indexed 'c'

       > msr_run cst <n>       -- execute n steps of rewriting, arbitrarily choosing rewrite choices.

That's all for now, more updates coming soon.
