{-# OPTIONS_GHC -XMultiParamTypeClasses -XFunctionalDependencies -XFlexibleInstances -XExistentialQuantification -XGADTs -XBangPatterns -XTypeSynonymInstances -fth #-}

import MSR3.Misc.Pretty

import MSR3.DSL.Base
import MSR3.DSL.Combinators
import MSR3.DSL.Derive

import MSR3.Runtime.Base
import MSR3.Runtime.Match
import MSR3.Runtime.Rewrite
import MSR3.Runtime.Control

import BlinkyBlockBase hiding (neighbor,vacant,neighborcount,setcolor,tap)

data BBCyclePredicate = Color (Term CAtom) (Term Color)
                      | BBBase BBPredicate deriving Eq

$(derive_predicate ''BBCyclePredicate ["BBBase"] True)

cycle_rules :: [Rule BBCyclePredicate]
cycle_rules = [let x = for_all ()
                   y = for_all ()
                   s = for_all ()
                   n = for_all ()
               in bang $ neighbor(x,y,s) /\ color(x,n) /\ color(y,n) .=>. setcolor(x,n.+.(Literal 1)) /\ color(x,n.+.(Literal 1)) /\ color(y,n)]

c1 = Literal $ CAtom "c1"
c2 = Literal $ CAtom "c2"
c3 = Literal $ CAtom "c3"
c4 = Literal $ CAtom "c4"
c5 = Literal $ CAtom "c5"

red = Literal 1
blue = Literal 2
green = Literal 3

cycle_eg1 :: [Predicate BBCyclePredicate]
cycle_eg1 = [bang $ neighbor(c1,c2,Literal Top),bang $ neighbor(c2,c1,Literal Bottom)
            ,bang $ neighbor(c2,c3,Literal North),bang $ neighbor(c3,c2,Literal South)
            ,bang $ neighbor(c2,c4,Literal East),bang $ neighbor(c4,c2,Literal West)
            ,bang $ neighbor(c4,c5,Literal East),bang $ neighbor(c5,c4,Literal West)
            ,color(c1,red),color(c2,red),color(c3,red),color(c4,red),color(c5,red)]


{-
instance BasePredicate BBCyclePredicate where
  symbol (Color _ _) = Literal "Color"
  symbol (BBBase p)  = symbol p
  sym_id (Color _ _) = 5
  sym_id (BBBase p)  = sym_id p
  num_of_preds _     = 6

instance Show BBCyclePredicate where
  show (Color x c) = "Color(" ++ (show x) ++ "," ++ (show c) ++ ")"
  show (BBBase p)  = show p

instance Pretty BBCyclePredicate where
  pretty env (Color x c) = 
    let (env',args) = pretty env (x,c)
    in (env',"Color(" ++ args ++ ")")
  pretty env (BBBase bb) = pretty env bb

instance HasTerm BBCyclePredicate where
  is_ground (Color x c) = (is_ground x) && (is_ground c)
  is_ground (BBBase bb) = is_ground bb
  apply env (Color x c) = Color (apply env x) (apply env c)
  apply env (BBBase bb) = BBBase (apply env bb)

instance Match BBCyclePredicate where
  match env (Color x s) (Color x' s') =
    case match env x x' of
     Just env' -> match env' s s'
     Nothing   -> Nothing
  match env (BBBase bb) (BBBase bb') =
    match env bb bb'
  match _ _ _ = Nothing
-}


{-
neighbor :: (Term CAtom,Term CAtom,Term Facing) -> Predicate BBCyclePredicate
neighbor (x,y,s) = predicate $ BBBase (Neighbor x y s)

vacant :: (Term CAtom,Term Facing) -> Predicate BBCyclePredicate
vacant (x,s) = predicate $ BBBase (Vacant x s)

neighborCount :: (Term CAtom,Term Int) -> Predicate BBCyclePredicate
neighborCount (x,n) = predicate $ BBBase (NeighborCount x n)

setColor :: (Term CAtom,Term Color) -> Predicate BBCyclePredicate
setColor (x,c) = predicate $ BBBase (SetColor x c)

tap :: Term CAtom -> Predicate BBCyclePredicate
tap x = predicate $ BBBase (Tap x) 

color :: (Term CAtom,Term Color) -> Predicate BBCyclePredicate
color (x,c) = predicate $ Color x c
-}
