{-# OPTIONS_GHC -XMultiParamTypeClasses -XFunctionalDependencies -XFlexibleInstances -XExistentialQuantification -XGADTs -XBangPatterns -XTypeSynonymInstances -fth #-}

module BlinkyBlockBase where

import MSR3.Misc.Pretty

import MSR3.DSL.Base
import MSR3.DSL.Combinators
import MSR3.DSL.Derive

import MSR3.Runtime.Base
import MSR3.Runtime.Match

import Data.IORef
import qualified Data.ByteString.Lazy.Char8 as BS


data CAtom  = CAtom String deriving (Show,Read,Eq)
data Facing = Top | Bottom | North | South | East | West deriving (Show,Read,Eq)
type Color  = Int

data BBPredicate = Neighbor (Term CAtom) (Term CAtom) (Term Facing) 
                 | Vacant (Term CAtom) (Term Facing)
                 | NeighborCount (Term CAtom) (Term Int)
                 | SetColor (Term CAtom) (Term Color)
                 | Tap (Term CAtom) deriving Eq

$(derive_predicate ''BBPredicate [] True)

bb_count_neighbor_rules :: [Rule BBPredicate]
bb_count_neighbor_rules = [let x = for_all ()
                           in bang $ neighbor(x,wild,wild) .=>. neighborcount(x,Literal 1)
                          ,let x = for_all ()
                               n = for_all ()
                               m = for_all ()
                           in bang $ neighborcount(x,n),neighborcount(x,m) .=>. neighborcount(x,n.+.m)]

bb_vacant_rules :: [Rule BBPredicate]
bb_vacant_rules = [let x = for_all ()
                       y = for_all ()
                       f = for_all ()
                   in bang $ neighbor(x,y,f) /\ vacant(x,f) .=>. neighbor(x,y,f)]

{-
instance BasePredicate BBPredicate where
  symbol (Neighbor _ _ _) = Literal "Neighbor"
  symbol (Vacant _ _)     = Literal "Vacant"
  symbol (NeighborCount _ _) = Literal "NeighborCount"
  symbol (SetColor _ _) = Literal "SetColor"
  symbol (Tap _) = Literal "Tap"
  sym_id (Neighbor _ _ _) = 0
  sym_id (Vacant _ _)     = 1
  sym_id (NeighborCount _ _) = 2
  sym_id (SetColor _ _) = 3
  sym_id (Tap _) = 4
  num_of_preds _ = 5

instance Show BBPredicate where
  show (Neighbor x y s) = "Neighbor(" ++ (show x) ++ "," ++ (show y) ++ "," ++ (show s) ++ ")"
  show (Vacant x s) = "Vacant(" ++ (show x) ++ "," ++ (show s) ++ ")"
  show (NeighborCount x n) = "NeighborCount(" ++ (show x) ++ "," ++ (show n) ++ ")"
  show (SetColor x c) = "SetColor(" ++ (show x) ++ "," ++ (show c) ++ ")"
  show (Tap x) = "Tap(" ++ (show x) ++ ")"

instance Pretty BBPredicate where
  pretty env (Neighbor x y s) = 
    let (env',args) = pretty env (x,y,s)
    in (env',"Neighbor(" ++ args ++ ")")
  pretty env (Vacant x s) = 
    let (env',args) = pretty env (x,s)
    in (env',"Vacant(" ++ args ++ ")")
  pretty env (NeighborCount x n) = 
    let (env',args) = pretty env (x,n)
    in (env',"NeighborCount(" ++ args ++ ")")
  pretty env (SetColor x c) = 
    let (env',args) = pretty env (x,c)
    in (env',"SetColor(" ++ args ++ ")")
  pretty env (Tap x) = 
    let (env',args) = pretty env x
    in (env',"Tap(" ++ args ++ ")")

instance HasTerm BBPredicate where
  is_ground (Neighbor x y s) = (is_ground x) && (is_ground y) && (is_ground s)
  is_ground (Vacant x s)     = (is_ground x) && (is_ground s)
  is_ground (NeighborCount x n) = (is_ground x) && ( is_ground n)
  is_ground (SetColor x c)   = (is_ground x) && (is_ground c)
  is_ground (Tap x) = is_ground x
  apply env (Neighbor x y s) = Neighbor (apply env x) (apply env y) (apply env s)
  apply env (Vacant x s) = Vacant (apply env x) (apply env s)
  apply env (NeighborCount x n) = NeighborCount (apply env x) (apply env n)
  apply env (SetColor x c) = SetColor (apply env x) (apply env c)
  apply env (Tap x) = Tap (apply env x)

instance Match BBPredicate where
  match env (Neighbor x y s) (Neighbor x' y' s') = 
    case match env x x' of
     Just env' -> case match env' y y' of
                   Just env'' -> match env'' s s'
                   Nothing    -> Nothing
     Nothing   -> Nothing
  match env (Vacant x s) (Vacant x' s') =
    case match env x x' of
     Just env' -> match env' s s'
     Nothing   -> Nothing
  match env (NeighborCount x n) (NeighborCount x' n') =
    case match env x x' of
     Just env' -> match env' n n'
     Nothing   -> Nothing 
  match env (SetColor x c) (SetColor x' c') =
    case match env x x' of
     Just env' -> match env' c c'
     Nothing   -> Nothing 
  match env (Tap x) (Tap x') = match env x x'
  match env _ _ = Nothing
-}
