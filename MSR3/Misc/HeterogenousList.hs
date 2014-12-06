{-# OPTIONS_GHC -XMultiParamTypeClasses -XFunctionalDependencies -XFlexibleInstances #-}

module MSR3.Misc.HeterogenousList where

class HeterogenousList as h t | as -> h t where
  hehead :: as -> h
  hetail :: as -> t

instance HeterogenousList (a,as) a as where
  hehead (a,_)  = a
  hetail (_,as) = as

instance HeterogenousList () () () where
  hehead _ = ()
  hetail _ = ()

(%) :: HeterogenousList as h t => a -> as -> (a,as)
(%) a as = (a,as)
   
infixr 7 %

