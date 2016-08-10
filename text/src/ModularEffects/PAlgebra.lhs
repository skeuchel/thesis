%include lhs2TeX.fmt
%include polycode.fmt
%include forall.fmt
%include macros.fmt

<  class (Functor f, Functor g, f :<: g) => 
<        PAlg name f g a where
<             p_algebra ::  Algebra f a
<             proj_eq   ::  forall e. p_1 (p_algebra e) == 
<                           in_t (inj (fmap p_1 e))
