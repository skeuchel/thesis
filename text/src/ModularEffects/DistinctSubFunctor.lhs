%include lhs2TeX.fmt
%include polycode.fmt
%include forall.fmt
%include macros.fmt

<  class (Functor h, f :<: h, g :<: h) => 
<  DistinctSubFunctor f g h where 
<    inj_discriminate :: forall a (fe :: f a) 
<                     (ge :: g a). inj fe <> inj ge
