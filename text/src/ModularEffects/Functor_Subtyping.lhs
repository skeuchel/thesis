%include lhs2TeX.fmt
%include polycode.fmt
%include forall.fmt
%include macros.fmt

< class f :<: g where
<   inj      :: f a -> g a 
<   prj      :: g a -> Maybe (f a)
<   inj_prj  :: prj ga == Just fa -> 
<            ga == inj fa 
<   prj_inj  :: prj . inj == Just 
