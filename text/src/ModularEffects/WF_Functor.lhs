%include lhs2TeX.fmt
%include polycode.fmt
%include forall.fmt
%include macros.fmt

<  class (Functor f, Functor g, f :<: g) =>
<   WF_Functor f g where
<    wf_functor :: forall a b (h :: a -> b).
<        fmap h . inj == inj . fmap h
