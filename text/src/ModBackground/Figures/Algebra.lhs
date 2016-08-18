%include lhs2TeX.fmt
%include polycode.fmt
%include forall.fmt
%include macros.fmt

< type Mixin t f a = (t -> a) -> f r -> a
< class FAlg name t a f where
<       f_algebra : Mixin t f a
