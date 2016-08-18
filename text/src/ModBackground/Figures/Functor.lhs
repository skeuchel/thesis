%include lhs2TeX.fmt
%include polycode.fmt
%include forall.fmt
%include macros.fmt

< class Functor f where
<   fmap :: (a -> b) -> (f a -> f b)
<   fmap_id :: fmap id == id
<   fmap_fusion :: forall g h. 
<          fmap h . fmap g == fmap (h . g)
