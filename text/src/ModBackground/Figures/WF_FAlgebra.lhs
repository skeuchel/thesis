%include lhs2TeX.fmt
%include polycode.fmt
%include forall.fmt
%include macros.fmt

< class (f :<: g, FAlg n t a f, FAlg n t a g) =>
< WF_FAlg n t a f g where 
<    wf_algebra :: forall rec (fa :: f t).
<       f_algebra rec (inj fa) == 
<                 f_algebra rec fa
