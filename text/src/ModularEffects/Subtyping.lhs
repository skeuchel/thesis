%include lhs2TeX.fmt
%include polycode.fmt
%include forall.fmt
%include macros.fmt

%if False

> {-# OPTIONS -XRankNTypes -XImpredicativeTypes -XTypeOperators -XMultiParamTypeClasses -XFlexibleInstances -XOverlappingInstances -XFlexibleContexts  -XUndecidableInstances #-}

> {-# LANGUAGE ScopedTypeVariables #-}

> module Subtyping where

> import Extensibility hiding (lit, I, B)

%endif


%-------------------------------------------------------------------------------
\subsection{Modularly Composing Mendler-style Algebras}\label{sec:comp}

\name adapts the ``data types \`a la carte'' (DTC) approach for composing 
|f|-algebras to Mendler-style algebras in a straightforward manner.
Definitions are regulated by a number of laws, which are essential
for supporting modular proofs.

\paragraph{Functor and Mendler Algebra Compositions} Signature
functors are composed with the same |:+:| operator as in DTC.  The
composition operator for algebras is similar, but it combines Mendler
algebras instead of |f|-algebras.

%if False

> (::*::) :: Mendler f a -> Mendler g a -> Mendler (f :+: g) a
> alg_1 ::*:: alg_2 = \rec e -> case e of
>                          Inl e_1 -> alg_1 rec e_1
>                          Inr e_2 -> alg_2 rec e_2




Just as in DTC, all the (now Mendler) algebras for a particular
operations are collected as instances of a type class. For instance,

> class Eval f where
>   evalAlg :: Mendler f Value

\noindent where feature composition uses Mendler algebra composition:

> instance (Eval f, Eval g) => Eval (f :+: g) where
>   evalAlg = evalAlg ::*:: evalAlg

and overall evaluation is defined as:

> eval2 :: Eval f => MFix f -> Value
> eval2 = mfold evalAlg

In order to avoid the repeated boilerplate of defining a
new type class for every semantic function and corresponding instance
for |:+:|, \name defines a single generic Coq type class, |FAlg|,
that is indexed by the name of the semantic function.  This class
definition can be found in Figure~\ref{fig:SalCa_Typeclasses} and
subsumes all other algebra classes found in this paper. The paper uses
more specific classes to make a gentler progression for the reader.

\paragraph{Injections and Projections of Functors}
Figure~\ref{fig:sub} shows the \name counterpart of DTC's multi-parameter type
class |:<:|. In addition to the |inj| function for injecting a (sub)functor |f|
into a larger composition |g|, it also features a projection operation (|prj|)
to project it out again. While not shown in the previous section, DTC already
featured projection.

The further use of the |:<:| type class is quite similar to that of DTC:
The |in_t| function builds a new term from the application of
|f| to some subterms.

> in_t :: f (MFix f) -> MFix f
> in_t fexp = \alg -> alg (mfold alg) fexp

%if False

> in_t1 :: Functor f => f (Fix f) -> Fix f
> in_t1 fexp = \alg -> alg (fmap (fold alg) fexp)

%endif

\noindent The combination of |in_t| and |inj| allows us to define
\emph{smart constructors} such as:
% \BD{We need to make the names in the paper and in the framework consistent.}

> inject :: (g :<: f) => g (MFix f) -> MFix f 
> inject gexp = in_t (inj gexp)
>
> lit :: (ArithF :<: f) => Nat -> MFix f
> lit n = inject (Lit n)
>
> blit :: (IfF :<: f) => Bool -> MFix f
> blit b = inject (BLit b)

\vspace{-.5cm}

< cond  :: (IfF :<: f) => MFix f -> MFix f -> MFix f -> MFix f
< cond c e1 e2 = inject (If c e1 e2)


%if False

> cond  :: forall f. (IfF :<: f) => MFix f -> MFix f -> MFix f -> MFix f
> cond c e1 e2 alg = inject ((If :: (MFix f -> MFix f -> MFix f -> IfF (MFix f)))
>                               c e1 e2) alg

%endif

\noindent Expressions are built with the smart constructors and 
used by operations like evaluation: 

< exp :: MFix (ArithF :+: IfF)
< exp = cond (blit True) (lit 3) (lit 2)
<
< > eval2 exp
< 3

The |out_t| function exposes the toplevel functor again:

< out_t :: Functor f => MFix f -> f (MFix f)
< out_t exp = mfold (\rec fr -> fmap (in_t . rec) fr) exp

%if False


> out_t :: forall f. Functor f => MFix f -> f (MFix f)
> out_t exp = mfold (\rec fr -> (fmap :: ((r -> MFix f) -> f r -> f (MFix f))) (\r -> in_t (rec r)) fr) exp
> {-
>   where  
>     g :: (r -> f (Fix f)) -> f r -> f (Fix f)
>     g ffexp = (fmap :: ((f (Fix f) -> Fix f) -> f (f (Fix f)) -> f (Fix f))) 
>                 in_t
>                 ffexp
> -}

%endif

\noindent In combination with |prj|, we can pattern match on particular features.

> project :: (g :<: f, Functor f) => MFix f -> Maybe (g (MFix f))
> project exp = prj (out_t exp)
>
> isLit :: (ArithF :<: f, Functor f) => MFix f -> Maybe Nat
> isLit exp = case project exp of
>     Just (Lit n)  -> Just n
>     Nothing       -> Nothing

%endif