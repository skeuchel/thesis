%include lhs2TeX.fmt
%include forall.fmt
%include polycode.fmt
%include Formatting.fmt
%include macros.fmt

%if False

> {-# LANGUAGE TypeFamilies #-}
> {-# LANGUAGE ScopedTypeVariables #-}
> {-# LANGUAGE TypeOperators #-}
> {-# LANGUAGE MultiParamTypeClasses #-}
> {-# LANGUAGE FlexibleInstances #-}
> {-# LANGUAGE FlexibleContexts #-}
>
> module DatatypesALaCarte where
>
> import Control.Arrow

%endif

%-------------------------------------------------------------------------------

\section{Datatypes \`a la Carte}\label{sec:mod:datatypesalacarte}

%The  (DTC) approach \cite{swierstra2008dtc} is a solution of
%the expression problem in the Haskell programming language.

This section reviews the core ideas behind \emph{Datatypes \`a la Carte} (DTC)
\cite{swierstra2008dtc}, a well-known Haskell solution to the expression
problem, and presents the infrastructure for writing modular functions over
modular datatypes.

%% In the next section we discuss our adapted approach that works in the restricted
%% Coq setting.


\subsection{Fixed-points}

\begin{figure}[t]
\fbox{
  \begin{minipage}{0.98\columnwidth}

> data Exp  =  Lit  Int   | Add Exp Exp
>           |  BLit Bool  | If Exp Exp Exp

  \hrule

> data ArithF  exp = LitF  Int   | AddF exp exp
> data BoolF   exp = BLitF Bool  | IfF exp exp exp

  \end{minipage}
}
\caption{Arithmetic and logical expressions}
\label{fig:mod:arithlogicexpressions}
\end{figure}

The main idea behind DTC is to open the recursion of datatypes and model the
fixed point explicitly. Consider the monolithic datatype |Exp| for simple
arithmetic and logical expressions in Figure \ref{fig:mod:arithlogicexpressions}
(top). Abstracting over the recursive positions of |Exp| yields a
\emph{signature functor} that we can then split up into functors |ArithF| and
|BoolF| -- shown in Figure \ref{fig:mod:arithlogicexpressions} (bottom) -- to
capture the signature of features in isolation.

%-------------------------------------------------------------------------------

\begin{figure}[t]
\fbox{
  \begin{minipage}{0.98\columnwidth}

> data FixDTC  f      =  InDTC { outDTC :: f (FixDTC f) }
> data (:+:)   f g a  =  Inl (f a) | Inr (g a)

  \end{minipage}
}
\caption{Datatypes \`a la Carte fixed-point}
\label{fig:mod:fixdtc}
\end{figure}

The type-level fixed-point combinator |FixDTC| in Figure \ref{fig:mod:fixdtc}
creates a recursive datatype from a signature. For example |ArithDTC| is a type
that features only arithmetic expressions.

> type ArithDTC = FixDTC ArithF

Different features can be combined modularly by taking the coproduct |(:+:)| of
the signatures before taking the fixed point. For example, taking the fixed-point
of the coproduct of |ArithF| and |BoolF|

> type ExpDTC = FixDTC (ArithF :+: BoolF)

essentially\footnote{Which due to laziness in Haskell means modulo non-termination.} yields a datatype that
is isomorphic to the monolithic datatype |Exp| from Figure
\ref{fig:mod:arithlogicexpressions} (top).

%-------------------------------------------------------------------------------

\subsection{Automated Injections}\label{ssec:mod:smartconstructors}

\begin{figure}[t]
\fbox{
  \begin{minipage}{0.98\columnwidth}
    \begin{spec}
      class f :<: g where
        inj      ::  f a -> g a
        prj      ::  g a -> Maybe (f a)
        inj_prj  ::  forall a (ga :: g a) (fa :: f a).
                       prj ga = Just fa -> ga = inj fa
        prj_inj  ::  forall a (fa :: f a).
                       prj (inj fa) = Just fa

      inject :: (f :<: g) => f (FixDTC g) -> FixDTC g
      inject x = InDTC (inj x)
      project :: (f :<: g) => FixDTC g -> Maybe (f (FixDTC g))
      project x = prj (outDTC x)
    \end{spec}

    \hrule \vspace{2mm}

    \begin{spec}
      instance (f :<: f) where
        inj = id
      instance (f :<: g) => (f :<: (g :+:h)) where
        inj = Inl . inj
      instance (f :<: h) => (f :<: (g :+:h)) where
        inj = Inr . inj
    \end{spec}
  \end{minipage}
}
\caption{Sub-functor relation}

\label{fig:subfunctorrelation}
\end{figure}

Combining signatures makes writing expressions difficult. For example the
arithmetic expression |3 + 4| is represented as the term

> ex1 :: FixDTC (ArithF :+: BoolF)
> ex1 = InDTC (Inl   (AddF
>                       (InDTC (Inl (LitF 3)))
>                       (InDTC (Inl (LitF 4)))))

Writing such expressions manually is too cumbersome and unreadable. Moreover, if
we extend the datatype with a new signature, other injections are needed.


%if False
\begin{code}
  class f :<: g where
    inj :: f a -> g a
    prj :: g a -> Maybe (f a)
  inject :: (f :<: g) => f (FixDTC g) -> FixDTC g
  inject x = InDTC $ inj x
  project :: (f :<: g) => FixDTC g -> Maybe (f (FixDTC g))
  project x = prj $ outDTC x
\end{code}
%endif

To facilitate writing expressions and make reuse possible we use the sub-functor
|f :<: g| relation shown in Figure \ref{fig:subfunctorrelation} (top). The
member function |inj| injects the sub-functor |f| into the super-functor |g|. In
our case we need injections of functors into coproducts which are automated
using type class machinery.\footnote{Coq's type-class mechanism performs
  backtracking. These instances do not properly work in Haskell. See
  \cite{swierstra2008dtc} for a partial solution.} The |prj| member function is
a partial inverse of |inj|. With it we can test if a specific sub-functor was
used to build the top layer of a value. This operation fails if another
sub-functor was used. The type class also includes the laws |inj_prj| and
|prj_inj| that witness the partial inversion.\footnote{Using a hypothetical
  dependently-typed Haskell syntax.}

The |inject| function is a variation of |inj| that additionally applies the
constructor of the fixed-point type |FixDTC|. Using the sub-functor relation we
can define smart constructors for arithmetic expressions

> lit :: (ArithF :<: expf) => Int -> FixDTC expf
> lit i = inject (LitF i)
> add :: (ArithF :<: expf) => FixDTC expf -> FixDTC expf -> FixDTC expf
> add a b = inject (AddF a b)

\noindent that construct terms of any abstract super-functor |expf| of
|ArithF|. This is essential for modularity and reuse. We can define terms using
the smart-constructors, but constructing a value of a specific fixed-point
datatype is delayed. With these smart constructors the above example term
becomes

> ex1' :: (ArithF :<: expf) => FixDTC expf
> ex1' = lit 3 `add` lit 4

The |project| function is a variation of |prj| that strips the constructor of
the fixed-point type |FixDTC|. Similarly to injections, we can automate
projections for coproducts by adding corresponding definitions to the instances
above.

%-------------------------------------------------------------------------------

\subsection{Semantic Functions}\label{sec:dtc:semanticfunctions}

In this section we define evaluation for arithmetic and boolean
expressions modularly. We use another modular datatype to represent
values. Its signatures and smart-constructors are given in Figure
\ref{fig:modularvalues}. The signature |StuckValueF| represents a
sentinel value to signal type errors during evaluation.

\begin{figure}[t]
\fbox{
\hspace{-5pt}\begin{minipage}{1\columnwidth}

> data IntValueF    val = VInt   Int
> data BoolValueF   val = VBool  Bool
> data StuckValueF  val = VStuck
>
> vint :: (IntValueF :<: valf) => Int -> FixDTC valf
> vint i = inject (VInt i)
> vbool :: (BoolValueF :<: valf) => Bool -> FixDTC valf
> vbool b = inject (VBool b)
> vstuck :: (StuckValueF :<: valf) => FixDTC valf
> vstuck = inject VStuck

\end{minipage}
}
\caption{Modular value datatype}

\label{fig:modularvalues}
\end{figure}

If |f| is a functor, we can fold over any value of type |FixDTC f| as
follows:

> type Algebra f a = f a -> a
> foldDTC :: Functor f => Algebra f a -> FixDTC f -> a
> foldDTC f (InDTC x) = f (fmap (foldDTC f) x)

An \emph{algebra} specifies one step of recursion that turns a value of type |(f
a)| into the desired result type |a|. The \emph{fold} uniformly applies this
operation to an entire term. All semantic functions over a modular datatype are
written as folds of an algebra.

Using type classes, we can define and assemble algebras in a modular
fashion. The class |FAlgebra| in Figure \ref{fig:falgebraclass}
carries an algebra for a functor |f| and carrier type |a|. It is
additionally indexed over a parameter |name| to allow definitions of
distinct functions with the same carrier. For instance, functions for
calculating the size and the height of a term can both be defined
using |Int| as the carrier.

\begin{figure}[t]
\fbox{
\hspace{-5pt}\begin{minipage}{1\columnwidth}

> class FAlgebra name f a where
>   f_algebra   :: name -> Algebra f a
>
> algebraPlus ::  Algebra f a -> Algebra g a -> Algebra (f :+: g) a
> algebraPlus f g (Inl a)  = f a
> algebraPlus f g (Inr a)  = g a
>
> instance  (FAlgebra name f a, FAlgebra name g a) =>
>             FAlgebra name (f :+: g) a where
>   f_algebra name =  algebraPlus (f_algebra name) (f_algebra name)

\end{minipage}
}
\caption{Function algebra infrastructure}

\label{fig:falgebraclass}
\end{figure}

We use the name |Eval| to refer to the evaluation algebra.

> data Eval = Eval

The evaluation algebras are parameterized over an abstract super-functor |valf|
for values. In case of |ArithF| we require that integral values are part of
|valf| and for |BoolF| we require that boolean values are part of |valf|.

In the case of an |AddF| in the evaluation algebra for arithmetic expressions we
need to project the results of the recursive calls to test whether integral
values were produced. Otherwise a type error occurs and the |stuck| value is
returned.

> instance  (IntValueF :<: valf, StuckValueF :<: valf) =>
>             FAlgebra Eval ArithF (FixDTC valf) where
>   f_algebra Eval (LitF i)     =  vint i
>   f_algebra Eval (AddF a b)   =  case (project a, project b) of
>       (Just (VInt a) , Just (VInt b))  -> vint (a + b)
>       _                                -> vstuck

Similarly, we have to test the result of the recursive call of the condition of
an |IfF| term for boolean values.

> instance  (BoolValueF :<: valf, StuckValueF :<: valf) =>
>             FAlgebra Eval BoolF (FixDTC valf) where
>   f_algebra Eval (BLitF b)    =  vbool b
>   f_algebra Eval (IfF c t e)  =  case project c of
>       Just (VBool b)  ->  if b then t else e
>       _               ->  vstuck

Function algebras for different signatures can be combined to get an algebra for
their coproduct. The necessary instance declaration is also given in Figure
\ref{fig:falgebraclass}. Finally, we can define an evaluation function for terms
given an |FAlgebra| instance for |Eval|.

> eval :: (Functor expf, FAlgebra Eval expf (FixDTC valf)) =>
>         FixDTC expf -> FixDTC valf
> eval = foldDTC (f_algebra Eval)


%%% Local Variables:
%%% mode: latex
%%% TeX-master: "../../mod"
%%% End:
