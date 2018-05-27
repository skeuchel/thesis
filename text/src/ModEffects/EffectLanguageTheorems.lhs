%include lhs2TeX.fmt
%include polycode.fmt
%include forall.fmt
%include macros.fmt
%include Formatting.fmt

%if False

> {-# OPTIONS -XRankNTypes -XImpredicativeTypes -XTypeOperators -XMultiParamTypeClasses -XFlexibleInstances -XOverlappingInstances -XFlexibleContexts #-}

> module Elaboration where

%endif

\section{Effect and Language Theorems}\label{sec:mod:effectlangtheorems}
%-------------------------------------------------------------------------------
The second phase of showing type soundness is the \emph{effect theorem}, that
proves a statement of soundness for a fixed set of effects.

\subsection{Pure Languages}

For pure effects, the soundness statement is straightforward:
%
\begin{equation}
\forall |v_m|~|t|. \vdash_M | v_m : return t| \Rightarrow \exists |v|. |v_m
== return v|~\wedge \vdash |v| : |t|
\tag{\textsc{ESound}$_P$}\label{thm:ESoundP}
\end{equation}

Each effect theorem is proved by induction over the derivation of $\vdash_M$
|v_m : return t|. \ref{thm:ESoundP} fixes the irrelevant environment type to the
unit type |()| and the evaluation monad to the pure monad |Id|. Since the
evaluation monad is fixed, the proof of \ref{thm:ESoundP} only needs to consider
the pure typing rules of Figure~\ref{fig:WFM+Pure}. The proof of the effect
theorem is straightforward: \textsc{WFM-Illtyped} could not have been used to
derive $\vdash_M |v_m : return t|$, and \textsc{WFM-Return} provides both a
witness for |v| and a proof that it is of type |t|.

The statement of soundness for a pure language built from a particular set of
features is similar to \ref{thm:ESoundP}:
\begin{equation}
\forall |e|, |t|. |typeof e == return t| \Rightarrow \exists |v|. |eval e
== return v|~\wedge \vdash |v| : |t|
\tag{\textsc{LSound}$_P$}\label{thm:LSoundP}
\end{equation}

The proof of \ref{thm:LSoundP} is an immediate consequence of the reusable
proofs of \ref{thm:FSound} and \ref{thm:ESoundP}. Folding a proof algebra for
\ref{thm:FSound} over |e| provides a proof of $\vdash_M |eval e : return t|$,
satisfying the first assumption of \ref{thm:ESoundP}.  \ref{thm:LSoundP} follows
immediately.

%Since this proof of \ref{thm:FSound} only depends on the typing rules
%used and not on the particular features involved, it can be reused for
%any other pure language, e.g. any combination of booleans and
%arithmetic expressions. Proofs of type soundness for a particular set
%of effects are similarly divorced from a language's features,
%depending only on the set of typing rules (and thus effects) included
%in a language.

%The proof proceeds by straightforward case analysis of the typing rules of Fig.~\ref{fig:WFM+Pure}.
% \tom{This text does not yet assume that the typing monad is fixed:}
% \begin{itemize}
% \item
% The
% case for \textsc{WFM-Return} depends on another property of the |MT|
% monad used in the |typeof| function:
%
% < forall A B (ma :: M A) (f :: A -> B) b,
% <    fmap f ma = return b -> exists a._ f a = b
%
% This allows us to 'lift' a proof out of any monad with refinement type
% whose proof component has been projected out. This allows us to
% conclude that all the types in |typeof e| equal |t|, and soundness
% follows immediately from the assumptions of
% \textsc{WFM-Return}.
% \item
% Furthermore, a corollary of this law is that
% |forall v._ fail <> return v|, which in the \textsc{WFM-Untyped} case
% contradicts the assumption that |typeof e = return t|. The latter case
% demonstrates the important point that the set of effects is fixed in
% the specialized soundness theorems, allowing the proof to reason about
% the complete set of operations. In the pure case, for example, the
% proof can safely assume that |typeof e| will either equal |fail| or
% there will exists some |T| such that |typeof e = return T|. This will
% be useful in the next section.
% \end{itemize}
%
%
%Note however that the typing rules are independent of the particular feature
%used; they only depend on the effect. This means that the same specific proof can be
%reused for all pure features as long as they supply a proof algebra for the
%pure typing rules.

%if False
This allows us to 'lift' a proof out of any monad with refinement type whose
proof component has been projected out. This allows us to conclude that all the
types in |typeof e| equal |t|, and soundness follows immediately from the
assumptions of
\textsc{WFM-Return}.
\item Furthermore, a corollary of this law is that |forall v._ fail <> return
  v|, which in the \textsc{WFM-Untyped} case contradicts the assumption that
  |typeof e == return t|. The latter case demonstrates the important point that
  the set of effects is fixed in the specialized soundness theorems, allowing
  the proof to reason about the complete set of operations. In the pure case,
  for example, the proof can safely assume that |typeof e| will either equal
  |fail| or there will exists some |T| such that |typeof e == return T|. This
  will be useful in the next section.
\end{itemize}
%endif

%if False
-- Walk through Bool to motivate how the 'refinement monad' lets us avoid
-- lockstep typing and evaluation; also why WFM-Untyped is over |m_t >>=
-- fail| . In general, we need to discuss the sorts of properties you
-- need for the typing monad to act like proper static semantics.

-- Show specific lemma, explain the extra set of laws we need to
-- reason- Injectivity, behavior of fmap, Reasonable Monad. This is
-- where we 'fix' the set of effect values we care about.

-- \BD{Can we get rid of error values altogether using the exception
-- monad?}
%endif

%-------------------------------------------------------------------------------

\begin{figure}[t]
  \centering
  \fbox{
    \begin{minipage}{\columnwidth}
      \[ \begin{array}{c}
           \inferrule* [right=\textsc{Wfm-Throw}]
           {
           }
           { \Sigma \vdash_M |throw x| ~:~ |t_m|
           } \\\\
           \inferrule* [right=\textsc{Wfm-Catch}]
           { \Sigma \vdash_M |m >>= k|  ~:~ |t_m| \\
           \forall~\Sigma' \supseteq \Sigma~|x|~.~\Sigma' \vdash_M |h x >>= k| ~:~ |t_m|
           }
           {
           \Sigma \vdash_M |catch m h >>= k| ~:~ |t_m|
           } \\
         \end{array}
      \]
    \end{minipage}
  }
  \caption{Typing rules for exceptional monadic values.}
  \label{fig:WFM+Except}
\end{figure}

%-------------------------------------------------------------------------------
\subsection{Errors}

The evaluation algebra of the error language feature uses the side effects of
the exception monad, requiring new typing rules.

\paragraph{Typing Rules}

% \steven{There is some inconsistency with the framework / case study code and the
%   presentation here . In the framework it seems that half of the definitions for
%   the exception part of the computation typing and the error feature specialize
%   the exception type to be unit. Yet the paper definitions here seem to specify
%   the more general case for the computation typing and the error feature is
%   consistently using unit.}

Figure~\ref{fig:WFM+Except} lists the typing rules for monadic computations
involving exceptions which are parameterized by a type |x| for exceptional
values. \textsc{WFM-Throw} states that |(throw x)| is typeable with any
type. \textsc{WFM-Catch} states that binding the results of both branches of a
|catch| statement will produce a monad with the same type. While it may seem odd
that this rule is formulated in terms of a continuation |>>= k|, it is essential
for compatibility with the proofs algebras required by other features. As
described in Section~\ref{sec:Thm+Reuse}, extensible proof algebras over the
typing derivation will now need cases for the two new rules. To illustrate this,
consider the proof algebra for the general purpose \textsc{WFM-Bind}
property. This algebra requires a proof of:
%
\begin{align*}
  \begin{array}{l}
    (\Sigma\vdash_M|catch e h >>= k| ~:~t_m) \rightarrow \\
    (\forall v~t~\Sigma'\supseteq\Sigma.~(\Sigma'\vdash~v~:~t) \rightarrow
        \Sigma'\vdash_M~k_v~v~:~k_t~t) \rightarrow \\
     \Sigma\vdash_M(|catch e h >>= k|) |>>=| k_v:t_m |>>=| k_t
  \end{array}
\end{align*}


%if False
\begin{multline*} (\Sigma\vdash_M m_i ~:~
t_i)~\rightarrow~(\Sigma\vdash_M m_e~:~t_e)~\rightarrow \\ \Sigma
\vdash_M \left(\hspace{-5mm} \begin{minipage}{37mm}

> do  v <- catch e h >>= k
>     case isBool v of
>        Just b   ->
>          if b  then m_i
>                else m_e
>        Nothing  -> stuck

\end{minipage}
\right) :
\left(\hspace{-5mm}
\begin{minipage}{35mm}

> do  tc <- return t_c
>     tt <- t_t
>     te <- t_e
>     guard (isTBool tc)
>     guard (eqT tt te)
>     return tt

\end{minipage}
\right)
\end{multline*}
%endif

With the continuation, we can first apply the associativity law to reorder the
binds so that \textsc{WFM-Catch} can be applied: \[ |(catch e h >>= k) >>=| k_v
|= catch e h >>= (k >>= |k_v). \] The two premises of the rule follow immediately
from the inductive hypothesis of the lemma, finishing the proof. Without the
continuation, the proof statement only binds |catch e h| to |v_m|, leaving no
applicable typing rules.

%Because the error
%feature forces the evaluation monad to support exceptions, the rules
%of Figure~\ref{fig:WFM+Except} will need to be included in the
%extensible typing relation of any language that includes this
%feature. This is needed to prove the general soundness theorem, and
%can induce similar feature interactions.

%if False
will need to reduce this statement further

When combined with the pure rules, the proof of type soundness for the
exceptions language feature is straightforward. Thus, any language which
includes the exception feature and makes use of this proof must include these
rules in their typing definition.  Any proof for this language which built from
proof algebras over the typing derivations must therefore include cases for the
two rules in Figure~\ref{fig:WFM+Except}. The soundness proof for boolean
expressions from \ref{sec:Thm+Reuse} is an example of such a proof
algebra.\tom{the example needs clarification} These sorts of proof algebras
which are only needed for specific combinations of features are examples of
\textit{feature interactions}. Thankfully, these sorts of missing algebra can be
defined in a separate interaction file without threatening modularity of the
individual features.  \BD{Now that we've improved the previous section, we can
  flesh out the discussion of how these proof algebras work now. This is the
  perfect place to discuss wfvm\_bind versus the 'weakest possible' rules.}
%endif

\paragraph{Effect Theorem} The effect theorem, \ref{thm:ESoundE}, for a
language whose only effect is exceptions reflects that the evaluation
function is either a well-typed value or an exception.
%
\begin{align*}
  \begin{array}{l}
    \forall |v_m|~|t|. \vdash_M |v_m : return t| \rightarrow \\
      \exists x. |v_m == throw |~x \lor
      \exists |v|. |v_m == return v| \wedge \vdash |v| : |t|
  \end{array}
  \tag{\textsc{ESound$_E$}}
  \label{thm:ESoundE}
\end{align*}
The proof of \ref{thm:ESoundE} is again by induction on the derivation of
$ \vdash_M$ |v_m : return t|. The irrelevant environment can be fixed to the
unit type |()|, while the evaluation monad is the exception monad |ExcT x Id|.

The typing derivation is built from four rules: the two pure rules from
Figure~\ref{fig:WFM+Pure} and the two exception rules from
Figure~\ref{fig:WFM+Except}.  The case for the two pure rules is effectively the
same as before, and \textsc{WFM-Throw} is straightforward. In the remaining
case, |(v_m == catch e' h)|, and we can leverage the fact that the evaluation
monad is fixed to conclude that either $(\exists |v|.|e' == return v|)$ or
$(\exists |x|. |e' == throw x|)$. In the former case, |catch e' h| can be
reduced using |catch_return|, and the latter case is simplified using
|catch_throw1|. In both cases, the conclusion then follows immediately from the
assumptions of \textsc{WFM-Catch}.  The proof of the language theorem \LSoundE
is similar to \ref{thm:LSoundP} and is easily built from \ref{thm:ESoundE} and
\ref{thm:FSound}.

\begin{figure}[t]
  \centering
  \fbox{
    \begin{minipage}{\columnwidth}
      \[ \begin{array}{c}
           \inferrule* [right=\textsc{Wfm-Get}]
           { \forall \sigma, \Sigma\vdash\sigma~\rightarrow~\Sigma \vdash_M k~\sigma:t_m
           }
           { \Sigma \vdash_M ~ |get >>= k| ~:~ t_m
           } \\\\
           \inferrule* [right=\textsc{Wfm-Put}]
           { \Sigma' \vdash \sigma \\
             \Sigma' \supseteq \Sigma \\
             \Sigma' \vdash_M k : t_m
           }
           { \Sigma \vdash_M ~ |put s_ >> k| ~:~ t_m
           } \\
         \end{array}
      \]
    \end{minipage}
  }
  \caption{Typing rules for stateful monadic values.}
  \label{fig:WFM+State}
\end{figure}

%-------------------------------------------------------------------------------
\subsection{References}

\paragraph{Typing Rules}

Figure~\ref{fig:WFM+State} lists the two typing rules for stateful computations.
To understand the formulation of these rules, consider \ref{thm:LSoundS}, the
statement of soundness for a language with a stateful evaluation function. The
statement accounts for both the typing environment $\Sigma$ and evaluation
environment $\sigma$ by imposing the invariant that $\sigma$ is well-formed with
respect to $\Sigma$. \ref{thm:FSound} however, has no such conditions (which
would be anti-modular in any case). We avoid this problem by accounting for the
invariant in the typing rules themselves:

\begin{itemize}
\item \textsc{WFM-Get} requires that the continuation |k| of a |get| is
  well-typed under the invariant.
\item \textsc{WFM-Put} requires that any newly installed environment maintains
  this invariant.
\end{itemize}
The intuition behind these premises is that effect theorems will maintain these
invariants in order to apply the rules.

% \begin{multline}
% \forall \Sigma |e| \sigma. |typeof e == return t| \Rightarrow
% \Sigma \vdash \sigma~:~\Sigma \Rightarrow \\
% \exists~\Sigma'~\sigma'~|v|. |put|~\sigma |>> eval e = put|~\sigma' |>>
%  return v| \wedge \Sigma' \vdash |v| : |t|
% \label{eqn:WFM+State+Thm}
% \end{multline}

%\begin{gather*}
%\forall e, t, \Sigma, \sigma.
%    \left\{\begin{array}{c}
%    | local (const Sigma) (typeof e) == return t | \\
%    \Sigma \vdash \sigma
%    \end{array}\right\} \\
% \rightarrow \\
%  \exists v, \Sigma', \sigma'.
%   \left\{\begin{array}{c}
%   |put sigma >> eval e| = |put sigma' >> return v| \\
%   \Sigma' \supseteq \Sigma \\
%   \Sigma' \vdash v : t \\
%   \Sigma' \vdash \sigma'
%   \end{array}\right\}
%\end{gather*}

\paragraph{Effect Theorem}

%format Sigma = "\Sigma"
The effect theorem for mutable state proceeds again by induction over the typing
derivation. The evaluation monad is fixed to |StateT Sigma Id| and the
environment type is fixed to |[Type]| with the obvious definitions for
$\supseteq$.

\begin{itemize}
\item
The proof case for the two pure rules is again straightforward.
\item
For \textsc{WFM-Get} we have that |put|~$\sigma$~|>> eval e ==
put|~$\sigma$~|>> get >>= k|. After reducing this to (|k| $\sigma$) with the
|put_get| law, the result follows immediately from the rule's assumptions.
\item
Similarly, for \textsc{WFM-Put} we have that |put|~$\sigma$~|>> eval e == put|~$\sigma$~|>> put|~$\sigma'$ |>> k|. After reducing this to |put|~$\sigma'$ |>> k| with the |put_put| law, the result again follows immediately from the rule's assumptions.
\end{itemize}

%Just as with exceptions, these new rules can induce new feature
%interactions. Thankfully, derivation of these proof algebras can be
%automated quite nicely by hooking automated tactics into the typeclass
%algorithm. \BD{Need to flesh this out some more.}

%The reader has no doubt noticed the $\Sigma$ typing environments
%polluting our other typing rules. Thankfully, we can deal with this
%quite cleanly. \BD{Need to implement the lifting function so we can
%flesh out this section.}

%-------------------------------------------------------------------------------
\subsection{Lambda}

The case study represents the binders of the lambda feature using
PHOAS~\cite{phoas} to avoid many of the boilerplate definitions and proofs about
term well-formedness found in first-order representations.
%The parametricity of the expression functor requires
%the soundness proofs to induct over an equivalence relation, the
%details of which are covered in the MTC paper~\cite{mtc}.

\paragraph{The Environment Effect} \name neatly hides the variable environment
of the evaluation function with a reader monad |MonadReader|, unlike
\textsc{MTC} which passes the environment explicitly. This new effect introduces
the two new typing rules listed in Figure~\ref{fig:WFM+Environment}.
Unsurprisingly, these typing rule are similar to those of
Figure~\ref{fig:WFM+State}. The rule for |ask| is essentially the same as
\textsc{WFM-Get}. The typing rule for |local| differs slightly from
\textsc{WFM-Put}. Its first premise ensures that whenever |f| is applied to an
environment that is well-formed in the original typing environment $\Gamma$, the
resulting environment is well-formed in some new environment $\Gamma'$. The
second premise ensures the body of |local| is well-formed in this environment
according to some type |T|, and the final premise ensures that |k| is
well-formed when applied to any value of type |T|. The intuition behind binding
the |local| expression in some |k| is the same as with |put|.


\begin{figure}[t]
  \centering
  \fbox{
    \begin{minipage}{\columnwidth}
      \[ \begin{array}{c}
           \inferrule* [right=\textsc{Wfm-Ask}]
           { \forall \gamma.~\Gamma\vdash\gamma~ \rightarrow
             ~\Gamma \vdash_M k~\gamma:t_m
           }
           { \Gamma \vdash_M ~ |ask >>= k| ~:~ t_m
           } \\\\
           \inferrule* [right=\textsc{Wfm-Local}]
           { \forall~\gamma.~\Gamma\vdash\gamma \rightarrow
             \Gamma'\vdash f~\gamma \\
             \Gamma' \vdash_M m~:~\mathit{return}~~t'_m \\
             \forall v.~\vdash v~:~t'_m \rightarrow \Gamma \vdash_M (k~v) : t_m \\
           }
           { \Gamma \vdash_M ~ |local f m >>= k| ~:~ t_m
           } \\\\
           \inferrule* [right=\textsc{Wfm-Bot}]
           { \; }
           { \Gamma \vdash_M \bot ~:~ |t_m|
           } \\
         \end{array}
      \]
    \end{minipage}
  }
  \caption{Typing rules for environment and failure monads.}
  \label{fig:WFM+Environment}
\end{figure}

% \begin{figure}
%   \fbox{
%   \begin{minipage}{.95\columnwidth}
%       \infrule[WFM-Bot]{}{
%         \Sigma \vdash_M \bot ~:~ |t_m|
%       }
%   \end{minipage}
%  }
% \caption{Typing rule for failure monad for nontermination.}
% \label{fig:WFM+Bot}
% \end{figure}

\paragraph{The Partiality Effect}
The lambda feature also introduces the possibility of non-termination to the
evaluation function, which is disallowed by Coq. MTC solves this problem by
combining \textit{mixin algebras} with a bounded fixed-point function. This
function applies an algebra a bounded number of times, returning a $\bot$ value
when the bound is exceeded.  Because MTC represented $\bot$ as a value, all
evaluation algebras needed to account for it explicitly. In the monadic setting,
\name elegantly represents $\bot$ with the |fail| primitive of the failure
monad. This allows terminating features to be completely oblivious to whether a
bounded or standard fold is used for the evaluation function, resulting in a
much cleaner semantics. \textsc{WFM-Bot} allows $\bot$ to have any type.



%===============================================================================
\subsection{Modular Effect Compositions}

As we have seen, laws are essential for proofs of \ref{thm:FSound}. The proofs
so far have involved only up to one effect and the laws regulate the behavior of
that effect's primitive operations.

Languages often involve more than one effect, however. As outline in
Section~\ref{ssec:mod:effectdependenttheorems} the effect theorem depends on the
set of available effects, and in the case of multiple effects the theorem is
different from the theorem for any proper subset of effects. Moreover, the
proofs of effect theorems must reason about the interaction between multiple
effects. There is a trade-off between fully instantiating the monad for the
language as we have done previously, and continuing to reason about a
constrained polymorphic monad. The former is easy for reasoning, while the
latter allows the same language proof to be instantiated with different
implementations of the monad. In the latter case, additional \emph{effect
  interaction} laws are required.

The following sections discuss compositions of different set of effects, their
effect theorem statement, and the necessary interaction laws to prove the effect
theorem.

%\BD{This section needs a discussion of the two candidate rules for how put and
%catch interact. This reflects the fact that sometimes there aren't single laws
%governing the interactions of effects. In this case, this is okay: we can prove
%the lemma for either choice. Plus, since only the catch feature needs this
%rule, the other effect rules are independent of this choice. }

%-------------------------------------------------------------------------------
\subsection{State and Exceptions}

Consider the effect theorem which fixes the evaluation monad to support
exceptions and state. The statement of the theorem mentions both kinds of
effects by requiring the evaluation function to be run with a well-formed state
$\sigma$ and by concluding that well-typed expressions either throw an exception
or return a value. The \textsc{WFM-Catch} case this theorem has the following
goal:
\begin{gather*}
(\Sigma \vdash \sigma~:~\Sigma) \\ \rightarrow \\
\exists~\Sigma',\sigma',|v|.
\left\{\begin{array}{c}
|put|~\sigma |>> catch e h >>= k == put|~\sigma' |>>
 return v| \\ \Sigma' \vdash |v| : |t| \\
\end{array}\right\} \\
\vee \\
\exists~\Sigma',\sigma',|x|.
\left\{\begin{array}{c}
|put|~\sigma |>> catch e h >>= k == put|~\sigma' |>>
 throw x| \\
 \Sigma' \vdash \sigma'~:~\Sigma'
\end{array}\right\}
\end{gather*}
% \begin{multline}
% \Sigma \vdash \sigma~:~\Sigma \Rightarrow \\
% \exists~\Sigma'~\sigma'~|v|. |put|~\sigma |>> catch e h >>= k == put|~\sigma' |>>
%  return v| \\\wedge \Sigma' \vdash |v| : |t| \\
% \bigvee~
% \exists~\Sigma'~\sigma'~|t|. |put|~\sigma |>> catch e h >>= k == put|~\sigma' |>>
%  throw t| \wedge \\
%  \Sigma' \vdash \sigma'~:~\Sigma'
% \end{multline}\BO{Please add some brakets to make the scoping of quantifiers clearer.}

%Building a language with references and exceptions produces yet
%another statement of type soundness.


In order to apply the induction hypothesis to |e| and |h|, we need to precede
them by a $(|put|~\sigma)$.  Hence, $(|put|~\sigma)$ must be pushed under the
|catch| statement through the use of a law governing the behavior of |put| and
|catch|.  There are different choices for this law, depending on the monad that
implements both |MonadState| and |MonadError|. We consider two reasonable
choices, based on the monad transformer compositions |ExcT x (StateT s Id)| and
|StateT s (ExcT x Id)|:
\begin{itemize}
\item Either |catch| passes the current state into the handler:
  \begin{spec}
    put s_ >> catch e h == catch (put s_ >> e) h
  \end{spec}
\item Or |catch| runs the handler with the initial state:
  \begin{spec}
    put s_ >> catch e h == catch (put s_ >> e) (put s_ >> h)
  \end{spec}
\end{itemize}
% There are other, more exotic interactions possible, but these two
% (alternative) rules capture the standard understanding of how languages with
% exceptions and environments may work.
The \textsc{WFM-Catch} case is provable under either choice.  As the
\ESoundES~proof is written as an extensible theorem, the two cases are
written as two separate proof algebras, each with a different assumption about
the behavior of the interaction. Since the cases for the other rules are
impervious to the choice, they can be reused with either proof of
\textsc{WFM-Catch}.

% In either case, |catch| can be reduced further. If |put s_ >> eval e = put s_'
% >> return v| the inductive hypothesis for |e| can be applied. Alternatively,
% when |put s_ >> eval e = put s' >> throw t|, the inductive hypothesis for |k|
% can be applied using |s'| and the extended context $\Sigma'$ produced by the
% inductive hypothesis for |e|. Note that \textsc{WFM-Catch} types |h >>= k|
% under all $\Sigma'$ precisely so that in the case that |catch| pass the
% effects from |eval e| to the handler the proof can account for the extended
% environment.

\begin{figure}[t]
\noindent\fbox{
\begin{minipage}{0.98\columnwidth}
\vspace{-.2cm}
\begin{align*}
\begin{array}{l}
\forall \Sigma,\Gamma,\delta,\gamma,\sigma,|e|_E,|e|_T.
  \left\{\begin{array}{c}
   \gamma,\delta\vdash~|e|_E\equiv|e|_T \\
   \Sigma \vdash \sigma~:~\Sigma \\
   \Sigma \vdash \gamma~:~\Gamma \\
  |typeof e|_T| == return t| \\
  \end{array}\right\}
\rightarrow \\
\hspace{0.25cm} \exists~\Sigma',\sigma',|v|.
  \left\{\begin{array}{c}
  |local (\ _._| \gamma |) (put|~\sigma |>> eval e|_E|)| \\
   |== local (\ _._| \gamma |) (put|~\sigma' |>> return v)| \\
  \Sigma' \vdash |v| : |t| \\
  \end{array}\right\}
 \vee \\
\hspace{0.25cm} \exists~\Sigma',\sigma',|v|.
  \left\{\begin{array}{c}
  |local (\ _._| \gamma |) (put|~\sigma |>> eval e|_E|)| \\
  |== local (\ _._| \gamma |(put|~\sigma' |>>| \bot |)| \\
  \Sigma' \vdash \sigma'~:~\Sigma'  \\
  \Sigma' \supseteq \Sigma
  \end{array}\right\}
 \vee \\
\hspace{0.25cm} \exists~\Sigma',\sigma',|v|.
  \left\{\begin{array}{c}
 |local (\ _._| \gamma |) (put|~\sigma |>> eval e|_E|)| \\
 |== local (\ _._| \Gamma |(put|~\sigma' |>> throw t)|  \\
 \Sigma' \vdash \sigma'~:~\Sigma' \\
 \Sigma' \supseteq \Sigma \\
         \end{array}\right\}
\end{array}
 \tag{\textsc{ESound}$_\mathit{ESRF}$}
  \label{thm:ESoundESRF}
\end{align*}

% \begin{multline}
% \forall \Sigma,\Gamma,\delta,\gamma,\sigma,|e|_E,|e|_T. \quad
% \gamma,\delta\vdash,|e|_E\equiv|e|_T \Rightarrow \\
% \Sigma \vdash \sigma,:,\Sigma \Rightarrow
% \Sigma \vdash \gamma,:,\Gamma \Rightarrow
% |typeof e|_T| == return t| \Rightarrow \\
% \exists,\Sigma',\sigma',|v|. |local (\ _._| \gamma |) (put|,\sigma |>> eval
% e|_E|) =| \\
%    |local (\ _._| \gamma |) (put|,\sigma' |>> return v)| \wedge \Sigma' \vdash |v| : |t| \\
% \bigvee
% \exists,\Sigma',\sigma',|v|. |local (\ _._| \gamma |) (put|,\sigma |>> eval
% e|_E|) =| \\
%  |local (\ _._| \gamma |(put|,\sigma' |>>|
%  \bot |)| \wedge \Sigma' \vdash \sigma',:,\Sigma'
% \wedge \Sigma' \supseteq \Sigma\\
% \bigvee
% \exists,\Sigma',\sigma',|v|. |local (\ _._| \gamma |) (put|,\sigma |>> eval
% e|_E|) =| \\
%  |local (\ _._| \Gamma |(put|,\sigma' |>>
%  throw t)| \wedge \Sigma' \vdash \sigma',:,\Sigma'
% \wedge \Sigma' \supseteq \Sigma \\
% \tag{\textsc{Sound}$_\mathit{ESRF}$}
% \label{thm:LSoundESRF}
% \end{multline}
\end{minipage}
}
\caption{Effect theorem statement for languages with errors, state, an environment and failure.}
\label{f:th:esrf}
\vspace{-.4cm}
\end{figure}

%-------------------------------------------------------------------------------
\subsection{State, Reader and Exceptions}

\begin{figure}[t]
\fbox{
\hspace{-10pt}\begin{minipage}{.98\columnwidth}
\scriptsize
\hspace{.65cm}\ruleline{Exceptional Environment}
< class (MonadError x m, MonadEnvironment  m) => MonadErrorEnvironment x g m where
<   local_throw      :: local f (throw e) == throw e
<   local_catch      :: local f (catch e h) ==
<                             catch (local f e) (\x._ local f (h x))

\hspace{.65cm}\ruleline{Exceptional Failure}
< class (MonadError x m, FailMonad m) => MonadFailState x m where
<   catch_fail       :: catch fail h == fail
<   fail_neq_throw   :: fail <> throw x

\hspace{.65cm}\ruleline{Exceptional State Failure}
< class (MonadError x m, MonadState s m, FailMonad m) => MonadFailErrorState x m where
<    put_fail_throw  :: put s_ >> fail <> put s_' >> throw x

\hspace{.65cm}\ruleline{Exceptional State}
< class (MonadError x m, FailMonad m) => MonadErrorState x m where
<   put_ret_throw :: put s_ >> return a <> put s_' >> throw x
<   put_throw        :: forall A B. put s_ >> throw_A x == put s_' >> throw_A x ->
<                    put s_ >> throw_B x == put s_' >> throw_B x

\hspace{.65cm}\ruleline{Alternate Exceptional State laws}
< class (MonadError x m, FailMonad m) => MonadErrorState_1 x m where
<   put_catch1        :: put s_ >> catch e h == catch (put s_ >> e) h
\hspace{.65cm}\ruleline{Or}
< class (MonadError x m, FailMonad m) => MonadErrorState_2 x m where
<   put_catch2       :: put env >> catch e h ==
<                       catch (put s_ >> e) (\x -> put s_ >> h x)

\end{minipage}
}

\caption{Interaction laws}

\label{fig:Interaction+Laws}
\end{figure}

A language with references, errors and lambda abstractions features four
effects: state, exceptions, an environment and failure. The language theorem for
such a language relies on the effect theorem \ref{thm:ESoundESRF} given in
Figure~\ref{f:th:esrf}. The proof of \ref{thm:ESoundESRF} is similar to the
previous effect theorem proofs, and makes use of the full set of interaction
laws given in Figure~\ref{fig:Interaction+Laws}. Perhaps the most interesting
observation here is that because the environment monad only makes local changes,
we can avoid having to choose between laws regarding how it interacts with
exceptions. Also note that since we are representing nontermination using a
failure monad |FailMonad m|, the |catch_fail| law conforms to our desired
semantics.

%\BD{Maybe we
%should just move this section and figures to the case study?}

%format throw_A = "\Varid{throw}_\Varid{A}"
%format throw_B = "\Varid{throw}_\Varid{B}"
%format <> = "\not\equiv"
%format MonadErrorState_1 = "\Varid{MonadErrorState}_1"
%format MonadErrorState_2 = "\Varid{MonadErrorState}_2"

% \BO{Maybe it would be worthwhile to say a few more words on these laws.  The
% interaction laws tend to be much more application-specific and really pin-down
% particular semantic interactions between effects. We already say something
% earlier regarding |put| and |catch|, but maybe we can have a more general
% statement and also comment on some other laws. For example |fail <> throw x|
% prevents a particular monad configuration which is when exceptions coincide
% with failure. This is because, in the particular application, we intend that
% exceptions denote exceptional values, whereas failure denotes
% non-termination.}

%%% Local Variables:
%%% mode: latex
%%% TeX-master: "../../mod"
%%% End:
