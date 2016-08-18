%include lhs2TeX.fmt
%include polycode.fmt
%include forall.fmt
%include macros.fmt
%include Formatting.fmt

%if False

> {-# OPTIONS -XRankNTypes -XImpredicativeTypes -XTypeOperators -XMultiParamTypeClasses -XFlexibleInstances -XOverlappingInstances -XFlexibleContexts #-}

> module Elaboration where

%endif

\begin{figure}[t!]
  \fbox{
  \begin{minipage}{.95\columnwidth}
     \hspace{-1.5cm}\begin{minipage}{1.15\columnwidth}
      \infrule[WFM-Illtyped]{}{
        \Sigma \vdash_M |v_m| ~:~ |fail|
      }
      \vspace{.25cm}
      \hspace{-1cm} \infrule[WFM-Return] {
         \Sigma \vdash v ~:~ t
      }
      {
       \Sigma \vdash_M |return v| ~:~ |return t|
      }
  \end{minipage}
  \end{minipage}
 }
\caption{Typing rules for pure monadic values.}
\label{fig:WFM+Pure}
\vspace{-.4cm}
\end{figure}

\section{Modular Monadic Type Safety}

%if False

As demonstrated above, soundness statements which hardwire the set of
effects limit their modularity by rendering proofs for soundness
statements with distinct effects incompatible.

%-------------------------------------------------------------------------------
\subsection{Three-Step Approach}

%endif

In order to preserve a measure of modularity, we do not prove type
soundness directly for a given feature, but by means of a more generic
theorem. The technique of proving a theorem of interest by means of a
more general theorem is well-known. For a conventional monolithic
language, for instance, type soundness is often established for any
well-formed typing context, even though the main interest lies with
the more specific initial, empty context. In that setting, the more
general theorem produces a weaker induction hypothesis for the
theorem's proof.

Our approach to type soundness follows the core idea of this technique
and relies on three theorems:

{\addtolength{\leftskip}{5mm}
\noindent \hspace{-.25cm} \textsc{FSound}:
 a reusable \emph{feature theorem} that is only aware of the effects that
 a feature uses \par}

{\addtolength{\leftskip}{5mm}
\noindent \hspace{-.25cm} \textsc{ESound}:
 an \emph{effect theorem} for a fixed set of known effects, and \par}

{\addtolength{\leftskip}{5mm}
\noindent\hspace{-.25cm} \textsc{LSound}: a \emph{language theorem} which combines the two
to prove soundness for a specific language.
\par }

\noindent In order to maximize compatibility, the statement of the
reusable feature theorem cannot hardwire the set of effects. This
statement must instead rephrase type soundness in a way that can adapt
to any superset of a feature's effects. Our solution is to have the
feature theorem establish that the monadic evaluation and typing
algebras of a feature satisfy an extensible well-formedness relation,
defined in terms of effect-specific typing rules. Thus, a
feature's proof of \ref{thm:FSound} uses only the typing rules required
for the effects specific to that feature. The final language combines
the typing rules of all the language's effects into a closed relation.

\begin{figure}[t!]
  \fbox{
  \includegraphics[scale = .77]{src/ModEffects/Figures/Dependency-1.pdf}
   }
\caption{Dependency Graph}
\label{fig:Dep-Graph}
\end{figure}

Figure~\ref{fig:Dep-Graph} illustrates how these reusable pieces fit
together to build a proof of soundness. Each feature provides a proof
algebra for \ref{thm:FSound} which relies on the typing rules
(\textsc{WFM-X}) for the effects it uses. Each unique statement of
soundness for a combination of effects requires a new proof of
\textsc{ESound}. The proof of \ref{thm:LSoundP} for a particular
language is synthesized entirely from a single proof of
\textsc{ESound} and a combination of proof algebras for
\ref{thm:FSound}.

Note that there are several dimensions of modularity here. A feature's
proof of \ref{thm:FSound} only depends on the typing rules for the
effects that feature uses and can thus be used in any language which
includes those typing rules. The typing rules themselves can be reused
by any number of different features. \textsc{ESound} depends solely on
a specific combination of effects and can be reused in any language
which supports that unique combination, e.g. both
\textsc{LSound$_{A}$} and \textsc{LSound$_{AR}$} use
\textsc{ESound$_{ES}$}.


% around an extensible relation, which relates two
% monadic computations.
% To acheive extensibility, we prove that an extensible
% relation holds over the monadic values of the evaluation function and
% the typing function of each language feature. Each effect will have
% its own set of typing rules used by each feature which uses that
% effect. The final relation is the composition of the typing rules for
% the set of effects in the final language.

% An important modularity property of the typing rules is that they only
% depend on the effects and not on the features. This enables us to
% decouple the proof that a feature's semantics obeys the extensible
% relation from the proof that the closed relation entails the actual
% property of interest, type soundness. The latter proof does
% not depend on the particular features involved, only on the
% effects. The rules reflect the other dimension of modularity: we can now
% have effect modules which are independent of language features
% (although the latter depend on the former). Thus, soundness theorems
% need to be proven only once for each combination of effects, and can
% be reused for any language with that combination of effects.

% Figures~\ref{fig:WFM+Pure}-\ref{fig:WFM+Except} provide examples of
% the judgements of this monadic well-formedness relation. In essence,
% each rule defines how to type a monadic value which binds an operation
% of that monad. Each effect-specific soundness proof proceeds by
% induction on this relation; in each case showing how to 'process' this
% function according to the specific set of effects and then using the
% inductive hypothesis for the computation resulting from binding the
% result.

%-------------------------------------------------------------------------------
\subsection{Soundness for a Pure Feature}

%- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
\label{sec:Thm+Reuse}

The reusable feature theorem \ref{thm:FSound} states that |eval| and
|typeof| are related by the extensible typing relation:
\begin{equation}
  \forall e, \Sigma.\quad\Sigma \vdash_M |eval e| : |typeof e|
\tag{\textsc{FSound}}
\label{thm:FSound}
\end{equation}

\paragraph{Extensible Typing Relation} The extensible
typing relation has the form: \[ \Sigma \vdash_M v_m : t_m \] The
relation is polymorphic in an environment type |env| and an evaluation
monad type |m|.  The parameters $\Sigma$, $v_m$ and $t_m$ have types
|env|, |m Value| and |Maybe Type| respectively.
% \BO{using |m_e| and
%|m_t| may be confused with the monad type |m|.  Maybe some different
%variable names are better? (This is low priority: if there's time,
%because we need to make sure everything is consistently patched)}.
The modular typing rules for this relation can impose constraints on
the environment type |env| and monad type |m|. A particular language must
instantiate |env| and |m| in a way that satisfies all the
constraints imposed by the typing rules used in its features.

Figure~\ref{fig:WFM+Pure} lists the two base typing rules of this
relation. These do not constrain the evaluation monad and environment
types and are the only rules needed for pure features. The
\textsc{(WFM-Illtyped)} rule denotes that nothing can be
said about computations (|m_e|) which are ill-typed.
The \textsc{(WFM-Return)} rule ensures that well-typed computations only
yield values of the expected type.

To see how the reusable theorem works for a pure feature, consider the proof
of soundness for the boolean feature.


\paragraph{Proof} Using the above two rules, we can show that
\ref{thm:FSound} holds for the boolean feature. The proof
has two cases.  The boolean literal case is handled by a
trivial application of \textsc{(WFM-Return)}. The second case, for
conditionals, is more interesting\footnote{We omit the environment $\Sigma$ to avoid clutter.}.
\vspace{-1mm}
\begin{multline*}
(\vdash_M |eval e_c|~:~|typeof e_c|) \rightarrow \\
\hspace{-2cm}(\vdash_M |eval e_t|~:~|typeof e_t|) \rightarrow \\
   (\vdash_M |eval e_e|~:~|typeof e_e|) \rightarrow \\
 \vdash_M \left(\hspace{-5mm}
\begin{minipage}{37mm}

> do  v <- eval e_c
>     case isBool v of
>        Just b   ->
>          if b  then eval e_t
>                else eval e_e
>        Nothing  -> stuck

\end{minipage}
\right) :
\left(\hspace{-5mm}
\begin{minipage}{35mm}

> do  t_c <- typeof e_c
>     t_t <- typeof e_t
>     t_e <- typeof e_e
>     guard (isTBool t_c)
>     guard (eqT t_t t_e)
>     return t_t

\end{minipage}
\right)
\tag{\textsc{WFM-If-Vc}}
\label{thm:WFM+If+Vc}
\end{multline*}
\vspace{-2mm}
% \BO{Another comment. Earlier we talk about the monad |m| (lowercase), here we use
% the subscript |M| (uppercase). Should these be the same?}

% TOM: I think we don't have to talk about lockstep here because we don't
%      mention it before either. It would only be distracting and confusing
%      to cover a failed attempt at tackling monads.
%
% The proof algebra that $\vdash_M$
% |(eval e) : typeof e| has a case for boolean literals and another for
% conditionals. The goal in the second case simplifies to $\vdash_M$ |(do
% v_c <- eval c; ...) : do T_c <- typeof; ... |. \BD{Latex this formula
% correctly.}  Observe there is a disconnect between the monadic values
% returned by the two functions. This is a common occurence, as |eval|
% can dynamically decide which subexpressions to evaluate while |typeof|
% must consider every subexpression in order to be a proper static
% semantic function. The desire to have a more flexible relation
% (i.e. not lockstep) motivates the formulation of \textsc{WFM-Return}
% in Fig.~\ref{fig:WFM+Pure}.

Because |eval| and |typeof| are polymorphic in the monad, we cannot
directly inspect the values they produce. We can, however, perform
case analysis on the derivations of the proofs produced by the
induction hypothesis that the subexpressions are well-formed,
$\vdash_M$~|eval e_c|~:~|typeof e_c|,
$\vdash_M$~|eval e_t|~:~|typeof e_t|, and
$\vdash_M$~|eval e_e|~:~|typeof e_e|. The final rule used in each derivation determines the shape of
the monadic value produced by |eval| and |typeof|.
Assuming that only the pure typing rules of Figure~\ref{fig:WFM+Pure}
are used for the derivations, we can divide the proof into
two cases depending on whether |e_c|, |e_t|, or |e_e| was typed with \textsc{(WFM-Illtyped)}.
\begin{itemize}
\item
If any of the three derivations uses \textsc{(WFM-Illtyped)},
the result of |typeof| is |fail|. As |fail| is the zero of the typing
monad, \textsc{(WFM-Illtyped)} resolves the case.
\item
Otherwise, each of the subderivations was built with
\textsc{(WFM-Return)} and the evaluation and typing expressions can
be simplified using the |return_bind| monad law.
\[ \hspace{-5mm}\vdash_M \left(\hspace{-5mm}
\begin{minipage}{37mm}

> case isBool v_c of
>    Just b   ->
>      if b  then return v_t
>            else return v_e
>    Nothing  -> stuck

\end{minipage}
\right) :
\left(\hspace{-5mm}
\begin{minipage}{35mm}

> do  guard (isTBool t_c)
>     guard (eqT t_t t_e)
>     return t_t

\end{minipage}
\right)
\]
After simplification, the typing expression has replaced the bind with
explicit values which can be reasoned with. If |isTBool t_c| is |false|, then
the typing expression reduces to |fail| and well-formedness again follows from the
\textsc{WFM-Illtyped} rule. Otherwise |t_c == TBool|, and we
can apply the inversion lemma
\[ \vdash |v| : |TBool| \rightarrow \exists b. |isBool v == Just b| \] to
establish that |v_c| is of the form |Just b|, reducing the evaluation
to either |return v_e| or |return v_t|. A similar case analysis on
|eqT t_t t_e| will either produce |fail| or |return t_t|. The former
is trivially true, and both $\vdash_M |return v_t|:|return
t_t|$ and $\vdash_M |return v_e|:|return t_t|$ hold
in the latter case from the induction hypotheses.
%
% \tom{Need more clarification here.}
% In
% the \textsc{WFM-Return} case, |(do v_c <- eval c; ...)| simplifies to
% either |Stuck|, |eval t|, or |eval e|. In the first case, we can push
% the type information in the refinement type of |T_c'| from the
% \textsc{WFM-Return} rule used to build the current case into the body
% of the bind expression to ensure that |do T_c <- typeof c; ...| will
% evaluate to |fail|, from which \textsc{WFM-Untyped} applies. The
% refinement type of the |T_c'| monad can be used analogously in the
% other two cases to ensure that |typeof c| always produces |TBool|, and
% \textsc{WFM-Return} can then be applied.
\end{itemize}

\paragraph{Modular Sublemmas} The above proof assumed that only the
pure typing rules of Figure~\ref{fig:WFM+Pure} were used to type the
subexpressions of the |if| expression, which is clearly not the case
when the boolean feature is included in an effectful
language. Instead, case analyses are performed on the extensible
typing relation in order to make the boolean feature theorem
compatible with new effects. Case analyses over the extensible
$\vdash_M$ relation are accomplished using extensible proof algebras
which are folded over the derivations provided by the induction
hypothesis, as outlined in Section~\ref{subsec:modproofs}.

In order for the boolean feature's proof of \ref{thm:FSound} to be
compatible with a new effect, each extensible case analysis requires a
proof algebra for the new typing rules the effect introduces to the $\vdash_M$
relation. These proof algebras are examples of
\emph{feature interactions}~\cite{featureinteractions} from the
setting of modular component-based frameworks. In essence, a feature
interaction is functionality (e.g., a function or a proof) that is
only necessary when two features are combined. Importantly, these
proof algebras do not need to be provided up front when developing the
boolean algebra, but can instead be modularly resolved by a separate
feature for the interaction of booleans and the new effect.

%if False
\vspace{-2mm}
\begin{multline} (\vdash_M m_c~:~t_c)~\rightarrow\\ (\vdash_M
m_t~:~t_t)~\rightarrow~(\vdash_M m_e~:~t_e)~\rightarrow\\ \vdash_M
\left(\hspace{-5mm} \begin{minipage}{37mm}

> do  v <- m_c
>     case isBool v of
>        Just b   ->
>          if b  then m_t
>                else m_e
>        Nothing  -> stuck

\end{minipage}
\right) :
\left(\hspace{-5mm}
\begin{minipage}{35mm}

> do  tc <- t_c
>     tt <- t_t
>     te <- t_e
>     guard (isTBool tc)
>     guard (eqT tt te)
>     return tt

\end{minipage}
\right)
\tag{\textsc{WFM-If-Vc}}
\label{thm:WFM+If+Vc}
\end{multline}
%endif


The formulation of the properties proved by extensible case analysis
has an impact on modularity. The conditional case of the previous
proof can be dispatched by folding a proof algebra for the property
\ref{thm:WFM+If+Vc} over $\vdash_M~|eval v_c|~:~|typeof t_c|$. Each
new effect induces a new case for this proof algebra, however,
resulting in an interaction between booleans and every
effect. \ref{thm:WFM+If+Vc} is specific to the proof of
\ref{thm:FSound} in the boolean feature; proofs of \ref{thm:FSound}
for other features require different properties and thus different
proof algebras. Relying on such specific properties can lead to a
proliferation of proof obligations for each new effect.

Alternatively, the boolean feature can use a proof algebra for a
stronger property that is also applicable in other proofs, cutting
down on the number of feature interactions. One such stronger, more
general sublemma relates the monadic bind operation to well-typing:
\begin{multline}
 (\Sigma\vdash_M~~ v_m ~:~t_m) \rightarrow \\
   (\forall v~T~\Sigma'\supseteq\Sigma.~(\Sigma'\vdash~v~:~T) \rightarrow
   ~\Sigma'\vdash_M~~ k_v~v~:~ k_t~T) \rightarrow \\
   \Sigma\vdash_M~~v_m |>>=| k_v~:~t_m |>>=| k_t
\tag{\textsc{WFM-Bind}}\label{thm:WFM+Bind}
\end{multline}

A proof of \textsc{WFM-If-Vc} follows from two applications of this
stronger property. The advantage of \textsc{WFM-Bind} is clear: it can
be reused to deal with case analyses in other proofs of
\ref{thm:FSound}, while a proof of \ref{thm:WFM+If+Vc} has only a
single use. The disadvantage is that \textsc{WFM-Bind} may not hold
for some new effect, while the weaker \ref{thm:WFM+If+Vc} does,
possibly excluding some feature combinations. As \textsc{WFM-Bind} is
a desirable property for typing rules, the case study focuses on that
approach.

% \BD{Maybe we
%should expound on this in the case study section- Lambda uses
%WFM-Bind to cut down on feature interactions. }

%if False
\tom{This a standard law -- or definition of |fmap| -- for monads.
     We should cover it earlier when we define functors and monads.}
This proof relies on the following law to constrain the behavior of the
|MT| monad:

< forall A B (f: A -> B) (m: MT A).
<    fmap f m = m >>= (\ v._ return (f v))
 \BD{Need to label this law better.}

This law simply states that mapping a function over a monadic value is
the same as applying the function to every value it contains. This law
follows from parametricity, but this proof is not available to Coq
without additional axioms. Instead we choose to encode it as an
additional monad law, which can be easily proven on a per-monad
basis. Similar laws governing the behavior of |fmap| in the presence
of other monadic operations have been added to other monads
(i.e. the exception monad).
%endif

%- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
\subsection{Type Soundness for a Pure Language}

The second phase of showing type soundness is to prove a statement of
soundness for a fixed set of effects. For pure effects, the
soundness statement is straightforward:
\begin{equation}
\forall |v_m|~|t|. \vdash_M | v_m : return t| \Rightarrow \exists |v|. |v_m
== return v|~\wedge \vdash |v| : |t|
\tag{\textsc{ESound}$_P$}\label{thm:ESoundP}
\end{equation}

Each effect theorem is proved by induction over the derivation of
$\vdash_M$ |v_m : return t|. \ref{thm:ESoundP} fixes the
irrelevant environment type to the type |()| and the evaluation monad
to the pure monad |Id|. Since the evaluation monad is fixed, the proof
of \ref{thm:ESoundP} only needs to consider the pure typing rules of
Figure~\ref{fig:WFM+Pure}. The proof of the effect theorem is
straightforward: \textsc{WFM-Illtyped} could not have been used to derive
$\vdash_M |v_m : return t|$, and \textsc{WFM-Return} provides both a witness
for |v| and a proof that it is of type |t|.

The statement of soundness for a pure language built from a particular
set of features is similar to \ref{thm:ESoundP}:
\begin{equation}
\forall |e|, |t|. |typeof e == return t| \Rightarrow \exists |v|. |eval e
== return v|~\wedge \vdash |v| : |t|
\tag{\textsc{LSound}}\label{thm:LSoundP}
\end{equation}

The proof of \ref{thm:LSoundP} is an immediate consequence of the
reusable proofs of \ref{thm:FSound} and \ref{thm:ESoundP}. Folding a
proof algebra for \ref{thm:FSound} over |e| provides a proof of
$\vdash_M |eval e : return t|$, satisfying the first assumption of
\ref{thm:ESoundP}.  \ref{thm:LSoundP} follows immediately.

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
This allows us to 'lift' a proof out of any monad with refinement type
whose proof component has been projected out. This allows us to
conclude that all the types in |typeof e| equal |t|, and soundness
follows immediately from the assumptions of
\textsc{WFM-Return}.
\item
Furthermore, a corollary of this law is that
|forall v._ fail <> return v|, which in the \textsc{WFM-Untyped} case
contradicts the assumption that |typeof e == return t|. The latter case
demonstrates the important point that the set of effects is fixed in
the specialized soundness theorems, allowing the proof to reason about
the complete set of operations. In the pure case, for example, the
proof can safely assume that |typeof e| will either equal |fail| or
there will exists some |T| such that |typeof e == return T|. This will
be useful in the next section.
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

\begin{figure}
  \fbox{
  \begin{minipage}{.95\columnwidth}
     \hspace{-2.1cm}\begin{minipage}{1.25\columnwidth}
      \infrule[WFM-Throw]{
      }
      {
        \Sigma \vdash_M |throw x| ~:~ |t_m|
      }
    \vspace{.25cm}
      \infrule[WFM-Catch]
      {
        \Sigma \vdash_M |m >>= k|  ~:~ |t_m| \\
        \forall~\Sigma' \supseteq \Sigma~|x|~.~\Sigma' \vdash_M |h x >>= k| ~:~ |t_m|
      }
      {
         \Sigma \vdash_M |catch m h >>= k| ~:~ |t_m|
      }
  \end{minipage}
  \end{minipage}
 }
\caption{Typing rules for exceptional monadic values.}
\label{fig:WFM+Except}
\vspace{-.4cm}
\end{figure}

%-------------------------------------------------------------------------------
\subsection{Errors}

The evaluation algebra of the error language feature uses the side
effects of the exception monad, requiring new typing rules.

\paragraph{Typing Rules}

Figure~\ref{fig:WFM+Except} lists the typing rules for monadic
computations involving exceptions. \textsc{WFM-Throw} states that
|throw x| is typeable with any type. \textsc{WFM-Catch} states that
binding the results of both branches of a |catch| statement will
produce a monad with the same type. While it may seem odd that this
rule is formulated in terms of a continuation |>>= k|, it is essential
for compatibility with the proofs algebras required by other
features. As described in Section~\ref{sec:Thm+Reuse}, extensible
proof algebras over the typing derivation will now need cases for the
two new rules. To illustrate this, consider the proof algebra for the
general purpose \ref{thm:WFM+Bind} property. This algebra requires a
proof of:
\begin{multline*}
 (\Sigma\vdash_M|catch e h >>= k| ~:~t_m) \rightarrow \\
   (\forall v~T~\Sigma'\supseteq\Sigma.~(\Sigma'\vdash~v~:~T) \rightarrow
   ~\Sigma'\vdash_M~~ k_v~v~:~ k_t~T) \rightarrow \\
   \Sigma\vdash_M(|catch e h >>= k|) |>>=| k_v:t_m |>>=| k_t
\end{multline*}

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

With the continuation, we can first apply the associativity law to
reorder the binds so that \textsc{WFM-Catch} can be applied: |(catch e
h >>= k) >>=| $k_v$ |= catch e h >>= (k >>= |$k_v)$. The two premises
of the rule follow immediately from the inductive hypothesis of the
lemma, finishing the proof. Without the continuation, the proof
statement only binds |catch e h| to |v_m|, leaving no applicable
typing rules.

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
expressions from \ref{sec:Thm+Reuse} is an example of such a proof algebra.\tom{the example needs clarification}
These sorts of proof algebras which are only needed for specific combinations
of features are examples of \textit{feature interactions}. Thankfully, these
sorts of missing algebra can be defined in a separate interaction file without
threatening modularity of the individual features.
\BD{Now that we've improved the previous section, we can flesh out the
discussion of how these proof algebras work now. This is the perfect
place to discuss wfvm\_bind versus the 'weakest possible' rules.}
%endif

\paragraph{Effect Theorem} The effect theorem, \ref{thm:ESoundE}, for a
language whose only effect is exceptions reflects that the evaluation
function is either a well-typed value or an exception.
\begin{multline}
\forall |v_m|~|t|. \vdash_M |v_m : return t| \Rightarrow \\
\exists x. |v_m == throw |~x \lor \exists |v|. |v_m == return v| \wedge \vdash |v| :
|t|
\tag{\textsc{ESound$_E$}}\label{thm:ESoundE}
\end{multline}
The proof of \ref{thm:ESoundE} is again by induction on the derivation
of $ \vdash_M$ |v_m : return t|. The irrelevant environment
can be fixed to |()|, while the evaluation monad is the
exception monad |ExcT x Id|.

The typing derivation is built from four rules: the two pure rules
from Figure~\ref{fig:WFM+Pure} and the two exception rules from
Figure~\ref{fig:WFM+Except}.  The case for the two pure rules is
effectively the same as before, and \textsc{WFM-Throw} is
straightforward. In the remaining case, |v_m == catch e' h|, and we can
leverage the fact that the evaluation monad is fixed to conclude that
either $\exists |v|.|e' == return v|$ or $\exists |x|. |e' == throw
x|$. In the former case, |catch e' h| can be reduced using
|catch_return|, and the latter case is simplified using
|catch_throw1|. In both cases, the conclusion then follows immediately
from the assumptions of \textsc{WFM-Catch}.  The proof of the language
theorem \ref{thm:SoundE} is similar to \ref{thm:LSoundP} and is easily
built from \ref{thm:ESoundE} and \ref{thm:FSound}.

\begin{figure}
  \fbox{
  \begin{minipage}{.95\columnwidth}
     \hspace{-1.5cm}\begin{minipage}{1.15\columnwidth}
      \infrule[WFM-Get]
      {
        \forall \sigma, \Sigma\vdash\sigma~\rightarrow~\Sigma \vdash_M k~\sigma:t_m
      }
      {
        \Sigma \vdash_M \hspace{-.5cm}
        \parbox{2cm}{
          \begin{spec}
            get >>=
          \end{spec}
        } \hspace{-.5cm}
        k~:~t_m
      }
      \vspace{.25cm}
      \infrule[WFM-Put]
      {
         \Sigma' \vdash \sigma \andalso
         \Sigma' \supseteq \Sigma \andalso
         \Sigma' \vdash_M k : t_m
      }
      {
       \Sigma \vdash_M \hspace{-.5cm}
         \parbox{2cm}{
          \begin{spec}
             put s_ >> k
          \end{spec}
        } : t_m
      }
  \end{minipage}
  \end{minipage}
 }
\caption{Typing rules for stateful monadic values.}
\label{fig:WFM+State}
\vspace{-.4cm}
\end{figure}

%-------------------------------------------------------------------------------
\subsection{References}

\paragraph{Typing Rules}

Figure~\ref{fig:WFM+State} lists the two typing rules for stateful
computations.  To understand the formulation of these rules, consider
\ref{thm:SoundS}, the statement of soundness for a language with a
stateful evaluation function. The statement accounts for both the
typing environment $\Sigma$ and evaluation environment $\sigma$ by
imposing the invariant that $\sigma$ is well-formed with respect
to $\Sigma$. \ref{thm:FSound} however, has no such conditions (which
would be anti-modular in any case). We avoid this problem by
accounting for the invariant in the typing rules themselves:

\begin{itemize}
\item \textsc{WFM-Get} requires that the continuation |k| of a
|get| is well-typed under the invariant.

\item \textsc{WFM-Put} requires that any newly installed
environment maintains this invariant.
\end{itemize}
The intuition behind these premises is that effect theorems will
maintain these invariants in order to apply the rules.

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

The effect theorem for mutable state proceeds again by induction over
the typing derivation. The evaluation monad is fixed to |StateT Sigma
Id| and the environment type is fixed to |[Type]| with the obvious
definitions for $\supseteq$.

\begin{itemize}
\item
The proof case for the two pure rules is again straightforward.
\item
For \textsc{WFM-Get} we have that |put|~$\sigma$~|>> eval e ==
put|~$\sigma$~|>> get >>= k|. After reducing this to |k| $\sigma$ with the
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
PHOAS~\cite{PHOAS} to avoid many of the boilerplate definitions and
proofs about term well-formedness found in first-order
representations.
%The parametricity of the expression functor requires
%the soundness proofs to induct over an equivalence relation, the
%details of which are covered in the MTC paper~\cite{mtc}.

\paragraph{The Environment Effect} Unlike in MTC, \name neatly hides
the variable environment of the evaluation function with a reader
monad |MonadReader|. This new effect introduces the two new typing
rules listed in Figure~\ref{fig:WFM+Environment}.  Unsurprisingly,
these typing rule are similar to those of
Figure~\ref{fig:WFM+State}. The rule for |ask| is essentially the same
as \textsc{WFM-Get}. The typing rule for |local| differs slightly from
\textsc{WFM-Put}. Its first premise ensures that whenever |f| is applied
to an environment that is well-formed in the original typing
environment $\Gamma$, the resulting environment is well-formed in some
new environment $\Gamma'$. The second premise ensures the body of
|local| is well-formed in this environment according to some type |T|,
and the final premise ensures that |k| is well-formed when applied to
any value of type |T|. The intuition behind binding the |local|
expression in some |k| is the same as with |put|.


\begin{figure}
  \fbox{
  \begin{minipage}{.95\columnwidth}
      \infrule[WFM-Ask]
      {
        \forall \gamma.~\Gamma\vdash\gamma~ \rightarrow
        ~\Gamma \vdash_M k~\gamma:t_m
      }
      {
        \Gamma \vdash_M \hspace{-.5cm}
        \parbox{2cm}{
          \begin{spec}
            ask >>=
          \end{spec}
        } \hspace{-.5cm}
        k~:~t_m
      }
      \vspace{.25cm}
      \infrule[WFM-Local]
      {
          \forall~\gamma.~\Gamma\vdash\gamma \rightarrow
          \Gamma'\vdash f~\gamma \andalso
          \Gamma' \vdash_M m~:~\mathit{return}~~t'_m \\
          \forall v.~\vdash v~:~t'_m \rightarrow \Gamma \vdash_M (k~v) : t_m \andalso
      }
      {
        \Gamma \vdash_M \hspace{-.4cm}
          \parbox{2cm}{
           \begin{spec}
              local f m >>= k
           \end{spec}
         } \hspace{.4cm}~:~t_m
      }
      \vspace{.25cm}
      \infrule[WFM-Bot]{}{
        \Gamma \vdash_M \bot ~:~ |t_m|
      }
  \end{minipage}
}
\caption{Typing rules for environment and failure monads.}
\label{fig:WFM+Environment}
\vspace{-.4cm}
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

\paragraph{The Non-Termination Effect}
The lambda feature also introduces the possibility of non-termination to the
evaluation function, which is disallowed by Coq. MTC solves this problem by
combining \textit{mixin algebras} with a bounded fixpoint function. This
function applies an algebra a bounded number of times, returning a $\bot$ value
when the bound is exceeded.  Because MTC represented $\bot$ as a value, all
evaluation algebras needed to account for it explicitly. In the monadic
setting, \name elegantly represents $\bot$ with the |fail| primitive of the
failure  monad. This allows terminating features to be completely oblivious to
whether a bounded or standard fold is used for the evaluation function,
resulting in a much cleaner semantics. \textsc{WFM-Bot} allows $\bot$ to have any type.
