%include lhs2TeX.fmt
%include polycode.fmt
%include forall.fmt
%include macros.fmt
%include Formatting.fmt

%if False

> {-# OPTIONS -XRankNTypes -XImpredicativeTypes -XTypeOperators -XMultiParamTypeClasses -XFlexibleInstances -XOverlappingInstances -XFlexibleContexts #-}

> module Elaboration where

%endif

\section{Monadic Type Safety}

As demonstrated in Section \ref{ssec:mod:effectdependenttheorems}, soundness
theorem which hardwire the set of effects limit their modularity by rendering
proofs for soundness with distinct effects incompatible. In this Section we
discuss how to split type soundness into smaller theorems and how to generalize
the parts for modularization.

%-------------------------------------------------------------------------------
\subsection{Three-Step Approach}

In order to preserve a measure of modularity, we do not prove type soundness
directly for a given feature, but by means of more generic theorems. In order to
maximize compatibility, the statement of the type soundness theorem of a feature
cannot hardwire the set of effects. This statement must instead rephrase type
soundness in a way that can adapt to any superset of a feature's effects. Hence,
similar to the modularization of the semantics in Section
\ref{sec:mod:monadicsemantics}, the idea is to abstract over any monad that
provides the effects of a feature.

%if False
The technique of proving a theorem of interest by means of a more general
theorem is well-known. For a conventional monolithic language, for instance,
type soundness is often established for any well-formed typing context, even
though the main interest lies with the more specific initial, empty context.  In
that setting, the more general theorem produces a weaker induction hypothesis
for the theorem's proof.
%endif

Our approach to state and prove type soundness of features, is to establish that
the monadic evaluation and typing algebras of a feature satisfy an extensible
well-typing relation of computations, defined in terms of effect-specific typing
rules. This relation forms the basis of a \emph{feature theorem} that has
\emph{uniform shape} independent of specific features or effects (except for
constraints on the monad). A feature's proof algebra for the feature theorem
only uses the typing rules required for the effects specific to that
feature. The final language combines the typing rules of all the language's
effects into a closed relation and the \emph{feature theorem} for the complete
set of features into a type soundness theorem of the whole language.

As discussed in Section \ref{ssec:mod:effectdependenttheorems} the type
soundness statement of a language still depends on the set of effects of all the
features of a language. The statement is however independent of the set of
features. This allows us to split the type soundness theorem further into a
reusable \emph{effect theorem} and a \emph{language theorem}. In summary, we
split the type soundness into three kinds of theorems:

\begin{itemize}
\item
  \FSound: a reusable \emph{feature theorem} that is only aware of the effects
  that a feature uses,

\item
  \ESound: an \emph{effect theorem} for a fixed set of known effects, and

\item
  \LSound: a \emph{language theorem} which combines the two to prove soundness
  for a specific language.
\end{itemize}

\begin{figure}[t]
  \fbox{
  \includegraphics[width=.96\columnwidth]{src/ModEffects/Figures/Dependency-1.pdf}
   }
\caption{Dependency Graph}
\label{fig:Dep-Graph}
\end{figure}
\steven{There is an edge missing from FSound of Ref to LSound of AR.}


Figure~\ref{fig:Dep-Graph} illustrates how these reusable pieces fit together to
build a proof of soundness. Each feature provides a proof algebra for
\ref{thm:FSound} which relies on the typing rules (\textsc{WFM-X}) for the
effects it uses. Each unique statement of soundness for a combination of effects
requires a new proof of \ESound. The proof of \ref{thm:LSoundP} for a particular
language is synthesized entirely from a single proof of \ESound~and a
combination of proof algebras for \FSound.

Note that there are several dimensions of modularity here. A feature's proof of
\ref{thm:FSound} only depends on the typing rules for the effects that feature
uses and can thus be used in any language which includes those typing rules. The
typing rules themselves can be reused by any number of different
features. \ESound~depends solely on a specific combination of effects and can be
reused in any language which supports that unique combination, e.g. both
\LSoundA~and \LSoundAR~use \ESoundES.


% around an extensible relation, which relates two monadic computations.  To
% acheive extensibility, we prove that an extensible relation holds over the
% monadic values of the evaluation function and the typing function of each
% language feature. Each effect will have its own set of typing rules used by
% each feature which uses that effect. The final relation is the composition of
% the typing rules for the set of effects in the final language.

% An important modularity property of the typing rules is that they only depend
% on the effects and not on the features. This enables us to decouple the proof
% that a feature's semantics obeys the extensible relation from the proof that
% the closed relation entails the actual property of interest, type
% soundness. The latter proof does not depend on the particular features
% involved, only on the effects. The rules reflect the other dimension of
% modularity: we can now have effect modules which are independent of language
% features (although the latter depend on the former). Thus, soundness theorems
% need to be proven only once for each combination of effects, and can be reused
% for any language with that combination of effects.

% Figures~\ref{fig:WFM+Pure}-\ref{fig:WFM+Except} provide examples of the
% judgements of this monadic well-formedness relation. In essence, each rule
% defines how to type a monadic value which binds an operation of that
% monad. Each effect-specific soundness proof proceeds by induction on this
% relation; in each case showing how to 'process' this function according to the
% specific set of effects and then using the inductive hypothesis for the
% computation resulting from binding the result.

%-------------------------------------------------------------------------------

\subsection{Typing of Monadic Computations}\label{sec:Thm+Reuse}
\steven{Introduce the typing relation for values first and then the
  one for monadic computations. Make it clear that these are two separate
  things.}
\begin{figure}[t]
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

The computation typing relation has the form: \[ \Sigma \vdash_M v_m : t_m \]
The relation is polymorphic in an environment type |env| and an evaluation monad
type |m|.  The parameters $\Sigma$, $v_m$ and $t_m$ have types |env|, |m Value|
and |Maybe Type| respectively.

The extensible feature theorem \ref{thm:FSound} states that |eval| and |typeof|
are related by the typing relation:

\begin{equation}
  \forall e, \Sigma.\quad\Sigma \vdash_M |eval e| : |typeof e|
\tag{\textsc{FSound}}
\label{thm:FSound}
\end{equation}


% \BO{using |m_e| and
%|m_t| may be confused with the monad type |m|.  Maybe some different
%variable names are better? (This is low priority: if there's time,
%because we need to make sure everything is consistently patched)}.
The modular typing rules for this relation can impose constraints on
the environment type |env| and monad type |m|. A particular language must
instantiate |env| and |m| in a way that satisfies all the
constraints imposed by the typing rules used in its features.

Figure~\ref{fig:WFM+Pure} lists the two base typing rules of this
relation. These do not constrain the evaluation monad and environment types and
are the only rules needed for pure features. The \textsc{(WFM-Illtyped)} rule
denotes that nothing can be said about computations (|m_e|) which are ill-typed.
The \textsc{(WFM-Return)} rule ensures that well-typed computations only yield
values of the expected type.

\subsection{Monolithic Soundness for a Pure Feature}

To see how the reusable theorem works for a pure feature, consider the proof
of soundness for the boolean feature.


\paragraph{Proof} Using the two rules of Figure \ref{fig:WFM+Pure}, we can show
that \ref{thm:FSound} holds for the boolean feature. The proof has two cases.
The boolean literal case is handled by a trivial application of
\textsc{(WFM-Return)}. The second case, for conditionals, is more
interesting\footnote{We omit the environment $\Sigma$ to avoid clutter.}:
%
\begin{align*}
\begin{array}{l}
  (\vdash_M |eval e_c| : |typeof e_c|) \rightarrow
  (\vdash_M |eval e_t| : |typeof e_t|) \rightarrow
  (\vdash_M |eval e_e| : |typeof e_e|) \rightarrow \\ \\
  %\multicolumn{2}{l}{
  \vdash_M
  \left(
    \hspace{-8mm}
    \begin{minipage}{43mm}
      \begin{spec}
        do
          v <- eval e_c
          case isBool v of
            Just b   ->
              if b  then eval e_t
                    else eval e_e
            Nothing  -> stuck
      \end{spec}
    \end{minipage}
  \right) :
  \left(
    \hspace{-8mm}
    \begin{minipage}{43mm}
      \begin{spec}
        do
          t_c <- typeof e_c
          t_t <- typeof e_t
          t_e <- typeof e_e
          guard (isTBool t_c)
          guard (eqT t_t t_e)
          return t_t
      \end{spec}
  \end{minipage}
  \right)
  %}
  \\
\end{array}
\tag{\textsc{WFM-If-Vc}}
\label{thm:WFM+If+Vc}
\end{align*}

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

Because |eval| and |typeof| are polymorphic in the monad, we cannot directly
inspect the values they produce. We can, however, perform case analysis on the
derivations of the proofs produced by the induction hypothesis that the
subexpressions are well-formed,
$\vdash_M$~|eval e_c|~:~|typeof e_c|,
$\vdash_M$~|eval e_t|~:~|typeof e_t|, and
$\vdash_M$~|eval e_e|~:~|typeof e_e|.
The final rule used in each derivation determines the shape of the monadic value
produced by |eval| and |typeof|.  Assuming that only the pure typing rules of
Figure~\ref{fig:WFM+Pure} are used for the derivations, we can divide the proof
into two cases depending on whether |e_c|, |e_t|, or |e_e| was typed with
\textsc{(WFM-Illtyped)}.

\begin{itemize}
\item
  If any of the three derivations uses \textsc{(WFM-Illtyped)}, the result of
  |typeof| is |fail|. Hence \textsc{(WFM-Illtyped)} resolves the case.

\item
  Otherwise, each of the subderivations was built with \textsc{(WFM-Return)} and
  the evaluation and typing expressions can be simplified using the
  |return_bind| monad law.

  \begin{align*}
    \begin{array}{l}
    \vdash_M
    \left(
      \hspace{-8mm}
      \begin{minipage}{47mm}
        \begin{spec}
          case isBool v_c of
             Just b ->
               if b  then return v_t
                     else return v_e
             Nothing  -> stuck
        \end{spec}
      \end{minipage}
    \right) :
    \left(
      \hspace{-8mm}
      \begin{minipage}{43mm}
        \begin{spec}
          do
            guard (isTBool t_c)
            guard (eqT t_t t_e)
            return t_t
        \end{spec}
      \end{minipage}
    \right)
    \end{array}
  \end{align*}

  After simplification, the typing expression has replaced the bind with
  explicit values which can be reasoned with. If |isTBool t_c| is |false|, then
  the typing expression reduces to |fail| and well-formedness again follows from
  the \textsc{WFM-Illtyped} rule. Otherwise |t_c == TBool|, and we can apply the
  canonical forms lemma
    \[ \vdash |v| : |TBool| \rightarrow \exists b. |isBool v == Just b| \]
  to establish that |v_c| is of the form |Just b|, reducing the evaluation to
  either |return v_e| or |return v_t|. A similar case analysis on |eqT t_t t_e|
  will either produce |fail| or |return t_t|. The former is trivially true, and
  both $\vdash_M |return v_t|:|return t_t|$ and $\vdash_M |return v_e|:|return
  t_t|$ hold in the latter case from the induction hypotheses.

  % \tom{Need more clarification here.}
  % In the \textsc{WFM-Return} case, |(do v_c <- eval c; ...)| simplifies to
  % either |Stuck|, |eval t|, or |eval e|. In the first case, we can push the
  % type information in the refinement type of |T_c'| from the
  % \textsc{WFM-Return} rule used to build the current case into the body of the
  % bind expression to ensure that |do T_c <- typeof c; ...| will evaluate to
  % |fail|, from which \textsc{WFM-Untyped} applies. The refinement type of the
  % |T_c'| monad can be used analogously in the other two cases to ensure that
  % |typeof c| always produces |TBool|, and \textsc{WFM-Return} can then be
  % applied.
\end{itemize}

\subsection{Modular Sublemmas}
The above proof assumed that only the pure typing rules of
Figure~\ref{fig:WFM+Pure} were used to type the subexpressions of the |if|
expression, which is clearly not the case when the boolean feature is included
in an effectful language. Instead, case analyses are performed on the extensible
typing relation in order to make the boolean feature theorem compatible with new
effects. Case analyses over the extensible $\vdash_M$ relation are accomplished
using extensible proof algebras which are folded over the derivations provided
by the induction hypothesis, as outlined in
Sections~\ref{ssec:mod:modularproofs} and \ref{ssec:modpred:proofs}.


In order for the boolean feature's proof of \ref{thm:FSound} to be compatible
with a new effect, each extensible case analysis requires a proof algebra for
the new typing rules the effect introduces to the $\vdash_M$ relation.  More
concretely, the conditional case of the previous proof can be dispatched by
folding a proof algebra for the property \ref{thm:WFM+If+Vc} over
$\vdash_M~|eval v_c|~:~|typeof t_c|$. Each new effect induces a new case for
this proof algebra, however.

These proof algebras are examples of
\emph{interactions}~\cite{featureinteractions} from the setting of modular
component-based frameworks. In essence, an interaction is functionality (e.g., a
function or a proof) that is only necessary when two components are combined.
Our case is an interaction between the boolean feature and any effect.

Importantly, these proof algebras do not need to be provided up front when
developing the boolean algebra, but can instead be modularly resolved by later
by separate proof algebras for the interaction of the boolean feature and each
effect.

Nevertheless, the formulation of the properties proved by extensible case
analysis has an impact on modularity.  \ref{thm:WFM+If+Vc} is specific to the
proof of \ref{thm:FSound} in the boolean feature; proofs of \ref{thm:FSound} for
other features require different properties and thus different proof
algebras. Relying on such specific properties can lead to a proliferation of
proof obligations for each new effect.


\subsection{Reusable Bind Sublemma}

Alternatively, the boolean feature can use a proof algebra for a stronger
property that is also applicable in other proofs, cutting down on the number of
feature interactions. One such stronger, more general sublemma relates the
monadic bind operation to well-typing:

\begin{figure}[t]
  \fbox{
  \begin{minipage}{.95\columnwidth}
      \hspace{-1cm} \infrule[WFM-Bind] {
        \Sigma\vdash_M v_m : t_m \\
        (\forall v~T~\Sigma'. (\Sigma'\supseteq\Sigma) \rightarrow (\Sigma'\vdash v : T) \rightarrow (\Sigma'\vdash_M k_v~v : k_t~T))
      }
      {
       \Sigma\vdash_M (v_m |>>=| k_v) : (t_m |>>=| k_t)
      }
  \end{minipage}
 }
\caption{Reusable sublemma for monadic binds.}
\label{fig:WFM+Pure}
\vspace{-.4cm}
\end{figure}


%% \begin{multline}
%%   \rightarrow \\
%%     \rightarrow \\
%% \end{multline}

A proof of \textsc{WFM-If-Vc} follows from two applications of this stronger
property. The advantage of \textsc{WFM-Bind} is clear: it can be reused to deal
with case analyses in other proofs of \ref{thm:FSound}, while a proof of
\ref{thm:WFM+If+Vc} has only a single use. The disadvantage is that
\textsc{WFM-Bind} may not hold for some new effect, while the weaker
\ref{thm:WFM+If+Vc} does, possibly excluding some feature combinations. As
\textsc{WFM-Bind} is a desirable property for typing rules, the case study
focuses on that approach.

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

 This law simply states that mapping a function over a monadic value is the same
 as applying the function to every value it contains. This law follows from
 parametricity, but this proof is not available to Coq without additional
 axioms. Instead we choose to encode it as an additional monad law, which can be
 easily proven on a per-monad basis. Similar laws governing the behavior of
 |fmap| in the presence of other monadic operations have been added to other
 monads (i.e. the exception monad).
%endif

%%% Local Variables:
%%% mode: latex
%%% TeX-master: "../../mod"
%%% End:
