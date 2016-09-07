%include lhs2TeX.fmt
%include polycode.fmt
%include forall.fmt
%include macros.fmt
%include Formatting.fmt

\section{Monolithic Type Safety}
%- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
\subsection{Pure Language}

The second phase of showing type soundness is to prove a statement of
soundness for a fixed set of effects. For pure effects, the
soundness statement is straightforward:
\begin{equation}
\forall |v_m|~|t|. \vdash_M | v_m : return t| \Rightarrow \exists |v|. |v_m
== return v|~\wedge \vdash |v| : |t|
\tag{\textsc{ESound}$_P$}\label{thm:ESoundP}
\end{equation}

Each effect theorem is proved by induction over the derivation of $\vdash_M$
|v_m : return t|. \ref{thm:ESoundP} fixes the irrelevant environment type to the
type |()| and the evaluation monad to the pure monad |Id|. Since the evaluation
monad is fixed, the proof of \ref{thm:ESoundP} only needs to consider the pure
typing rules of Figure~\ref{fig:WFM+Pure}. The proof of the effect theorem is
straightforward: \textsc{WFM-Illtyped} could not have been used to derive
$\vdash_M |v_m : return t|$, and \textsc{WFM-Return} provides both a witness for
|v| and a proof that it is of type |t|.

The statement of soundness for a pure language built from a particular set of
features is similar to \ref{thm:ESoundP}:
\begin{equation}
\forall |e|, |t|. |typeof e == return t| \Rightarrow \exists |v|. |eval e
== return v|~\wedge \vdash |v| : |t|
\tag{\textsc{LSound}}\label{thm:LSoundP}
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

The evaluation algebra of the error language feature uses the side effects of
the exception monad, requiring new typing rules.

\paragraph{Typing Rules}

Figure~\ref{fig:WFM+Except} lists the typing rules for monadic computations
involving exceptions. \textsc{WFM-Throw} states that |throw x| is typeable with
any type. \textsc{WFM-Catch} states that binding the results of both branches of
a |catch| statement will produce a monad with the same type. While it may seem
odd that this rule is formulated in terms of a continuation |>>= k|, it is
essential for compatibility with the proofs algebras required by other
features. As described in Section~\ref{sec:Thm+Reuse}, extensible proof algebras
over the typing derivation will now need cases for the two new rules. To
illustrate this, consider the proof algebra for the general purpose
\ref{thm:WFM+Bind} property. This algebra requires a proof of:
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

With the continuation, we can first apply the associativity law to reorder the
binds so that \textsc{WFM-Catch} can be applied: |(catch e h >>= k) >>=| $k_v$
|= catch e h >>= (k >>= |$k_v)$. The two premises of the rule follow immediately
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

The typing derivation is built from four rules: the two pure rules from
Figure~\ref{fig:WFM+Pure} and the two exception rules from
Figure~\ref{fig:WFM+Except}.  The case for the two pure rules is effectively the
same as before, and \textsc{WFM-Throw} is straightforward. In the remaining
case, |v_m == catch e' h|, and we can leverage the fact that the evaluation
monad is fixed to conclude that either $\exists |v|.|e' == return v|$ or
$\exists |x|. |e' == throw x|$. In the former case, |catch e' h| can be reduced
using |catch_return|, and the latter case is simplified using |catch_throw1|. In
both cases, the conclusion then follows immediately from the assumptions of
\textsc{WFM-Catch}.  The proof of the language theorem \ref{thm:SoundE} is
similar to \ref{thm:LSoundP} and is easily built from \ref{thm:ESoundE} and
\ref{thm:FSound}.

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

Figure~\ref{fig:WFM+State} lists the two typing rules for stateful computations.
To understand the formulation of these rules, consider \ref{thm:SoundS}, the
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

The effect theorem for mutable state proceeds again by induction over the typing
derivation. The evaluation monad is fixed to |StateT Sigma Id| and the
environment type is fixed to |[Type]| with the obvious definitions for
$\supseteq$.

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
PHOAS~\cite{PHOAS} to avoid many of the boilerplate definitions and proofs about
term well-formedness found in first-order representations.
%The parametricity of the expression functor requires
%the soundness proofs to induct over an equivalence relation, the
%details of which are covered in the MTC paper~\cite{mtc}.

\paragraph{The Environment Effect} Unlike in MTC, \name neatly hides the
variable environment of the evaluation function with a reader monad
|MonadReader|. This new effect introduces the two new typing rules listed in
Figure~\ref{fig:WFM+Environment}.  Unsurprisingly, these typing rule are similar
to those of Figure~\ref{fig:WFM+State}. The rule for |ask| is essentially the
same as \textsc{WFM-Get}. The typing rule for |local| differs slightly from
\textsc{WFM-Put}. Its first premise ensures that whenever |f| is applied to an
environment that is well-formed in the original typing environment $\Gamma$, the
resulting environment is well-formed in some new environment $\Gamma'$. The
second premise ensures the body of |local| is well-formed in this environment
according to some type |T|, and the final premise ensures that |k| is
well-formed when applied to any value of type |T|. The intuition behind binding
the |local| expression in some |k| is the same as with |put|.


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

\paragraph{The Partiality Effect}
The lambda feature also introduces the possibility of non-termination to the
evaluation function, which is disallowed by Coq. MTC solves this problem by
combining \textit{mixin algebras} with a bounded fixpoint function. This
function applies an algebra a bounded number of times, returning a $\bot$ value
when the bound is exceeded.  Because MTC represented $\bot$ as a value, all
evaluation algebras needed to account for it explicitly. In the monadic setting,
\name elegantly represents $\bot$ with the |fail| primitive of the failure
monad. This allows terminating features to be completely oblivious to whether a
bounded or standard fold is used for the evaluation function, resulting in a
much cleaner semantics. \textsc{WFM-Bot} allows $\bot$ to have any type.


%%% Local Variables:
%%% mode: latex
%%% TeX-master: "../../mod"
%%% End:
