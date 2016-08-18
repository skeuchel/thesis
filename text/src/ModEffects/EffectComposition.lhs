%include lhs2TeX.fmt
%include polycode.fmt
%include forall.fmt
%include macros.fmt
%include Formatting.fmt

%if False

> {-# OPTIONS -XRankNTypes -XImpredicativeTypes -XTypeOperators -XMultiParamTypeClasses -XFlexibleInstances -XOverlappingInstances -XFlexibleContexts #-}

> module Elaboration where

%endif

%===============================================================================
\section{Effect Compositions}

As we have seen, laws are essential for proofs of
\ref{thm:FSound}. The proofs so far have involved only one effect and
the laws regulate the behavior of that effect's primitive operations.

Languages often involve more than one effect, however. Hence, the
proofs of effect theorems must reason about the interaction between
multiple effects.  There is a trade-off between fully instantiating
the monad for the language as we have done previously, and continuing
to reason about a constrained polymorphic monad. The former is easy
for reasoning, while the latter allows the same language proof to be
instantiated with different implementations of the monad. In the latter case,
additional \emph{effect interaction} laws are required.

%\BD{This section needs a discussion of the two candidate rules for
%how put and catch interact. This reflects the fact that sometimes
%there aren't single laws governing the interactions of effects. In
%this case, this is okay: we can prove the lemma for either
%choice. Plus, since only the catch feature needs this rule, the other
%effect rules are independent of this choice. }

%-------------------------------------------------------------------------------
\subsection{Languages with State and Exceptions}

Consider the effect theorem which fixes the evaluation monad to
support exceptions and state. The statement of the theorem mentions
both kinds of effects by requiring the evaluation function to be run
with a well-formed state $\sigma$ and by concluding that well-typed
expressions either throw an exception or return a value. The
\textsc{WFM-Catch} case this theorem has the following goal:
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
them by a $|put|~\sigma$.  Hence, |put| $\sigma$ must be pushed under the |catch|
statement through the use of a law governing the behavior of |put| and |catch|.
There are different choices for this law, depending on the monad
that implements both |MonadState| and |MonadError|. We consider
two reasonable choices, based on the monad transformer compositions |ExcT x (StateT s Id)|
and |StateT s (ExcT x Id)|:
\begin{itemize}
\item Either |catch| passes the current state into the handler:\\
 |put s_ >> catch e h == catch (put s_ >> e) h|
\item Or |catch| runs the handler with the initial state:\\
|put s_ >> catch e h == catch (put s_ >> e) (put s_ >> h)|
\end{itemize}
% There are other, more exotic interactions possible, but these two (alternative) rules capture the
% standard understanding of how languages with exceptions and environments may work.
The \textsc{WFM-Catch} case is provable under either choice.
As the \ref{thm:SoundES} proof
is written as an extensible theorem, the two cases are written as
two separate proof algebras, each with a different assumption about
the behavior of the interaction. Since the cases for the other rules are
impervious to the choice, they can be reused with either proof of
\textsc{WFM-Catch}.

% In either case, |catch| can be reduced further. If |put s_ >> eval e =
% put s_' >> return v| the inductive hypothesis for |e| can be
% applied. Alternatively, when |put s_ >> eval e = put s' >> throw t|,
% the inductive hypothesis for |k| can be applied using |s'| and the
% extended context $\Sigma'$ produced by the inductive hypothesis for
% |e|. Note that \textsc{WFM-Catch} types |h >>= k| under all $\Sigma'$
% precisely so that in the case that |catch| pass the effects from |eval
% e| to the handler the proof can account for the extended environment.

\begin{figure}
\noindent\fbox{
\begin{minipage}{.93\columnwidth}
\vspace{-.2cm}
\begin{gather*}
\forall \Sigma,\Gamma,\delta,\gamma,\sigma,|e|_E,|e|_T.
  \left\{\begin{array}{c}
   \gamma,\delta\vdash~|e|_E\equiv|e|_T \\
   \Sigma \vdash \sigma~:~\Sigma \\
   \Sigma \vdash \gamma~:~\Gamma \\
  |typeof e|_T| == return t| \\
  \end{array}\right\}
\rightarrow \\
\exists~\Sigma',\sigma',|v|.
  \left\{\begin{array}{c}
  |local (\ _._| \gamma |) (put|~\sigma |>> eval e|_E|)| \\
   |== local (\ _._| \gamma |) (put|~\sigma' |>> return v)| \\
  \Sigma' \vdash |v| : |t| \\
  \end{array}\right\} \\
 \vee \\
\exists~\Sigma',\sigma',|v|.
  \left\{\begin{array}{c}
  |local (\ _._| \gamma |) (put|~\sigma |>> eval e|_E|)| \\
  |== local (\ _._| \gamma |(put|~\sigma' |>>| \bot |)| \\
  \Sigma' \vdash \sigma'~:~\Sigma'  \\
  \Sigma' \supseteq \Sigma
  \end{array}\right\} \\
 \vee \\
\exists~\Sigma',\sigma',|v|.
  \left\{\begin{array}{c}
 |local (\ _._| \gamma |) (put|~\sigma |>> eval e|_E|)| \\
 |== local (\ _._| \Gamma |(put|~\sigma' |>> throw t)|  \\
 \Sigma' \vdash \sigma'~:~\Sigma' \\
 \Sigma' \supseteq \Sigma \\
  \end{array}\right\}
 \tag{\textsc{ESound}$_\mathit{ESRF}$}
 \label{thm:ESoundESRF}
\end{gather*}
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
\subsection{Full Combination of Effects}

A language with references, errors and lambda abstractions features
four effects: state, exceptions, an environment and failure. The
language theorem for such a language relies on the effect theorem
\ref{thm:ESoundESRF} given in Figure~\ref{f:th:esrf}. The proof of
\ref{thm:ESoundESRF} is similar to the previous effect theorem proofs, and
makes use of the full set of interaction laws given in
Figure~\ref{fig:Interaction+Laws}. Perhaps the most interesting
observation here is that because the environment monad only makes
local changes, we can avoid having to choose between laws regarding
how it interacts with exceptions. Also note that since we are
representing nontermination using a failure monad |FailMonad m|, the
|catch_fail| law conforms to our desired semantics.

\begin{figure}[!hb]
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

%\BD{Maybe we
%should just move this section and figures to the case study?}

%format throw_A = "\Varid{throw}_\Varid{A}"
%format throw_B = "\Varid{throw}_\Varid{B}"
%format <> = "\not\equiv"
%format MonadErrorState_1 = "\Varid{MonadErrorState}_1"
%format MonadErrorState_2 = "\Varid{MonadErrorState}_2"

% \BO{Maybe it would be worthwhile to say a few more words on these laws.
% The interaction laws tend to be much more application-specific and really pin-down
% particular semantic interactions between effects. We already say something earlier
% regarding |put| and |catch|, but maybe we can have a more general statement and
% also comment on some other laws. For example
% |fail <> throw x|  prevents a particular monad configuration which is when
% exceptions coincide with failure. This is because, in the particular application,
% we intend that exceptions denote exceptional values, whereas failure denotes
% non-termination.}
