%include lhs2TeX.fmt
%include polycode.fmt
%include forall.fmt
%include macros.fmt

\begin{figure*}[t]
  \begin{center}
  \fbox{
        \includegraphics[scale = .85]{src/ModEffects/Figures/CaseStudyFigure.pdf}
   }
  \end{center}
  \caption{Dependency and size information for the features and effects used in the case study.}
  \label{fig:codesize}
\end{figure*}

\section{Case Study}
\label{sec:CaseStudy}

As a demonstration of the \Name~framework, we have built a set of five
reusable language features and combined them to build a family of
languages which includes a mini-ML~\cite{clement86mini-ML} variant
with references and errors. The study includes pure boolean and
arithmetic features as well as effectful features for references,
errors and lambda abstractions.

The study builds twenty eight different combinations of the features which are
all possible combinations with at least one feature providing
values.\footnote{Also available at \url{http://www.cs.utexas.edu/~bendy/3MT}}
Figure~\ref{fig:MiniMLSyntax} presents the syntax of the expressions,
values, and types provided; each line is annotated with the feature
that provides that set of definitions.

Four kinds of feature interactions appear in the case study.

\begin{itemize}

\item The PHOAS representation of binders requires an auxiliary
equivalence relation, the details of which are covered in the MTC
paper~\cite{mtc}. The soundness proofs of language theorems for
languages which include binders proceed by induction over this
equivalence relation instead of expressions. The reusable feature
theorems of other features need to be lifted to this equivalence
relation.

\item The effect theorems that feature an environment
typing $\Sigma$, such as those for state or environment, need a weakening sublemma
which
states
that each well-formed value under
$\Sigma$ is also well-formed under a conservative extension:
\[\Sigma \vdash v ~:~ t  \\ \rightarrow \\
  \Sigma' \supseteq \Sigma \\ \rightarrow \\
  \Sigma' \vdash v ~:~ t \]
\item Inversion lemmas for the well-formed value relation as in the
proof of \ref{thm:FSound} for the boolean feature in
Section \ref{sec:Thm+Reuse} are proven by induction over the
relation.

%% \item The sublemmas of reusable feature theorems for properties such as
%% \textsc{WFM-If-Vc} are
%% proven by induction over the extensible typing relation. When effectful
%% features introduce new judgements to the relation, these new
%% judgements must have proof algebra instances for the sublemmas.

\end{itemize}


The proofs of the first and second kind of feature interactions are
straightforward; the inversion lemmas of the third kind can be
dispatched by tactics hooked into the type class inference algorithm.
%% The last kind of interactions require more work and comprise the
%% biggest part of the code dealing with feature interactions.
%%
%% The presented typing rules for effects satisfy the \textsc{WFM-Bind}
%% property; as previously discussed, it can be used cut down on feature
%% interactions. The lambda feature uses \textsc{WFM-Bind} in its proof
%% of \ref{thm:FSound} instead of targeted sublemmas. The following table
%% shows the number of sublemmas used by the reusable feature theorems,
%% highlighting that the \textsc{WFM-Bind} property provides significantly
%% more convenience despite its stronger assumptions.

%if False
\begin{figure}[t]
  \begin{center}
    \begin{minipage}{\columnwidth}
    \begin{tabular}{cc}
      \begin{minipage}{.48\columnwidth}
        \hspace{-.3cm}
        \fbox{
        \hspace{-.3cm}
          \begin{tabular}{lr}
            \textit{Arith}      &   878 \\
            \textit{Bool}       &   955 \\
            \textit{Errors}     &   590 \\
            \textit{References} &  1085 \\
            \textit{Lambda}     &  1549 \\
          \end{tabular}
        }
      \end{minipage} &
      \begin{minipage}{.38\columnwidth}
        \hspace{-.3cm}
        \fbox{
        \hspace{-.3cm}
          \begin{tabular}{lr}
            \textit{Pure}         & 134 \\
            \textit{Exception}    & 145 \\
            \textit{State}        &  90 \\
            \textit{Environment}  & 107 \\
            \textit{Failure}      &  54 \\
          \end{tabular}
        }
      \end{minipage}
    \end{tabular}
    \end{minipage}
    \begin{minipage}{\columnwidth}
      \begin{center}
        \fbox{
        \hspace{-.3cm}
          \begin{tabular}{lrlr}
            $P$  &  93    &   $ES$   & 297  \\
            $E$  & 126    &   $ERF$  & 211  \\
            $S$  & 164    &   $SRF$  & 274  \\
            $RF$ & 162    &   $ESRF$ & 405  \\
          \end{tabular}
        }
      \end{center}
    \end{minipage}
  \end{center}
  \caption{Implementation size in LoC}
  \label{fig:codesize}
\end{figure}
% https://docs.google.com/spreadsheet/ccc?key=0Akyoo1cBki3JdFRMU2lBdHJ3TzNwdjk5c2xNX1NNeVE&usp=sharing
%endif

The framework itself consists of about 4,400 LoC of which about 2,000
LoC comprise the implementation of the monad transformers and their
algebraic laws. The size in LoC of the implementation of semantic
evaluation and typing functions and the reusable feature theorem for
each language feature is given in the left box in Figure
\ref{fig:codesize}. The right box lists the sizes of the effect
theorems. Each language needs on average 110 LoC to assemble its
semantic functions and soundness proofs from those of its features and
the effect theorem for its set of effects.


\input{src/ModEffects/Figures/MiniMLSyntax}

%% \begin{center}
%%   \fbox{
%%   \hspace{-.3cm}
%%     \begin{tabular}{ c c c c c }
%%       \textit{Arith} & \textit{Bool} & \textit{Errors} & \textit{References} & \textit{Lambda} \\
%%       2 & 3 & 0 & 4 & 0 \\
%%     \end{tabular}
%%   }
%% \end{center}
%% Each sublemma of the above table requires on average 50 LoC per effect.
