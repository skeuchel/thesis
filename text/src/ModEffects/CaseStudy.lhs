%include lhs2TeX.fmt
%include polycode.fmt
%include forall.fmt
%include macros.fmt

% \begin{figure*}[t]
%   \centering
%   \fbox{
%      \includegraphics[width=.96\columnwidth]{src/ModEffects/Figures/CaseStudyFigure.pdf}
%    }
%   \caption{Dependency and size information for the features and effects used in the case study.}
%   \label{fig:codesize}
% \end{figure*}

\section{Case Study}\label{sec:modeffects:casestudy}

\input{src/ModEffects/Figures/MiniMLSyntax}

As a demonstration of the \Name~framework, we have built a set of five reusable
language features and combined them to build a family of languages which
includes a mini-ML~\cite{clement86mini-ML} variant with references and
errors. The study includes pure boolean and arithmetic features as well as
effectful features for references, errors and lambda abstractions.

The study builds twenty eight different combinations of the features which are
all possible combinations with at least one feature providing
values. Figure~\ref{fig:MiniMLSyntax} presents the syntax of the expressions,
values, and types provided; each line is annotated with the feature that
provides that set of definitions.

\begin{table*}[t]
  \centering
  \begin{tabular}{lrrrl}
    \toprule
    \textbf{Module} & \textbf{Spec} & \textbf{Proof} & \textbf{Total} & \textbf{Description}               \\ \midrule
    |MTC|           & 803           & 388            & 1191           & MTC Framework.                     \\
    |MonadLib|      & 1350          & 201            & 1551           & 3MT monad and monad transfomers.   \\
    |Names|         & 358           & 94             & 452            & Type-safety infrastructure.        \\
    |PNames|        & 229           & 100            & 329            & PHOAS type-safety infrastructure.  \\\midrule
    Total           & 2740          & 783            & 3523           &                                    \\
    \bottomrule
  \end{tabular}
  \caption{Size statistic for the 3MT framework for modular effect reasoning}
  \label{tbl:3mt:sizeframework}
\end{table*}

Table \ref{tbl:3mt:sizeframework} gives an overview of the size in \emph{lines
  of code} (LoC) of different parts of the \Name~library. The \Name~library
consists of about 3,550 LoC of which 1,200 LoC comprise the MTC implementation
of modular datatypes and modular induction, 1,550 LoC comprise the
implementation of the monad transformers and their algebraic laws and finally
the infrastructure for monadic type safety consists of 800 LoC.

\begin{table*}[t]
  \centering
  \begin{tabular}{lrrr}
                                                                         \toprule
    \textbf{Module} & \textbf{Spec} & \textbf{Proof} & \textbf{Total} \\ \midrule
    |Pure|          & 79            & 60             & 139            \\
    |Fail|          & 65            & 11             & 76             \\
    |Except|        & 97            & 59             & 156            \\
    |Reader|        & 95            & 24             & 119            \\
    |State|         & 107           & 20             & 127            \\ \midrule
    Total           & 483           & 174            & 657            \\ \bottomrule
  \end{tabular}
  \caption{Size statistics of the monadic value typing relations.}
  \label{tbl:3mt:sizemonadictyping}
\end{table*}

A breakdown of the size of the effect implementation is given in Table
\ref{tbl:3mt:sizemonadictyping}. These include the modular typing rules for the
specified effect and a proof algebra for the reusable bind lemma of these rules.

\begin{table*}[t]
  \centering
  \begin{tabular}{lrrr}
                                                                         \toprule
    \textbf{Module} & \textbf{Spec} & \textbf{Proof} & \textbf{Total} \\ \midrule
    |Arith|         & 524           & 110            & 634            \\
    |Bool|          & 590           & 122            & 712            \\
    |Error|         & 348           & 60             & 408            \\
    |Ref|           & 895           & 229            & 1124           \\
    |Lambda|        & 840           & 173            & 1013           \\ \midrule
    |ArithEqv|      & 158           & 13             & 171            \\
    |BoolEqv|       & 174           & 14             & 188            \\
    |ErrorEqv|      & 145           & 14             & 159            \\
    |RefEqv|        & 229           & 16             & 245            \\ \midrule
    |Lambda_Arith|  & 40            & 16             & 56             \\
    |Lambda_Bool|   & 40            & 16             & 56             \\
    |Lambda_Ref|    & 53            & 35             & 88             \\ \midrule
    Total           & 4036          & 818            & 4854           \\ \bottomrule
  \end{tabular}
  \caption{Size statistics of the feature implementations.}
  \label{tbl:3mt:sizefeatures}
\end{table*}

The size in LoC of the implementation of semantic evaluation and typing
functions and the reusable feature theorem for each language feature is given in
Table \ref{tbl:3mt:sizefeatures}.

Three kinds of feature interactions appear in the case study.

\begin{itemize}
\item
  The PHOAS representation of binders requires an auxiliary equivalence
  relation, the details of which are covered in the MTC paper~\cite{mtc}. The
  soundness proofs of language theorems for languages which include binders
  proceed by induction over this equivalence relation instead of
  expressions. The reusable feature theorems of other features need to be lifted
  to this equivalence relation. In our case study only the |Lambda| feature
  includes binders. The equivalence relations and liftings of the other features
  are contained in the modules |ArithEqv|, |BoolEqv|, |ErrorEqv| and |RefEqv|
  which are also listed in Table \ref{tbl:3mt:sizefeatures}.

\item
  The effect theorems that feature an environment typing $\Sigma$, such as those
  for state or reader, need a weakening sub-lemma which states that each
  well-formed value under $\Sigma$ is also well-formed under a conservative
  extension:
  \[ \Sigma \vdash v ~:~ t  \\ \rightarrow \\
     \Sigma' \supseteq \Sigma \\ \rightarrow \\
     \Sigma' \vdash v ~:~ t
  \]

\item
  Inversion lemmas for the well-formed value relation, such as in the proof of
  \ref{thm:FSound} for the boolean feature in Section \ref{sec:Thm+Reuse}, are
  proven by induction over the relation. Inversion lemmas are needed for natural
  numbers, boolean, store locations and closures. Except for closures, these
  inversion lemmas are dispatched by tactics hooked into the type class
  inference algorithm. For the closure inversion, manually written proof
  algebras are used.

% \item
%   The sublemmas of reusable feature theorems for properties such as
%   textsc{WFM-If-Vc} are proven by induction over the extensible typing
%   relation. When effectful features introduce new judgements to the
%   relation, these new judgements must have proof algebra instances for the
%   sublemmas.
\end{itemize}

The proofs of the second and third kind of feature interactions are
contained in the modules |Lambda_Arith|, |Lambda_Bool| and |Lambda_Ref|.

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

\begin{table*}[t]
  \centering
  \begin{tabular}{lrrr}
                                                                         \toprule
    \textbf{Module} & \textbf{Spec} & \textbf{Proof} & \textbf{Total} \\ \midrule
    |ESoundP|       &   59          & 20             & 79             \\
    |ESoundE|       &   76          & 61             & 137            \\
    |ESoundRF|      &   95          & 50             & 145            \\
    |ESoundS|       &   87          & 70             & 157            \\
    |ESoundERF|     &  210          & 31             & 241            \\
    |ESoundRFS|     &  179          & 104            & 283            \\
    |ESoundES|      &  134          & 164            & 298            \\
    |ESoundERFS|    &  199          & 233            & 432            \\ \midrule
    Total           & 1039          & 733            & 1772           \\ \bottomrule
  \end{tabular}
  \caption{Size statistics of the effect theorems.}
  \label{tbl:3mt:sizeeffecttheorem}
\end{table*}

Table \ref{tbl:3mt:sizeeffecttheorem} lists the sizes of the effect theorems for
each set of effects used in the case study. The letters in the module name
encode the effect set: |P = Pure| (no effects), |E = Exceptions|, |R = Reader|,
|F = Fail| and |S = State|.

\begin{table*}[t]
  \centering
  \begin{tabular}{lrrrclrrr}
                                                                                                                                                \toprule
    \textbf{Module} & \textbf{Spec} & \textbf{Proof} & \textbf{Total} &  & \textbf{Module} & \textbf{Spec} & \textbf{Proof} & \textbf{Total} \\ \midrule
    |A|             & 25            & 4              & 29             &  & |BL|            & 58            & 9              &  67            \\
    |B|             & 26            & 10             & 36             &  & |BARE|          & 58            & 19             &  77            \\
    |AB|            & 27            & 12             & 39             &  & |BAL|           & 64            & 9              &  73            \\
    |R|             & 35            & 9              & 44             &  & |LR|            & 75            & 18             &  93            \\
    |AR|            & 37            & 12             & 49             &  & |ARL|           & 80            & 18             &  98            \\
    |BR|            & 37            & 12             & 49             &  & |BRL|           & 81            & 18             &  99            \\
    |AE|            & 37            & 22             & 59             &  & |ALE|           & 85            & 18             &  103           \\
    |BE|            & 37            & 22             & 59             &  & |BARL|          & 86            & 16             &  102           \\
    |BAR|           & 38            & 14             & 52             &  & |BLE|           & 87            & 18             &  105           \\
    |ABE|           & 38            & 25             & 63             &  & |BALE|          & 93            & 18             &  111           \\
    |RE|            & 53            & 18             & 71             &  & |LRE|           & 106           & 9              &  116           \\
    |ARE|           & 56            & 17             & 73             &  & |ARLE|          & 113           & 9              &  122           \\
    |BRE|           & 57            & 17             & 74             &  & |BRLE|          & 115           & 9              &  124           \\
    |AL|            & 58            & 9              & 67             &  & |BARLE|         & 121           & 9              &  130           \\ \midrule
    Total           & 1783          & 400            & 2184           &  &                 &               &                &                \\ \bottomrule
  \end{tabular}
  \caption{Size statistics of the language compositions.}
  \label{tbl:3mt:sizelanguages}
\end{table*}

Each language needs on average 90 LoC to assemble its semantic functions and
soundness proofs from those of its features and the effect theorem for its set
of effects. Table \ref{tbl:3mt:sizelanguages} contains a detailed overview. The
letters encode the set of used features: |A = Arith, B = Bool, E = Error, L =
Lambda| and |R = References|.


%%% Local Variables:
%%% mode: latex
%%% TeX-master: "../../mod"
%%% End:
