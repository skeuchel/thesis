%include lhs2TeX.fmt
%include forall.fmt
%include polycode.fmt
%include Formatting.fmt
%include macros.fmt
%include exists.fmt

\section{Case Study}\label{sec:modpred:casestudy}

As a demonstration of the advantages of our approach over MTC's Church
encoding-based approach, we have ported the case study from~\cite{mtc}. The
study consists of soundness and continuity\footnote{of step-bounded evaluation
  functions} proofs in addition to typing and evaluation functions of five
reusable language features: 1) arithmetic expressions, 2) boolean expressions,
3) natural number pattern matching, 4) lambda abstraction and 5) a general
recursion fixed-point operator.

Figure~\ref{fig:mini-ml-syntax} presents the syntax of the expressions, values,
and types provided by the features; each line is annotated with the feature that
provides that set of definitions.

\begin{figure}[t]
  \centering
  \fbox{
    \begin{minipage}{0.98\columnwidth}
      \begin{tabular*}{\columnwidth}{r@@{\;}c@@{\;}l@@{\hspace{30mm}}r}
        \texttt{e} & ::=    & \texttt{$\mathbb{N}$ $\mid$ e + e}                                                                     & \textit{Arith}     \\
                   & $\mid$ & \texttt{$\mathbb{B}$ $\mid$ \textbf{if} e \textbf{then} e \textbf{else} e}                             & \textit{Bool}      \\
                   & $\mid$ & \texttt{\textbf{case} e \textbf{of} \{ z $\Rightarrow$ e $\mathbf{;}$ \textbf{S} n $\Rightarrow$ e \}} & \textit{NatCase}   \\
                   & $\mid$ & \texttt{\textbf{lam} x : T.e $\mid$ e e $\mid$ x}                                                      & \textit{Lambda}    \\
                   & $\mid$ & \texttt{\textbf{fix} x : T.e}                                                                          & \textit{Recursion} \\
      \end{tabular*}
      \begin{tabular*}{\columnwidth}{r@@{\;}c@@{\;}l@@{\hspace{5mm}}rcr@@{\;}c@@{\;}l@@{\hspace{5mm}}r}
        \texttt{V} & ::=    & \texttt{$\mathbb{N}$}                               & \textit{Arith}  &  & \texttt{T} & ::=    & \texttt{\textbf{nat}}      & \textit{Arith}  \\ 
                   & $\mid$ & \texttt{$\mathbb{B}$}                               & \textit{Bool}   &  &            & $\mid$ & \texttt{bool}              & \textit{Bool}   \\ 
                   & $\mid$ & \texttt{\textbf{closure} e $\mathtt{\overline{V}}$} & \textit{Lambda} &  &            & $\mid$ & \texttt{T $\rightarrow$ T} & \textit{Lambda} \\ 
      \end{tabular*}
    \end{minipage}
  }
  \caption{mini-ML expressions, values, and types}
  \label{fig:mini-ml-syntax}
\end{figure}

In this section we discuss the benefits and trade-offs we have experienced while
porting the case study to our approach.


\paragraph{Impredicative sets}\label{ssec:impredicativeset}
The higher-rank type in the definition of |FixMTC|

< FixMTC (f :: Set -> Set) = forall ((a :: Set)). Algebra f a -> a

causes |FixMTC f| to be in a higher universe level than the domain of |f|. Hence
to use |FixMTC f| as a fixed-point of |f| we need an impredicative sort. MTC
uses Coq's impredicative-set option for this which is known to be incompatible
with axioms of classical logic.

When constructing the fixed-point of a container we do not need to raise the
universe level and thus avoid impredicative sets.


\paragraph{Adequacy}
Adequacy of definitions is an important problem in mechanizations. One concern
is the adequate encoding of fixed-points. MTC relies on a side-condition to show
that for a given functor |f| the folding |(inMTC :: f (FixMTC f) -> FixMTC f)|
and unfolding |(outMTC :: FixMTC f -> f (FixMTC f))| are inverse operations,
namely, that all appearing |(FixMTC f)| values need to have the universal
property of folds. This side-condition raises the question if |(FixMTC f)| is an
adequate fixed-point of |f|. The pairing of terms together with their proofs of
the universal property do not form a proper fixed-point either, because of the
possibility of different proof components for the same underlying terms.

Our approach addresses this adequacy issue: the |SPF| type class from Figure
\ref{fig:strictlypositivefunctor} requires that |inFix| and |outFix| are inverse
operations without any side conditions on the values and containers give rise to
proper |SPF| instances.


\paragraph{Equality of terms}
Packaging universal properties with terms obfuscates equality of terms
when using Church encodings. The proof component may differ for the
same underlying term.

This shows up for example in type-soundness proofs in MTC. An extensible logical
relation |WTValue (v ,t)| is used to represent well-typing of values. The
judgement ranges over values and types. The universal properties are needed for
inversion lemmas and thus the judgement needs to range over the variants that
are packaged with the universal properties.

However, knowing that |WTValue (v, t)| and |proj1 t = proj1 t'| does not
directly imply |WTValue (v ,t')|, because of the possibly distinct proof
component. To solve this situation auxiliary lemmas are needed that establish
the implication. Other logical relations need similar lemmas. Every feature that
introduces new rules to the judgments must also provide proof algebras for these
lemmas.

In the case study two logical relations need this kind of auxiliary lemmas: the
relation for well-typing and a sub-value relation for continuity. Both of these
relations are indexed by two modular types and hence need two lemmas each. The
proofs of these four lemmas, the declaration of abstract proof algebras and the
use of the lemmas amounts to roughly 30 LoC per feature.

In our approach we never package proofs together with terms and hence this
problem never appears. We thereby gain better readability of proofs and a small
reduction in code size.


\paragraph{Code Size}

\begin{table*}[t]
  \centering
  \begin{tabular}{lrrrl}
    \toprule
      \textbf{Module} & \textbf{Spec} & \textbf{Proof} & \textbf{Total} & \textbf{Description}               \\ \midrule
      |FJ_tactics|    & 193           & 99             & 292            & Tactic library.                    \\
      |Functors|      & 675           & 83             & 758            & Functors, algebras and coproducts. \\
      |Containers|    & 758           & 105            & 863            & Universe of containers).           \\
      |Polynomial|    & 249           & 198            & 447            & Universe of polynomial functors.   \\
      |Equality|      & 63            & 53             & 116            & Equality for polynomial functors.  \\ \midrule
      Total           & 1938          & 548            & 2476           &                                    \\
    \bottomrule
  \end{tabular}
  \caption{Size statistic for the GDTC modular reasoning framework}
  \label{tbl:gdtc:sizeframework}
\end{table*}

By moving to a datatype-generic approach the underlying framework for modular
datatypes and modular relations and modular reasoning grew from about 1,200 LoC
to about 2,500 LoC. Table \ref{tbl:gdtc:sizeframework} shows a detailed
breakdown of the different modules which include both the universe of containers
and polynomial functors and the generic implementations of fold, induction and
equality.

\begin{table*}[t]
  \centering
  \begin{tabular}{lcrrrcrrr}
    \toprule
    &
    & \multicolumn{3}{c}{\textbf{GDTC}} & \phantom{abc}
    & \multicolumn{3}{c}{\textbf{MTC}}  \\
                    \cmidrule{3-5}            \cmidrule{7-9}
      \textbf{Module} & & \textbf{Spec} & \textbf{Proof} & \textbf{Total} &  & \textbf{Spec} & \textbf{Proof} & \textbf{Total} \\ \midrule
      |Names|         & & 480           & 145            & 625            &  & 479           & 92             & 571            \\
      |PNames|        & & 399           & 180            & 579            &  & 507           & 119            & 626            \\ \midrule
      Total           & & 879           & 325            & 1204           &  & 986           & 211            & 1197           \\
    \bottomrule
  \end{tabular}
  \caption{Size statistics of the type-safety infrastructure.}
  \label{tbl:gdtc:sizetypesafety}
\end{table*}

The feature-independent infrastructure for type-safety is defined in modules
|Names| and |PNames|. These contain declarations of modular functions for typing
and evaluation, and modular proofs of continuity and type safety of evaluation.
Table \ref{tbl:gdtc:sizetypesafety} contains a breakdown of these modules and a
comparison with the original versions from the MTC case study. The GDTC versions
avoid some duplicate declarations for decorated and undecorated fixed-points and
save code by eliminating the need to reason about universal properties. However
the GDTC approach also requires instance declarations for containers, in
particular indexed container instances for predicates on environments, which are
new obligations and nullify any savings. Both the MTC and the GDTC version are
about 1,200 LoC.

\begin{table*}[t]
  \centering
  \begin{tabular}{lrrrcrrr}
    \toprule
    & \multicolumn{3}{c}{\textbf{GDTC}} & \phantom{abc}
    & \multicolumn{3}{c}{\textbf{MTC}}  \\
                    \cmidrule{2-4}            \cmidrule{6-8}
      \textbf{Module} & \textbf{Spec} & \textbf{Proof} & \textbf{Total} &  & \textbf{Spec} & \textbf{Proof} & \textbf{Total} \\ \midrule
      |Arith|         & 415           & 150            & 565            &  & 522           & 492            & 1014           \\
      |Bool|          & 441           & 151            & 592            &  & 560           & 169            & 729            \\
      |Lambda|        & 779           & 171            & 950            &  & 1223          & 159            & 1382           \\
      |Mu|            & 401           & 31             & 432            &  & 481           & 26             & 507            \\
      |NatCase|       & 212           & 25             & 237            &  & 282           & 12             & 294            \\
      |ArithLambda|   & 59            & 9              & 68             &  & 103           & 7              & 110            \\
      |BoolLambda|    & 60            & 11             & 71             &  & 112           & 7              & 119            \\ \midrule
      Total           & 2367          & 548            & 2915           &  & 3283          & 872            & 4155           \\
    \bottomrule
  \end{tabular}
  \caption{Size statistics of the feature mechanizations.}
  \label{tbl:gdtc:sizefeatures}
\end{table*}

The size of the implementation of the five modular feature components and
feature interactions is roughly 830 LoC per feature in the original MTC case
study. By switching from Church encodings to a datatype-generic approach we
stripped away on average about 230 LoC of additional proof obligations needed
for reasoning with Church encodings per feature. However, instantiating the MTC
interface amounts to roughly 40 LoC per feature while our approach requires
about 70 LoC per feature for the container and polynomial instances.

By using the generic equality and generic proofs about its properties we can
remove the feature-specific implementations from the case study. This is about
40 LoC per feature. In total we have reduced the average size of a feature
implementation by about 240 LoC to 590 LoC. Table \ref{tbl:gdtc:sizefeatures}
shows a detailed breakdown of the different features implemented as part of the
case study.

\begin{table*}[t]
  \centering
  \begin{tabular}{lcrrrcrrr}
    \toprule
    &
    & \multicolumn{3}{c}{\textbf{GDTC}} & \phantom{abc}
    & \multicolumn{3}{c}{\textbf{MTC}}  \\
                    \cmidrule{3-5}            \cmidrule{7-9}
    \textbf{Composition} &  & \textbf{Spec} & \textbf{Proof} & \textbf{Total} &  & \textbf{Spec} & \textbf{Proof} & \textbf{Total} \\ \midrule
    A                    &  & 52            & 3              & 55             &  & 47            & 3              & 50             \\
    AL                   &  & 76            & 5              & 81             &  & 49            & 9              & 58             \\
    BL                   &  & 76            & 5              & 81             &  & 57            & 9              & 66             \\
    AB                   &  & 79            & 3              & 82             &  & 73            & 6              & 79             \\
    ABL                  &  & 103           & 5              & 108            &  & 129           & 9              & 138            \\
    MiniML               &  & 91            & 5              & 96             &  & 67            & 10             & 77             \\ \midrule
    Total                &  & 477           & 26             & 503            &  & 422           & 46             & 468            \\
    \bottomrule
  \end{tabular}
  \caption{Size statistics of the language compositions}
  \label{tbl:gdtc:sizecompositions}
\end{table*}

The last piece of the case study consists of the language compositions: a subset
of features is chosen to form a language and the type-safety theorem is derived
for that language from the modular proof algebras. The breakdown for six
different compositions is shown in Table~\ref{tbl:gdtc:sizecompositions}. The
GDTC compositions derive local container instances for composed functors to
avoid costly and repetitive type class resolutions. This puts the GDTC variants
slightly above the MTC version in terms of code size.

\paragraph{Summary}

The case study shows that our approach can effectively replace the MTC approach
and offers simplifications for programming and reasoning about modular datatypes
and relations. Another benefit is the applicability in proof-assistants that do
not offer impredicative sorts to implement the MTC approach.

In terms of development effort the savings achieved by switching to the
container based approach and removing boilerplate functions like equality
testing are in the order of a 25\% code size reduction per feature. Since the
user does not need to concern herself with the preservation of the universal
properties of folds in her definitions, our approach offers a less complex
framework that can result in less development effort not only in terms of code
size, but also in terms of coding time and mental effort.

%if False
\paragraph{Refinement types}

The paper \cite{3mt} presents follow-up work
that uses the original MTC framework. It tackles
the problem of modular type-safety proofs for languages
with side-effecting features.

The following rule is used in \cite{3mt} for an extensible
relation of well-typed monadic computations.

< WFVM_Return ::
<     (v :: FixMTC vf) (t :: FixMTC tf) (mt : MT (FixMTC T)),
<     WFValue v t ->
<     {mt' : MT {t' : FixMTC T | proj1_sig t = proj1_sig t'} &
<       fmap (@proj1_sig _ _) mt' = mt} -> ...

%endif

%if False
\paragraph{Equality testing}

The implementation of equality testing in MTC proceeds in the same way
as other semantic functions: as folds of an algebra.

The carrier type of the algebra is |Fix d -> Bool| where |d| is the
abstract super-functor for types. The properties of the equality
type class from Figure \ref{fig:equalityclass} are established by
proof-algebras. However, the implementation is not entirely modular.

The algebra for the |FunType| functor relies on an additional function

> eq_TArrow :: SPF d =>
>   (Fix d -> Bool) -> (Fix d -> Bool) ->
>   Fix d -> Bool

that given the equality functions for two terms, constructs and
equality function for |TArrow|, i.e. if the given value was
constructed using |TArrow| it performs checking equality recursively
using the two given functions and otherwise it returns |False|. This
function also needs to be implemented by means of an algebra that
needs to be defined for |FunType| and any other functor for types and
is hence an instance of feature interaction in MTC. Using a generic
implementation of equality we can thus not only avoid boilerplate
code, but also cut down on feature interactions.
%endif


%%% Local Variables:
%%% mode: latex
%%% TeX-master: "../../mod"
%%% End:
