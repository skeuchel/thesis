%include lhs2TeX.fmt
%include forall.fmt
%include polycode.fmt
%include Formatting.fmt

%if False
(defun pct (part total) (/ (fround (/ (* 1000.0 part) total)) 10))
(defun fc-eval-and-replace ()
  "Replace the preceding sexp with its value."
  (interactive)
  (backward-kill-sexp)
  (prin1 (eval (read (current-kill 0)))
         (current-buffer)))
(global-set-key (kbd "C-c e") 'fc-eval-and-replace)
%endif

\newcommand{\mycolorbox}[2]{{\setlength{\fboxsep}{0pt}\colorbox{#1}{#2}}}

\definecolor{light-red}{HTML}{FFDDDD}
\definecolor{light-green}{HTML}{DDFFDD}
\definecolor{light-blue}{HTML}{DDDDFF}
\definecolor{light-violet}{HTML}{FFDDFF}

%% Needle column
\newcolumntype{n}{>{\columncolor{dark-gray}}r}
%% Boilerplate column
\newcolumntype{b}{>{\columncolor{light-gray}}r}
%% Essential column
\newcolumntype{e}{>{\columncolor{light-gray}}r}
%% Manual column
\newcolumntype{m}{>{\columncolor{light-gray}}r}
%% Group separator
\newcolumntype{s}{c}

\newcommand{\Ndl}{\textsc{Ndl}}

%\section{Case Studies}\label{sec:casestudy}

This chapter evaluates the benefits of the \Knot approach for type-safety
mechanizations with two complimentary evaluations. The first considers different
mechanizations for the same language (the \POPLmark challenge) authored by
different people with different degrees of automation or tool support. The
second compares \Knot against manual mechanizations (written by the same author
in a consistent and highly automated style) across different languages.

%% First, we compare fully manual versus \Knot-based mechanizations of type-safety
%% proofs for 10 lambda-calculi in Section \ref{sec:casestudymechanizations}.
%% Second, Section \ref{sec:casestudypoplmark} compares \Knot's solution of the
%% \POPLmark challenge against various existing ones.

%% This sections demonstrates the benefits of the \Knot approach with two case
%% studies. First, we compare fully manual versus \Knot-based mechanizations of
%% type-safety proofs for 10 languages. Second, we compare \Knot's solution of the
%% \POPLmark challenge against various existing ones.




\section{Comparison of Approaches}\label{sec:casestudypoplmark}

\begin{figure*}[t]\centering
  \begin{tikzpicture}
    \begin{axis}[
      width=\linewidth, height=5.8cm,
      symbolic x coords={ %% Leroy
        Chargueraud,Vouillon,Manual,GMeta dB,
        GMeta LN,LNGen,Twelf,AutoSubst,Knot*,Knot
      },
      nodes near coords,
      nodes near coords align={vertical},
      xtick=data,
      x tick label style={rotate=25,anchor=east},
      ybar,
      bar width=0.43cm,
      ylabel={Lines of code},
      ylabel near ticks,
      enlarge y limits={abs=0.4cm},
    ]
    %% (Leroy LN,655)
    %% (Leroy LN,1199)
      \addplot coordinates {
        (Chargueraud,523) (Vouillon,500) (Manual,509) (GMeta dB,297)
        (GMeta LN,376) (LNGen,330) (Twelf,174) (AutoSubst,210) (Knot*,168)
        (Knot,117)
      };
      \addplot coordinates {
        (Chargueraud,538) (Vouillon,614) (Manual,259) (GMeta dB,669)
        (GMeta LN,513) (LNGen,432) (Twelf,402) (AutoSubst,225) (Knot*,121)
        (Knot,75)
      };
      \addplot coordinates {
      };
      \legend{Spec,Proof,Time}
    \end{axis}
%if False
    \begin{axis}[
      width=\linewidth, height=5cm,
      symbolic x coords={ %% Leroy
        Chargueraud,Vouillon,Manual,GMeta dB,
        GMeta LN,LNGen,Twelf,AutoSubst,Knot
      },
      hide x axis,
      nodes near coords rotate={45},
      nodes near coords align={vertical},
      xtick=data,
      axis y line*=right,
      %% enlarge y limits={abs=0.4cm}, %% Seems to be problematic.
      ymin=0,
      ymax=108,
      ybar,
      bar width=0.43cm,
      ylabel={Checking time},
      ylabel near ticks,
    ]
    %% (Leroy LN,655)
    %% (Leroy LN,1199)
      \addplot coordinates {
      };
      \addplot coordinates {
      };
      \addplot coordinates {
        (Chargueraud,8.6) (Vouillon,5.3) (Manual,6.4) (GMeta dB,10.4)
        (GMeta LN,37) (LNGen,97) (Twelf,0.2) (AutoSubst,13.9) (Knot,8.4)
        (Knot,0)
      };
    \end{axis}
%endif
  \end{tikzpicture}
  \caption{Sizes (in LoC) of \POPLmark solutions}
  \label{fig:casestudypoplmark}
\end{figure*}

Because it is the most widely implemented benchmark for mechanizing metatheory,
we use parts 1A + 2A of the \POPLmark challenge to compare our work with that of
others. These parts prove type-safety for \SystemFsub with algorithmic
subtyping. As they involve only single-variable bindings, they are manageable
for most existing approaches. Figure \ref{fig:casestudypoplmark} compares 10
different solutions:

\begin{enumerate}
\item[1.] Chargu\'eraud's \cite{poplmark:chargueraud} developments use the
  locally-nameless representation and come with automation via proof tactics for
  this representation.
\item[2.] Vouillon \cite{poplmark:vouillon} presents a self-contained de Bruijn
  solution. The solution only moderately uses automation and instead performs
  proof steps explicitly for didactic purposes.
\item[3.] Our own more compact manual mechanization (see
  Section~\ref{sec:casestudymechanizations}) based on de Bruijn terms with more
  automation than Vouillon's solution.
\item[4--5.] Two solution based on the \textsc{GMeta}~\cite{gmeta}
  datatype-generic library for de Bruijn and locally-nameless representations.
\item[6.] A mechanization in \Coq using a locally-nameless representation
  and boilerplate produced by the \textsc{LNGen} \cite{lngen} code generator
  from an \Ott specification.
\item[7.] A solution in the \textsc{Twelf} logical framework \cite{poplmark:cmu}.
\item[8.] A solution using the \textsc{Autosubst} \cite{autosubst} \Coq library for
  de Bruijn terms.
\item[9.] A \Knot-based solution without generation of semantics-related boilerplate
  \cite{knotneedle} (\Knot{}*).
\item[10.] Our \Knot-based solution (\Knot) for both syntax and semantics.
\end{enumerate}

The figure shows the code size separated into \emph{proof} scripts and other
\emph{spec}ification lines as generated by \textit{coqwc}, except for the
\textsc{Twelf} solution were we made the distinction manually. We excluded both
library code and generated code. The \AutoSubst and \Knot formalizations are
significantly smaller than the others. \Knot's biggest savings compared to
\AutoSubst come from the generic handling of well-scopedness predicates and
semantic relations which are not supported by \AutoSubst. In comparison to the
\Knot-based solution \cite{knotneedle} without support for relations, we save
relatively more LoC in \emph{proofs} than in \emph{specifications}. In summary,
the \Knot solution is the smallest solutions we are aware of.


%-------------------------------------------------------------------------------
\section{Manual vs. \Knot Mechanizations}\label{sec:casestudymechanizations}

%if False
(defun pct (part total) (/ (fround (/ (* 1000.0 part) total)) 10))
(defun fc-eval-and-replace ()
  "Replace the preceding sexp with its value."
  (interactive)
  (backward-kill-sexp)
  (prin1 (eval (read (current-kill 0)))
         (current-buffer)))
(global-set-key (kbd "C-c e") 'fc-eval-and-replace)
%endif
\afterpage{
  \clearpage
  \begin{landscape}
    \begin{table*}[t]
      \centering
      \setlength\tabcolsep{5pt}

      \begin{tabular}{@@{}rlebnsebbnsmnn||rr@@{}}
        \toprule
            &
            & \multicolumn{3}{c}{\textbf{Specification}} & \phantom{abc}
            & \multicolumn{4}{c}{\textbf{Metatheory}}    & \phantom{abc}
            & \multicolumn{5}{c}{\textbf{Total}} \\
        \cmidrule{3-5}      \cmidrule{7-10} \cmidrule{12-16}
            &              & Ess. & Bpl. & \Ndl &  & Ess. & Syn. & Sem. & \Ndl &  & Man. & \multicolumn{2}{n}{\Ndl} & \multicolumn{2}{r}{$\Delta\Needle$} \\
        \midrule
         1) & \stlc        & 41   & 39   & 36   &  & 23   & 22   & 23   & 19   &  & 148  & 55  & (37.2\%)           & 28  & (18.9\%) \\
         2) & \stlcprod    & 82   & 67   & 75   &  & 32   & 61   & 72   & 75   &  & 314  & 150 & (47.8\%)           & 48  & (15.3\%) \\
         3) & \F           & 51   & 102  & 46   &  & 185  & 79   & 30   & 30   &  & 447  & 76  & (17.0\%)           & 42  & (9.4\%)  \\
         4) & \fprod       & 90   & 150  & 85   &  & 230  & 126  & 79   & 87   &  & 675  & 172 & (25.5\%)           & 97  & (14.4\%) \\
         5) & \fexists     & 71   & 114  & 66   &  & 266  & 86   & 44   & 43   &  & 581  & 109 & (18.8\%)           & 79  & (13.6\%) \\
         6) & \fexistsprod & 123  & 164  & 103  &  & 365  & 172  & 98   & 101  &  & 922  & 204 & (22.1\%)           & 106 & (11.5\%) \\
         7) & \fseqlet     & 99   & 165  & 88   &  & 249  & 162  & 49   & 70   &  & 724  & 158 & (21.8\%)           & 89  & (12.3\%) \\
         8) & \fsub        & 66   & 117  & 57   &  & 264  & 150  & 163  & 138  &  & 760  & 195 & (25.7\%)           & 94  & (12.4\%) \\
         9) & \fsubprod    & 110  & 155  & 92   &  & 311  & 212  & 256  & 235  &  & 1044 & 327 & (31.3\%)           & 149 & (14.3\%) \\
        10) & \lomega      & 97   & 88   & 75   &  & 202  & 141  & 251  & 268  &  & 779  & 343 & (44.0\%)           & 161 & (15.4\%) \\
        11) & \fomega      & 120  & 98   & 92   &  & 204  & 141  & 311  & 330  &  & 874  & 422 & (48.3\%)           & 160 & (15.3\%) \\
        \bottomrule
      \end{tabular}
      \caption{Size statistics of the meta-theory mechanizations.}
      \label{tbl:casestudy}
    \end{table*}
  \end{landscape}
  \clearpage
}

The previous comparison only considers the type-safety proof for a single
language, and thus paints a rather one-sided picture of the savings to be had.
For this reason, our second comparison considers the savings across 11
languages. As their mechanizations are not readily available across different
tools and systems, we here pit \Knot \& \Needle only against our own manual
mechanizations. To yield representative results, all our manual mechanizations
have been written by the same author in a consistent and highly automated
style.\footnote{ E.g., compare our manual solution against Vouillon's in
  Figure~\ref{fig:casestudypoplmark}: it is smaller due to more automation and
  simpler definitions that are more amenable to proof search.}

The 11 textbook calculi we consider are: 1) the simply typed lambda calculus
$\stlc$, 2) \stlc extended with products, 3) \SystemF, 4) F with products, 5) F
with existentials, 6) F with existentials and products, 7) F with sequential
lets, 8) $\text{F}_{<:}$ as in the \POPLmark challenge 1A + 2A of
Section~\ref{ssec:casestudypoplmark}, 9) $\text{F}_{<:}$ with products, 10)
$\stlc$ with type-operators, and 11) F with type-operators.

For each language, we have two \Coq formalizations: one developed without tool
support and one that uses \Needle's generated code. Table \ref{tbl:casestudy}
gives a detailed overview of the code sizes (LoC) of different parts of the
formalizations and the total and relative amount of boilerplate. It also shows
the $\Delta\Needle$ savings due to \Needle's new support for relations.


The \emph{Specification} column comprises the language specifications.  For the
manual approach, it is split into an \emph{essential} part
\mycolorbox{light-gray}{(Ess.)} and a \emph{boilerplate} part
\mycolorbox{light-gray}{(Bpl.)}.  The former comprises the abstract syntax
declarations (including binding specifications), the evaluation rules, typing
contexts and typing rules; this part is also expressed (slightly more concisely) in the
\Knot specification \mycolorbox{dark-gray}{(\Ndl)}.  The boilerplate part
consists of lookups for the variable rules and shifting and substitution
functions, that are necessary to define $\beta$-reduction on terms and, where
applicable, on types; this boilerplate is generated by \Needle and thus
not counted towards the size of the \Knot-based mechanization.

The \emph{Metatheory} column shows the effort to establish type-safety of the
languages. The essential lemmas are canonical forms, typing inversion, progress
and preservation and where applicable this also includes: pattern-matching
definedness, reflexivity and transitivity of subtyping and the Church-Rosser
property for type reductions.

There are two classes of binder boilerplate in the metatheory:
\begin{enumerate}
\item Syntax-related boilerplate \mycolorbox{light-gray}{(Syn.)} that consists
  of interaction lemmas, weakening and substitution lemmas for well-scopedness
  predicates. The code size for these lemmas depends mainly on the number of
  namespaces, the number of syntactic sorts and the dependency structure between
  them, which is roughly the same for these languages. \Needle derives this
  boilerplate completely automatically.

\item The semantics-related boilerplate \mycolorbox{light-gray}{(Sem.)} are
  well-scoping, shifting and substitution lemmas for user-defined semantic
  relations. The size of these lemmas depends on the number of namespaces
  and the size of the semantics relations.

  We defined \lomega and \fomega using algorithmic type equality with
  reflexivity only on type-variables, not on types. For the substitution lemmas
  of these calculi, \Needle generates a proof obligation for the admissibility
  of reflexivity of types. Similarly, \fsub and \fsubprod use algorithmic
  subtyping and both, the type-variable reflexivity and type-variable
  transitivity rule, give rise to a proof obligation. Furthermore, neither of
  these two rules meets the restrictions of Section \ref{ssec:relationwf} for
  variable rules, and thus deriving a variable rule yields another proof
  obligation.
\end{enumerate}

The final column group contrasts the total sizes of the manual
\mycolorbox{light-gray}{(Man.)} and \Knot based formalizations
\mycolorbox{dark-gray}{(\Ndl)}. The last column $\Delta\Needle$ shows the
difference between \Knot-based solutions with and without generation of
semantics-related boilerplate.

\paragraph{Summary}

Table \ref{tbl:casestudy} clearly shows that \Needle provides substantial
savings in each of the language formalizations. On average, {\Needle}-based
solutions are 71\% smaller than the manual solutions
$(100\%-\mycolorbox{dark-gray}{\Ndl} / \mycolorbox{light-gray}{Man.})$, the
generation of semantics-related boilerplate saves $\sim$14\% of the manual
approach $(\Delta\Needle / \mycolorbox{light-gray}{Man.})$ and $\sim$33\% of the
\Needle-assisted approach $(\Delta\Needle / \mycolorbox{dark-gray}{\Ndl})$.


%% It is noteworthy that, unlike other solutions of the PoplMark
%% challenge using de Bruijn indices, we have no lemmas that depend on
%% the relative order of two indices and we never use commutation of
%% addition. For the narrowing of \fsub and \fsubprod one lemma
%% regarding the lookup of bounds uses a disequality between two
%% indices.

%% However the proof of weakening for \LF typing rules makes use of
%% all commutation lemmas except for the ones featuring two
%% substitutions. Moreover, we expect that the lemmas of typing
%% preservation under substitutions will use all generated lemmas.

%% Secondly, during the formalization the amount of arithmetic
%% reasoning we had to perform was minimal.




%if False
%-----------------------------------------------------------------------------
\subsection{Expressivity Demonstration}

While Section \ref{ssec:casestudymechanizations} demonstrates the effectiveness
of \Knot on a number of well-known calculi, these do not put the expressivity
of \Knot to the test. Hence, we also provide a small suite of language
specifications that involve more challenging binder-related features.
For each of the languages in the suite, we give a full specification of the type
system and proofs of crucial preservation lemmas of typing relations
under substitution.\footnote{A full mechanization of type safety is out of scope of
this work.}

The suite comprises the examples of Section~\ref{s:spec:ex}, calculi with
recursive let and telescopic lambdas. These example illustrate multi-binders
and advanced scoping. The dependent type theories of \LF and \textsc{CoC},
whose specifications in the suite we have derived from Pierce~\cite{atapl}, are
particularly challenging: they use dependent contexts with mutually-recursive
sorts with variables.

The number of lemmas generated lies in $O(m^3n)$ where |m| is the
number of namespaces and |n| is the number of syntactic sorts.  For
languages with two namespaces like \LF~this amounts to about 1600
lines of boilerplate code. The worst case is the commutation of a
substitution in namespaces $\alpha$ with one in namespace $\beta$
while going under a $\gamma$ binder (with
$\gamma \in nsOf \alpha \cup nsOf \beta$) while traversing a term of
sort |S|. Therefore, the number of boilerplate quickly grows
unmanageable and tool support becomes a necessity.

In general we cannot derive preservation lemmas for all inductive
relations. In particular the algorithmic term, type and kind equality
relations represent normal forms. In these cases \Knot creates
proof obligations.
%endif




%%% Local Variables:
%%% mode: latex
%%% TeX-master: "../Main"
%%% End:
