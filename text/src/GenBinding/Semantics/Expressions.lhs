%include lhs2TeX.fmt
%include polycode.fmt
%include Formatting.fmt
%include forall.fmt

%format ti = t "_{\igmv{i}}"
%format ki = k "_{\igmv{i}}"
%format ci = c "_{\igmv{i}}"
%format αi = α "_{\igmv{i}}"
%format mi = m "_{\igmv{i}}"
%format si = s "_{\igmv{i}}"
%format bsi = bs "_{\igmv{i}}"
%format nti = nt "_{\igmv{i}}"
%format t'i = t' "_{\igmv{i}}"
%format c'i = c' "_{\igmv{i}}"

%-------------------------------------------------------------------------------
\section{Expression Semantics}\label{sec:exprsemantics}

The semantics of expressions is an evaluation: given an assignment $\vartheta$
to all appearing meta-variables, we can evaluate an expression |sym| to a de
Bruijn term $u$. Expressions can contain weakenings and substitutions and we
have to give a proper interpretation for them in terms of the de Bruijn
representation. These are boilerplate definitions that we define generically in
Sections \ref{ssec:sem:shifting} and \ref{ssec:sem:substitution} before coming
back to evaluation in Section \ref{ssec:sem:evaluation}.


%-------------------------------------------------------------------------------
\subsection{Shifting}\label{ssec:sem:shifting}

% We generically define common infrastructure operations generically over all
% terms of a specifications. This includes shifting and substitution in sort and
% environment terms.

\begin{figure}[t]
  \centering
  \fbox{
    \begin{minipage}{0.98\columnwidth}
      \[\begin{array}{@@{}l@@{\hspace{1mm}}c@@{\hspace{1mm}}lr}
          c   & ::=  & 0 \mid |S|~c ~~   & \text{Cutoffs}
        \end{array}
      \]

      \vspace{-5mm}
      \begin{tabular}{lr}
        \begin{minipage}[t]{0.49\columnwidth}
          \begin{code}
          box (weakenα :: c → h → c)

          weakenα c 0       = c
          weakenα c (Sβ h)  =
            if α = β
              then S (weakenα c h)
              else weakenα c h

          box (shiftN :: c → n → n)

          shiftN 0      n      =  S n
          shiftN (S c)  0      =  0
          shiftN (S c)  (S n)  =  S (shiftN c n)

          box (weaken :: u → h → u)

          weaken u 0       =  u
          weaken u (Sα h)  =
            shiftα' 0 (weaken u h)

          \end{code}
        \end{minipage}
        &
        \begin{minipage}[t]{0.49\columnwidth}
          \begin{code}
          box (shiftα :: c → u → u)

          shiftα c (K n)             =
            if K : α → S
              then K (shiftN c n)
              else K n
          shiftα c (K (overline u))  =
              K (overline (shiftα' (weakenα c (subscript (⟦ bs ⟧) ϑ)) u))
            where
              K (overline x) ((overline ([bs] t : T))) ∈ mathit spec
              ϑ = overline (t ↦ u)

          box (shiftα' :: c → u → u)

          shiftα' c u =
            if α ∈ depsOf u
              then shiftα c u else u

          \end{code}
        \end{minipage}
      \end{tabular}
    \end{minipage}
  }
  \caption{Shifting of terms}
  \label{fig:shift}
\end{figure}

Shifting adapts indices when a variable |x| is inserted into the context.
$$
|Γ,Δ ⊢ e ↝ Γ,(x:τ),Δ ⊢ e|
$$
Indices in |e| for |α|-variables in |Γ| need to be incremented to account for
the new variable while indices for variables in |Δ| remain unchanged. The
|shift| function is defined in Figure \ref{fig:shift} implements this. It is
parameterized over the namespace |α| of variable |x| in which the shift is
performed. It takes a \emph{cut-off} parameter |c| that is the number of
|α|-variable bindings in |Δ|. In case of a variable constructor |K : α → S|, the
index is shifted using the |shiftN| function. For variable constructors of other
namespaces, we keep the index unchanged. In the case of a regular constructor, we
need to calculate the cut-offs for the recursive calls. This is done by
evaluating the binding specification |bs| and weakening the cut-off. Using the
calculated cut-offs, the |shiftα'| function can proceed recursively on the
subterms that depend on the namespace |α|.

Instead of using the traditional arithmetical implementation
$$|if n < c then n else n + 1|$$
we use an equivalent recursive definition of |shiftN| that inserts the successor
constructor \emph{at the right place}. This follows the inductive structure of
|Δ| which facilitates inductive proofs on |Δ|.

\paragraph{Weakening}

Weakening is the transportation of a term |e| from a context |Γ| to a bigger
context |Γ,Δ| where variables are only added at the end.
$$
|Γ ⊢ e ↝ Γ,Δ ⊢ e|
$$

Figure~\ref{fig:shift} shows the implementation of |weakenα| that iterates the
1-place |shiftα'| function. Its second parameter |h| is the domain of |Δ|; the
range of |Δ| is not relevant for weakening.


\subsection{Substitution}\label{ssec:sem:substitution}

\begin{figure}[t]
  \begin{center}
    \fbox{
      \begin{minipage}{0.98\columnwidth}
        \[\begin{array}{@@{}l@@{\hspace{1mm}}c@@{\hspace{1mm}}lr}
            x   & ::=  & 0 \mid |Sα|~x ~~   & \text{Trace}
          \end{array}
        \]
        \vspace{-5mm}
        \framebox{\mbox{$\vdash_\alpha x$}} \\
        \[ \begin{array}{c}
           \inferrule* [right=\textsc{WfTraceZero}]
                       {\,}
                       {\vdash_\alpha 0} \quad
           \inferrule* [right=\textsc{WfTraceSucc}]
                       {\vdash_\alpha n \\
                        |β ∈ depsOf α|}
                       {\vdash_\alpha Sβ~n}
           \end{array}
        \]

        \vspace{-5mm}
        \begin{tabular}{lr}
          \begin{minipage}[t]{0.46\columnwidth}
          \begin{code}
          box (weakenα :: x → h → x)

          weakenα c 0       =  c
          weakenα c (Sβ h)  =
            if β ∈ depsOf α
               then Sβ (weakenα x h)
               else weakenα x h

          box (substαℕ :: v → x → n → u)
          substαℕ v 0       0      =  v
          substαℕ v 0       (S n)  =  K n
            where K : α → T ∈ mathit spec
          substαℕ v (Sα x)  0      =  K 0
            where K : α → T ∈ mathit spec
          substαℕ v (Sα x)  (S n)  =
            weaken (substαN v x n) Iα
          substαℕ v (Sβ x)  n      =
            weaken (substαN v x n) Iβ
          \end{code}
          \end{minipage} \qquad
           &
          \begin{minipage}[t]{0.52\columnwidth}
          \begin{code}
          box (substα :: v → x → u → u)

          substα v x (K n)             =
            if K : α → S
              then substαℕ v x n
              else K n
          substα v x (K (overline u))  =
              K (overline (substα' v (weakenα x (subscript (⟦ bs ⟧) ϑ)) u))
            where
              K (overline x) ((overline ([bs] t : T))) ∈ mathit spec
              ϑ = overline (t ↦ u)

          box (substα' :: v → x → u → u)

          substα' v x u =
            if α ∈ depsOf u
              then substα v x u
              else u
          \end{code}
          \end{minipage}
        \end{tabular}
      \end{minipage}
    }
  \end{center}
\caption{Substitution of terms}
\label{fig:subst}
\end{figure}


Next, we define substitution of a single variable |x| for a term |e| in some
other term |e'| generically. In the literature, two commonly used variants can
be found.

\begin{enumerate}

\item The first variant keeps the invariant that |e| and |e'| are in the same
  context and immediately weakens |e| when passing under a binder while
  traversing |e'| to keep this invariant. It corresponds to the substition lemma
$$
\begin{array}{c}
\inferrule*[]
  {\gray{|Γ,Δ ⊢ e : σ|} \\
   |Γ,x:σ,Δ ⊢ e' : τ|
  }
  {|Γ,Δ ⊢ {x ↦ e}e' : τ|}
\end{array}
$$

\item The second variant keeps the invariant that |e'| is in a weaker context
  than |e|. It defers weakening of |e| until the variable positions are reached
  to keep the invariant and performs shifting if the variable is substituted. It
  corresponds to the substitution lemma
$$
\begin{array}{c}
\inferrule*[]
  {\gray{|Γ ⊢ e : σ|} \\
   |Γ,x:σ,Δ ⊢ e' : τ|
  }
  {|Γ,Δ ⊢ [x ↦ e]e' : τ|}
\end{array}
$$
\end{enumerate}

Both variants were already present in de Bruijn's seminal paper
\cite{namelessdummies}, but the first variant has enjoyed more widespread
use. However, we will use the second variant because it has the following
advantages:

\begin{enumerate}
\item It supports the more general case of languages with a dependent context:
$$
\begin{array}{c}
\inferrule*[]
  {|Γ ⊢ e : σ| \\
   |Γ,x:σ,Δ ⊢ e' : τ|
  }
  {|Γ,[x ↦ e]Δ ⊢ [x ↦ e]e' : [x ↦ e]τ|}
\end{array}
$$

\item The parameter |e| is constant while recursing into |e'| and hence it can
also be moved outside of inductions on the structure of |e|. Proofs become
slightly simpler because we do not need to reason about any changes to |s| when
going under binders.
\end{enumerate}

For the definition of substitution, we again need to use a refinement of natural
numbers, a different one from before: we need to keep track of variable bindings
of the namespaces to transport |e| into the context of |e'|, i.e. those in
|depsOf S| where |S| is the sort of |e|. Figure \ref{fig:subst} contains the
refinement, which we call "traces", a well-formedness condition that expresses
the namespace restriction and a |weakenα| function for traces.

Figure \ref{fig:subst} also contains the definition of substitution. Like for
shift, we define substitution by three functions. The function |substαℕ v x n|
defines the operation for namespace |α| on indices by recursing on |x| and case
distinction on |n|. If the index and the trace match, then the result is the term
|v|. If the index |n| is strictly smaller or strictly larger than the trace |x|,
then |substαℕ| constructs a term using the variable constructor for |α|. In the
recursive cases, |substαℕ| performs the necessary shifts when coming out of the
recursion in the same order in which the binders have been crossed. This avoids
a multiplace |weaken| on terms.

The substitution |substα| traverses terms to the variable positions and weakens
the trace according to the binding specification. As previously discussed |v|
remains unchanged. The function |substα'| only recurses into the term if it is
interesting to do so.


%% Using the interpretation of binding specification we can generically define
%% \cite{knotneedle} shifting and substitution on terms:
%% $$
%% \begin{array}{c@@{\hspace{5mm}}c}
%%   $\knotbox{\text{sh}_{\alpha,S} : h \to u \to u}$ &
%%   $\knotbox{\text{su}_{\alpha,S} : h \to u \to u \to u}$ \\
%%   $\knotbox{\text{sh}_{\alpha,E} : h \to u \to u}$ &
%%   $\knotbox{\text{su}_{\alpha,E} : h \to u \to u \to u}$ \\
%% \end{array}
%% $$
%%
%% \noindent To simplify the presentation we assume that these are defined
%% without any subordination in mind, i.e. for all possible namespace and sort
%% combinations even if these amount to being the identity function and we drop the
%% subscript in cases where these can be inferred from the type of the arguments.
%%
%% Furthermore, we can generically define well-scopedness predicates on de Bruijn terms
%% which can be found in Appendix \ref{appendix:semantics}
%% $$
%% \begin{array}{c@@{\hspace{5mm}}c@@{\hspace{5mm}}c}
%%   \knotbox{h \vdash_\alpha n} & \knotbox{h \vdash_S u} & \knotbox{h \vdash_E u} \\
%% \end{array}
%% $$
%% and associated generic shifting and substitution lemmas
%% \cite{knotneedle}.


\subsection{Evaluation}\label{ssec:sem:evaluation}

\begin{figure}[t]
  \centering
  \fbox{
    \begin{minipage}{0.96\columnwidth}

      \begin{code}
      box (⟦ _ | _ ⟧ (sub _) : bs → sym → ϑ → u)

      ⟦ bs        | t                               ⟧ (sub ϑ) = ϑ t
      ⟦ bs        | K g                             ⟧ (sub ϑ) = K (ϑ g + ⟦ bs ⟧ (sub ϑ))
      ⟦ bs,b,bs'  | K b                             ⟧ (sub ϑ) = K (0 + ⟦ bs' ⟧ (sub ϑ))
      ⟦ bs        | K (overline b) (overline sym)   ⟧ (sub ϑ) = K (overline (⟦ bs, {b' ↦ b}bs' | sym ⟧ (sub ϑ)))
        where  K : (overline ((b':α))) → (overline (([bs']s:S))) → T
      ⟦ bs,bs'    | weaken sym bs'                 ⟧ (sub ϑ)         =  shstar (evalsym bs sym ϑ) (evalbs bs' ϑ)
      ⟦ bs        | subst b sym1 sym2              ⟧ (sub ϑ)         =  su 0 (evalsym bs sym1 ϑ) (evalsym (bs,b) sym2 ϑ)
      \end{code}

      %% \begin{code}
      %% box (⟦ _ | _ ⟧ (sub _) : bs → sym → ϑ → u)
      %%
      %% ⟦ bs        | t                               ⟧ (sub ϑ) = ϑ t
      %% ⟦ bs        | K g                             ⟧ (sub ϑ) = K (ϑ g + ⟦ bs ⟧ (sub ϑ))
      %% ⟦ bs,b,bs'  | K b                             ⟧ (sub ϑ) = K (0 + ⟦ bs' ⟧ (sub ϑ))
      %% ⟦ bs        | K (overline b) (overline sym)   ⟧ (sub ϑ) = K (overline (⟦ bs, bs'' | sym ⟧ (sub ϑ)))
      %%   where  K : (overline ((b':α))) → (overline (([bs']s:S))) → T
      %%          (overline (evalbig (overline (b' ↦ b),overline (s ↦ sym)) bs' bs''))
      %% ⟦ bs,bs'    | weaken sym bs'                 ⟧ (sub ϑ)         =
      %%   shstar (evalsym bs sym ϑ) (evalbs bs' ϑ)
      %% ⟦ bs        | subst b sym1 sym2              ⟧ (sub ϑ)         =
      %%   su 0 (evalsym bs sym1 ϑ) (evalsym (bs,b) sym2 ϑ)
      %% \end{code}
     \begin{tabular}{@@{}ll}
       \begin{minipage}[c]{0.25\columnwidth}
        \begin{code}
        box (shstar : u → h → u)
        \end{code}
        \end{minipage}
        &
       \begin{minipage}[c]{0.4\columnwidth}
       \begin{code}
        shstar u  0        = u
        shstar u  (Sα  h)  = shα 0 (shstar u h)
        \end{code}
        \end{minipage}
     \end{tabular}
    \end{minipage}
  }
  \caption{Expression evaluation}
  \label{fig:sem:expressions}
\end{figure}

We now define the semantics of symbolic expressions as an evaluation to concrete
de Bruijn terms. Figure~\ref{fig:sem:expressions} contains the definition. The
evaluation function takes as inputs a symbolic expression $\symbolicterm$, the
local scope $\bindspec$ of $\symbolicterm$ and an environment $\vartheta$ that
maps reference variables to concrete de Bruijn indices and sort variables to
concrete de Bruijn terms.

Sort variables $t$ are looked up in $\vartheta$. We assume that these terms are
in the same scope as $t$ and hence they do not need to be adjusted. Global
reference variables $g$ are also looked up in $\vartheta$ but need to be
adjusted by weakening with the interpretation of the current local scope
$\bindspec$. For variable constructors with locally bound variables $b$ we
determine the index by interpreting the difference $\bindspec'$ of the current
scope and the scope where $b$ was introduced. For regular constructors we
recursively evaluate each expression for the sort fields in the local scope
respectively extended with the symbolically evaluated binding specifications of
the fields. Bindings $\ov{b}$ of regular constructors are simply
dropped. Symbolic syntactic operations are replaced by applications of the
concrete versions. In case of symbolic weakening we need to evaluate the
expression argument in the smaller scope $\bindspec$ and weaken it with the
interpretation of $\bindspec'$ for which we use the multi-place shifting
function |shstar| that iterates one-place shiftings. We restricted symbolic
substitution to only allow substituting the last introduced variable and hence
always substitute the index $0$. The expression arguments of substitution need
to be evaluated in their respective local scopes.

% \begin{figure}[t]
% \begin{center}
%   \fbox{
%   \hspace{-2mm}
%   \begin{minipage}{0.98\columnwidth}
%     \begin{code}
%     box (⟦ _ | _ ⟧ (sub _) : bs → sym → ϑ → u)
%
%     ⟦ bs        | t                              ⟧ (sub ϑ) = ϑ t
%     ⟦ bs        | K g                            ⟧ (sub ϑ) = K (ϑ g + ⟦ bs ⟧ (sub ϑ))
%     ⟦ bs,b,bs'  | K b                            ⟧ (sub ϑ) = K (0 + ⟦ bs' ⟧ (sub ϑ))
%     ⟦ bs        | K (overline b) (overline sym)  ⟧ (sub ϑ) = K (overline (⟦ bs, bs'' | sym ⟧ (sub ϑ)))
%       where  K : (overline ((b':α))) → (overline (([bs']s:S))) → T
%              (overline (evalbig (overline (b' ↦ b),overline (s ↦ sym)) bs' bs''))
%     ⟦ bs,bs'    | weaken sym bs'                 ⟧ (sub ϑ)         =
%       shstar (evalsym bs sym ϑ) (evalbs bs' ϑ)
%     ⟦ bs        | subst b sym1 sym2              ⟧ (sub ϑ)         =
%       su 0 (evalsym bs sym1 ϑ) (evalsym (bs,b) sym2 ϑ)
%     \end{code}
%
%    \begin{tabular}{@@{}ll}
%    \begin{minipage}[c]{0.3\columnwidth}
%     \begin{code}
%     box (shstar : u → h → u)
%     \end{code}
%     \end{minipage}
%     &
%    \begin{minipage}[c]{0.4\columnwidth}
%    \begin{code}
%     shstar u  0        = u
%     shstar u  (Sα  h)  = shα 0 (shstar u h)
%     \end{code}
%     \end{minipage}
%     \end{tabular}
%   \end{minipage}
% }
% \end{center}
% \caption{Interpretation of symbolic expressions}
% \label{fig:evalsymbolicterm}
% \end{figure}

%-------------------------------------------------------------------------------

%%% Local Variables:
%%% mode: latex
%%% TeX-master: "../Main"
%%% End:

%% (add-to-list 'TeX-command-list '("Make" "make" TeX-run-compile nil t))
