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
\subsection{Shifting and Weakening}\label{ssec:sem:shifting}

% We generically define common infrastructure operations generically over all
% terms of a specifications. This includes shifting and substitution in sort and
% environment terms.

\begin{figure}[t]
  \centering
  \fbox{
    \begin{minipage}{0.96\columnwidth}
      % \[\begin{array}{@@{}l@@{\hspace{1mm}}c@@{\hspace{1mm}}lr}
      %     c   & ::=  & 0 \mid |S|~c ~~   & \text{Cutoffs}
      %   \end{array}
      % \]
      \begin{code}
      box (shiftαN : c → n → n)

      shiftαN 0      n      =  S n
      shiftαN (Sα c) 0      =  0
      shiftαN (Sα c) (S n)  =  S (shiftαN c n)
      shiftαN (Sβ c) n      =  shiftαN c n
        where α ≠ β

      box (shiftαS : c → u → u)

      shiftαS c (K n)             = if K : α → S then K (shiftαN c n) else K n
      shiftαS c (K (overline u))  = K (overline (shiftαT (c + (subscript (⟦ bs ⟧) ϑ)) u))
        where
          K : (overline (b : β)) -> ((overline ([bs] t : T))) -> S
          ϑ = overline (t ↦ u)

      box (weakenS : u → h → u)

      weakenS u 0       =  u
      weakenS u (Sα h)  =  shiftαS 0 (weakenS u h)

      \end{code}

       %%box (shiftα' : c → u → u)
       %%
       %%shiftα' c u =
       %%  if α ∈ depsOf u
       %%    then shiftα c u else u
    \end{minipage}
  }
  \caption{Shifting of terms}
  \label{fig:shift}
\end{figure}


Shifting adapts indices when a variable $x$ is inserted into the context which
is generically defined in Figure \ref{fig:shift}. The |shift| function is
parameterized over the namespace $\alpha$ of variable $x$ in which the shift is
performed and the sort $S$ of the term that the function operates on. In case of
a variable constructor $K : \alpha \to S$, the index is shifted using the
|shiftαN| function, which implements shifting indices for namespace
$\alpha$. For variable constructors of other namespaces, we keep the index
unchanged. In the case of a regular constructor, we need to calculate the
cut-offs for the recursive calls. This is done by evaluating the binding
specification |bs| and weakening the cut-off $c$ accordingly.

To avoid clutter, the definition presented here does not take subordination into
account, i.e. for \fexistsprod a shifting of term variables inside a term will
also recurse into types. Since types do not contain term variables this is
effectively the identity function. This can of course be optimized. The paper
\cite{knotneedle} contains this optimized version.

% Using the calculated cut-offs, the |shiftα| function can proceed recursively on
% the subterms that depend on the namespace $\alpha$.

% Instead of using the traditional arithmetical implementation
% $$|if n < c then n else n + 1|$$
% we use an equivalent recursive definition of |shiftN| that inserts the successor
% constructor \emph{at the right place}. This follows the inductive structure of
% |Δ| which facilitates inductive proofs on |Δ|.

\paragraph{Weakening}

Weakening is the transportation of a sort term to a bigger context where
variables are only added at the end.  Figure~\ref{fig:shift} shows the
implementation of |weakenS| that iterates the 1-place |shiftαS| function. Its
second parameter |h| represents the domain of the context extension.

\subsection{Substitution}\label{ssec:sem:substitution}

\begin{figure}[t]
  \centering
  \fbox{
    \begin{minipage}{0.98\columnwidth}
      %% \[\begin{array}{@@{}l@@{\hspace{1mm}}c@@{\hspace{1mm}}lr}
      %%     x   & ::=  & 0 \mid |Sα|~x ~~   & \text{Trace}
      %%   \end{array}
      %% \]

      %% \framebox{\mbox{$\vdash_\alpha x$}} \\
      %% \[ \begin{array}{c}
      %%    \inferrule* [right=\textsc{WfTraceZero}]
      %%                {\,}
      %%                {\vdash_\alpha 0} \quad
      %%    \inferrule* [right=\textsc{WfTraceSucc}]
      %%                {\vdash_\alpha n \\
      %%                 |β ∈ depsOf α|}
      %%                {\vdash_\alpha Sβ~n}
      %%    \end{array}
      %%  \]

      %% box (weakenα :: x → h → x)
      %%
      %% weakenα c 0       =  c
      %% weakenα c (Sβ h)  =
      %%   if β ∈ depsOf α
      %%      then Sβ (weakenα x h)
      %%      else weakenα x h


      \begin{code}
      box (substαN : c → v → n → u)
      substαN 0       v 0      =  v
      substαN 0       v (S n)  =  K n
        where K : α → T
      substαN (Sα x)  v 0      =  K 0
        where K : α → T
      substαN (Sα c)  v (S n)  =  weakenS (substαN c v n) Iα
      substαN (Sβ c)  v n      =  weakenS (substαN c v n) Iβ

      box (substαS : c → v → u → u)

      substαS c v (K n)             = if K : α → S then substαN c v n else K n
      substαS c v (K (overline u))  = K (overline (substαT (c + (subscript (⟦ bs ⟧) ϑ)) v u))
        where
          K : (overline (b : β)) → ((overline ([bs] t : T))) → S
          ϑ = overline (t ↦ u)
      \end{code}

      %% box (substα' :: v → x → u → u)
      %%
      %% substα' v x u =
      %%   if α ∈ depsOf u
      %%     then substα v x u
      %%     else u
    \end{minipage}
  }
  \caption{Substitution of terms}
  \label{fig:subst}
\end{figure}

%% For the definition of substitution, we again need to use a refinement of natural
%% numbers, a different one from before: we need to keep track of variable bindings
%% of the namespaces to transport |e| into the context of |e'|, i.e. those in
%% |depsOf S| where |S| is the sort of |e|. Figure \ref{fig:subst} contains the
%% refinement, which we call "traces", a well-formedness condition that expresses
%% the namespace restriction and a |weakenα| function for traces.

Figure \ref{fig:subst} also contains the definition of substitution. Like for
shift, we define substitution by two functions. The function |substαN c v n|
defines the operation for namespace |α| on indices by recursing on |c| and case
distinction on |n|. If the index and the cut-off match, then the result is the
term |v|. If the index |n| is strictly smaller or strictly larger than the
cut-off |c|, then |substαN| constructs a term using the variable constructor for
|α|. In the recursive cases, |substαN| performs the necessary weakenings when
coming out of the recursion in the same order in which the binders have been
crossed. This avoids a multiplace |weaken| on terms. The substitution |substαS|
traverses terms to the variable positions and weakens the trace according to the
binding specification. As previously discussed |v| remains unchanged.

Like for shifting we can use subordination information to avoid recursing into
sub-terms for which we statically know that they do not contain variables. The
paper \cite{knotneedle} also contains this optimized version.



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
      box (evalsymS : bs → sym → ϑ → u)

      evalsymS bs          t                                ϑ = ϑ t
      evalsymS bs          (K g)                            ϑ = K (ϑ g + ⟦ bs ⟧ (sub ϑ))
      evalsymS (bs,b,bs')  (K b)                            ϑ = K (0 + ⟦ bs' ⟧ (sub ϑ))
      evalsymS bs          (K (overline b) (overline sym))  ϑ =
          K (overline (evalsymT (bs, {(overline (b' ↦ b))} bs') sym ϑ))
        where K : (overline ((b':α))) → (overline (([bs']s:S))) → T
      evalsymS (bs,bs')    (weaken sym bs')                 ϑ =
          weakenS (evalsymS bs sym ϑ) (evalbs bs' ϑ)
      evalsymS bs          (subst b sym1 sym2)              ϑ =
        substαS 0 (evalsymT bs sym1 ϑ) (evalsymS (bs,b) sym2 ϑ)
        where K : α → T
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

     %% \begin{tabular}{@@{}ll}
     %%   \begin{minipage}[c]{0.25\columnwidth}
     %%    \begin{code}
     %%    box (shstar : u → h → u)
     %%    \end{code}
     %%    \end{minipage}
     %%    &
     %%   \begin{minipage}[c]{0.4\columnwidth}
     %%   \begin{code}
     %%    shstar u  0        = u
     %%    shstar u  (Sα  h)  = shα 0 (shstar u h)
     %%    \end{code}
     %%    \end{minipage}
     %% \end{tabular}
    \end{minipage}
  }
  \caption{Expression evaluation}
  \label{fig:sem:expressions}
\end{figure}

We now define the semantics of symbolic expressions as an evaluation to concrete
de Bruijn terms. Figure~\ref{fig:sem:expressions} contains the definition. The
evaluation function takes as inputs a symbolic expression $\symbolicterm$, the
local scope $\bindspec$ of $\symbolicterm$ and a value environment $\vartheta$
for global and sort meta-variables.

Sort variables $t$ are looked up in $\vartheta$. We assume that these terms are
in the same scope as $t$ and hence they do not need to be adjusted. Global
reference variables $g$ are also looked up in $\vartheta$ but need to be
adjusted by weakening with the interpretation of the current local scope
$\bindspec$. For variable constructors with locally bound variables $b$ we
determine the index by interpreting the difference $\bindspec'$ of the current
scope and the scope where $b$ was introduced. For regular constructors we
recursively evaluate each expression for the sort fields in the local scope
respectively extended with the symbolically evaluated binding specifications of
the fields. Bindings $\ov{b}$ of regular constructors are dropped.

Symbolic syntactic operations are replaced by applications of the concrete
versions. In case of symbolic weakening we need to evaluate the expression
argument in the smaller scope $\bindspec$ and weaken it with the interpretation
of $\bindspec'$ for which we use the concrete multi-place weakening
|weakenS|. We restricted symbolic substitution to only allow substituting the
last introduced variable and hence always substitute the index $0$. The
expression arguments of substitution need to be evaluated in their respective
local scopes.

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
