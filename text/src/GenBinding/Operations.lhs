%include lhs2TeX.fmt
%include forall.fmt
%include polycode.fmt
%include Formatting.fmt

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
\section{Infrastructure Operations}
\label{sec:operation}

In this section, we generically define common infrastructure operations
generically over all terms of a specifications. This includes shifting and
substitution in sort and environment terms and lookups in environments.
\scw{This section is good at explaining WHAT the system does, but it doesn't go much into
  contributions of the work. What is the new idea here? What was difficult?}


%-------------------------------------------------------------------------------
\subsection{Shifting}\label{ssec:shifting}

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


%-------------------------------------------------------------------------------
\subsection{Substitution}\label{ssec:substitution}

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


%-------------------------------------------------------------------------------
\subsection{Environment lookups}\label{ssec:contextlookups}

The paramount infrastructure operation on environments is the lookup of
variables and their associated data. Lookup is a partial function. For that
reason, we define it as a relation |(n:overline u) inα Γ| that witnesses that
looking up the index |n| of namespace |α| in the environment term |Γ| is valid
and that |overline u| is the associated data. Figure \ref{fig:environmentlookup}
contains the definition.

Rule \textsc{InHere} forms the base case where |n = 0|. In this case the
environment term needs to be a cons for namespace |α|. Note that well-scopedness
of the associated data is included as a premise. This reflects common practice
of annotating variable cases with with well-scopedness conditions. By moving it
into the lookup itself, we free the user from dealing with this obligation
explicitly. We need to |weaken| the result of the lookup to account for the
binding.

Rule \textsc{InThere} encodes the case that the lookup is not the last cons of
the environment. The rule handles both the homogeneous |α = β| and the
heterogeneous case |α ≠ β| by means of weakening the index |n|. The associated
data is also shifted to account for the new |β| binding.

\begin{figure}[t]
\begin{center}
\fbox{
  \begin{minipage}{0.95\columnwidth}
  \framebox{\mbox{|(n : overline u) inα Γ|}} \\
  \vspace{-7mm}
  \[ \begin{array}{c}
     \inferrule* [right=\textsc{InHere}]
                 {|domain Γ ⊢ u_i| \quad (\forall i)}
                 {|(0 : overline (weaken u Iα)) inα (Γ ► overline u)|}  \\ \vspace{-2mm} \\
     \inferrule* [right=\textsc{InThere}]
                 {|(n : overline u) inα Γ|}
                 {|(weakenα n Iβ : overline (weaken u Iβ)) inα (Γ ►► overline v)|}
     \end{array}
  \]
  \end{minipage}
}
\end{center}
\caption{Environment lookup}
\label{fig:environmentlookup}
\end{figure}

%%% Local Variables:
%%% mode: latex
%%% TeX-master: "../Main"
%%% End:
