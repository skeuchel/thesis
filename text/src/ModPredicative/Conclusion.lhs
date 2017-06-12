
\section{Scientific Output}\label{sec:modp:conclusion}

Main contributions of this work are

\begin{itemize}
\item Bringing existing work from the fields of modularity, genericity and type
  theory together in the same framework.
\item A novel representation of proof algebras that serves as a connection
  between these fields.
\end{itemize}

Below we make the border between prior work and this work precise.

Modular programming and the expression problem have been studied
extensively. The Datatypes \`a la Carte~\cite{dtc} approach is an existing
solution in a purely functional programming setting. Metatheory \`a la
Carte~\cite{mtc} extends DTC to modular proving. We reuse most of the
definitions from MTC, in particular automation of compositions. The main
difference and contribution of this work is the change to a new datatype-generic
based representation of signature functors that provides an alternative to the
Church encodings of MTC. This alternative representation addresses multiple
shortcoming of MTC.

Datatype-generic programming (DGP) or polytypic
programming~\cite{jansson1997polyp} is an established field in functional
programming which has also seen extensive use in dependently-type
theory~\cite{benke:ugpp}. The universe of containers is a well-studied subject,
including generic functionality like generic induction for
containers~\cite{categoriesofcontainers}. The container-based representation
allows us to define generic fixed-points, folds and induction principles that
meet the requirements of proof-assistants. We combine this work with modular
programming.

We use all-modalities to achieve a uniform representation of proof-algebras.
All-modalities have been used implicitly by \cite{benke:universes} to define
generic induction but have not been worked out as a
concept. \cite{morris2007constructing} models all-modalities explicitly for
datatype-generic universes but does not use them to generic induction
principles. Our contribution is to provide the last missing piece: use model
proof-algebras on all-modalities explicitly and uniformly, in order to define
generic induction.



%% MTC uses extensible Church encodings to overcome conservative restrictions
%% imposed by the Coq proof-assistant. This approach has shortcomings in terms
%% of confidence in the definitions and in terms of usability. These
%% shortcomings are addressed by using datatype-generic programming techniques
%% to replace Church encodings as the underlying representation of type-level
%% fixed points. Our approach avoids impredicativity, adequately encodes fixed
%% points and leads to stronger induction principles by exploiting DGP
%% approaches that capture only strictly-positive functors.
%%
%% Working with generic structure representation has the added benefit that we can
%% implement generic functions like equality and generic proofs once and for all.


%%% Local Variables:
%%% mode: latex
%%% TeX-master: "../../mod"
%%% End:
