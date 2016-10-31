
\section{Conclusion}\label{sec:modp:conclusion}
Formally mechanizing proofs can be very tedious and the amount of work required
for larger developments is excruciating. Meta-Theory \`a la Carte is a framework
for modular reusable components for use in mechanizations. It builds on the
Datatypes \`a la Carte approach to solve an extended version of the expression
problem. MTC allows modular definitions of datatypes, semantic functions and
logical relations and furthermore modular inductive proofs.

MTC uses extensible Church encodings to overcome conservative restrictions
imposed by the Coq proof-assistant. This approach has shortcomings in terms of
confidence in the definitions and in terms of usability. These shortcomings are
addressed by using datatype-generic programming techniques to replace Church
encodings as the underlying representation of type-level fixed points. Our
approach avoids impredicativity, adequately encodes fixed points and leads to
stronger induction principles by exploiting DGP approaches that capture only
strictly-positive functors.

Working with generic structure representation has the added benefit that we can
implement generic functions like equality and generic proofs once and for all.


%%% Local Variables:
%%% mode: latex
%%% TeX-master: "../../mod"
%%% End:
