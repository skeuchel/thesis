%include lhs2TeX.fmt
%include polycode.fmt
%include forall.fmt
%include Formatting.fmt
%include macros.fmt

%format myLookup = "\Varid{fetch}"
%format fail1 = "\Varid{fail}"

\begin{figure*}[!ht]

\scriptsize
\begin{center}
\begin{tabular}{||ccc||}
\hline
\hspace{-.5cm}
\begin{minipage}[t]{0.23\linewidth}
\vspace{-.15cm}
\hspace{-5pt}

\hspace{.65cm}\ruleline{\scriptsize Simplified value interface}
< type Value
<
< loc    :: Int -> Value
< stuck  :: Value
< unit   :: Value
< isLoc  :: Value -> Maybe Int

\vspace{-3pt}

\hspace{.65cm}\ruleline{\scriptsize Simplified type interface}
< type Type
<
< tRef    :: Type -> Type
< tUnit   :: Type
< isTRef  :: Type -> Maybe Type

\vspace{-3pt}

\hspace{.65cm}\ruleline{\scriptsize Expression functor}
> data RefF a = Ref a 
>             | DeRef a 
>             | Assign a a

> type Store = [Value]
>
\end{minipage} & 

\begin{minipage}[t]{0.28\linewidth}
\vspace{-.05cm}

\hspace{.65cm}\ruleline{\scriptsize Monadic typing algebra}
> typeofRef :: FailMonad m => 
>           MAlgebra RefF (m Type)
> typeofRef rec (Ref e) =
>   do  t <- rec e
>       return (tRef t)
> typeofRef rec (DeRef e) =
>   do  te <- rec e
>       maybe fail1 return (isTRef te)
> typeofRef rec (Assign e1 e2) =
>   do  t1 <- rec e1
>       case isTRef t1 of
>          Nothing -> fail1
>          Just t -> do  t2 <- rec e2
>                        if (t == t2) 
>                           then return tUnit
>                           else fail1

\end{minipage}

&

\begin{minipage}[t]{0.43\linewidth}
\vspace{-.05cm}

\hspace{.65cm}\ruleline{\scriptsize Monadic evaluation algebra}
> evalRef :: MonadState Store m => MAlgebra RefF (m Value)
> evalRef rec (Ref e) =
>   do  v    <- rec e
>       env  <- get
>       put (v : env)
>       return (loc (length env))
> evalRef rec (DeRef e) =
>   do  v    <- rec e
>       env  <- get
>       case isLoc v of
>           Nothing -> return stuck
>           Just n -> return (maybe stuck id (myLookup n env))
> evalRef rec (Assign e1 e2) =
>   do  v    <- rec e1
>       env  <- get
>       case isLoc v of
>          Nothing  -> return stuck
>          Just n   -> do  v2 <- rec e2
>                          put (replace n v2 env)
>                          return unit
\end{minipage}\\
\hline
\end{tabular}
\end{center}
\vspace{-.2cm}
\caption{Syntax, type, and semantic function definitions for references.}
\label{fig:references}
\vspace{-.3cm}
\end{figure*}
