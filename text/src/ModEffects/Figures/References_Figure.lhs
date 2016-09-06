%include lhs2TeX.fmt
%include polycode.fmt
%include forall.fmt
%include Formatting.fmt
%include macros.fmt

%format myLookup = "\Varid{fetch}"
%format fail1 = "\Varid{fail}"

\begin{figure*}[t]
  \scriptsize
  \centering
  \fbox{\begin{minipage}[t]{0.981391\columnwidth}
    \begin{tabular}{@@{\hspace{-7.5mm}}l@@{}l}
      \begin{minipage}[t]{0.5\linewidth}
        \hspace{7mm}\ruleline{Simplified value interface}
        \vspace{-12pt}
        \begin{spec}
          type Value

          loc    :: Int -> Value
          stuck  :: Value
          unit   :: Value
          isLoc  :: Value -> Maybe Int
        \end{spec}

        \hspace{7mm}\ruleline{Expression functor}
        \vspace{-12pt}
        \begin{spec}
          data RefF a  = Ref a
                       | DeRef a
                       | Assign a a

          type Store = [Value]
        \end{spec}

        \hspace{7mm}\ruleline{Monadic typing algebra}
        \vspace{-12pt}
        \begin{spec}
          typeofRef ::  FailMonad m =>
                          MAlgebra RefF (m Type)
          typeofRef rec (Ref e) = do
            t <- rec e
            return (tRef t)
          typeofRef rec (DeRef e) = do
            te <- rec e
            maybe fail1 return (isTRef te)
          typeofRef rec (Assign e1 e2) = do
            t1 <- rec e1
            case isTRef t1 of
              Nothing  -> fail1
              Just t   -> do
                t2 <- rec e2
                if (t == t2)
                  then return tUnit
                  else fail1
        \end{spec}

      \end{minipage}
    &
      \begin{minipage}[t]{0.5\linewidth}

        \hspace{7mm}\ruleline{Simplified type interface}
        \vspace{-12pt}
        \begin{spec}
          type Type

          tRef    :: Type -> Type
          tUnit   :: Type
          isTRef  :: Type -> Maybe Type
        \end{spec}


        \hspace{7mm}\ruleline{Monadic evaluation algebra}
        \begin{spec}
          evalRef ::  MonadState Store m =>
                        MAlgebra RefF (m Value)
          evalRef rec (Ref e) = do
            v    <- rec e
            env  <- get
            put (v : env)
            return (loc (length env))
          evalRef rec (DeRef e) = do
            v    <- rec e
            env  <- get
            return $
              case isLoc v of
                Nothing  -> stuck
                Just n   ->
                  maybe stuck id (myLookup n env)
          evalRef rec (Assign e1 e2) = do
            v    <- rec e1
            env  <- get
            case isLoc v of
              Nothing  -> return stuck
              Just n   -> do
                v2 <- rec e2
                put (replace n v2 env)
                return unit
        \end{spec}

      \end{minipage} \\

    \end{tabular}

    \vspace{-3mm}
  \end{minipage}}
  \vspace{-3mm}
  \caption{Syntax and type definitions for references.}
  \label{fig:mod:references:datatypes}
\end{figure*}
