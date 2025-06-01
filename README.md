# *ord-axiomata*

When using `Data.Type.Ord`, there are many facts one intuitively expects to hold that GHC is not clever enough to infer.

We rectify this situation with a `TotalOrder` typeclass that not only enables comparison of singletons, but also provides axiomata allowing one to safely prove such facts to GHC.

## Axiomata

Alongside `TotalOrder`, there are a few other accompanying classes.

### Equivalence

$$
\begin{alignat*}{3}
&\text{reflexivity}  \quad\quad\quad && \forall a       \kern-2pt :
  \kern6pt && a = a \\
&\text{symmetry}     \quad\quad\quad && \forall a, b    \kern-2pt :
  \kern6pt && a = b \implies b = a \\
&\text{transitivity} \quad\quad\quad && \forall a, b, c \kern-2pt :
  \kern6pt && a = b \land b = c \implies a = c \\
\end{alignat*}
$$

### Total Ordering

$$
\begin{alignat*}{3}
&\text{strong connectivity} \quad\quad\quad && \forall a, b    \kern-2pt :
  \kern6pt && a \lt b \lor a = b \lor a \gt b \\
&\text{anti-symmetry}       \quad\quad\quad && \forall a, b    \kern-2pt :
  \kern6pt && a \le b \implies b \ge a \\
&\text{transitivity}        \quad\quad\quad && \forall a, b, c \kern-2pt :
  \kern6pt && a \leq b \land b \leq c \implies a \leq c \\
\end{alignat*}
$$

### Bounding

$$
\begin{alignat*}{3}
&\text{bounded below} \quad\quad\quad && \exists l \forall a \kern-2pt :
  \kern6pt && l \leq a \\
&\text{bounded above} \quad\quad\quad && \exists u \forall a \kern-2pt :
  \kern6pt && a \leq u \\
\end{alignat*}
$$

## Lemmata

With the above at our disposal, we can prove general, reusable facts.
Both for practical use and as demonstration, we provide several lemmata for the `Min` and `Max` type families.

### Minimum

$$
\begin{alignat*}{3}
&\text{deflationary} \quad\quad\quad && \forall a, b \kern-2pt :
  \kern6pt && \mathrm{min} \kern3pt a \kern3pt b \leq a, b \\
&\text{monotonicity} \quad\quad\quad && \forall a, b, c, d \kern-2pt :
  \kern6pt && a \leq c \land b \leq d
    \implies \mathrm{min} \kern3pt a \kern3pt b
        \leq \mathrm{min} \kern3pt c \kern3pt d \\
\end{alignat*}
$$

### Maximum

$$
\begin{alignat*}{3}
&\text{inflationary} \quad\quad\quad && \forall a, b \kern-2pt :
  \kern6pt && a, b \leq \mathrm{max} \kern3pt a \kern3pt b \\
&\text{monotonicity} \quad\quad\quad && \forall a, b, c, d \kern-2pt :
  \kern6pt && a \leq c \land b \leq d
    \implies \mathrm{max} \kern3pt a \kern3pt b
        \leq \mathrm{max} \kern3pt c \kern3pt d \\
\end{alignat*}
$$

