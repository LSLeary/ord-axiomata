# *ord-axiomata*

When using `Data.Type.Ord`, there are many facts one intuitively expects to hold that GHC is not clever enough to infer.

We rectify this situation with `TotalOrder` and related typeclasses that not only enable comparison of singletons, but also provide axiomata allowing one to safely prove such facts to GHC.

## Axiomata

Due to the expression of equivalence and ordering in terms of `Compare`, the phrasing of the axiomata is a little different than normal—some are reduced to consistency conditions for the following definitions.

$$
\begin{alignat*}{3}
  &a  <   b &&\iff &&\mathrm{Compare} \kern3pt a \kern3pt b \sim \mathrm{LT} \\
  &a  =   b &&\iff &&\mathrm{Compare} \kern3pt a \kern3pt b \sim \mathrm{EQ} \\
  &a  >   b &&\iff &&\mathrm{Compare} \kern3pt a \kern3pt b \sim \mathrm{GT} \\
  &a \leq b &&\iff &&a < b \lor a = b                                        \\
  &a \geq b &&\iff &&a > b \lor a = b
\end{alignat*}
$$

### Equivalence

$$
\begin{alignat*}{3}
&\text{decidability}     \quad\quad\quad && \forall a, b \kern-2pt :
  \kern6pt && a = b \lor a \neq b     \\
&\text{reflexivity}      \quad\quad\quad && \forall a, b \kern-2pt :
  \kern6pt && a \sim b \implies a = b \\
&\text{substitutability} \quad\quad\quad && \forall a, b \kern-2pt :
  \kern6pt && a = b \implies a \sim b \\
\end{alignat*}
$$

### Total Ordering

$$
\begin{alignat*}{3}
&\text{connectivity}  \quad\quad\quad && \forall a, b    \kern-2pt :
  \kern6pt && a \lt b \lor a = b \lor a \gt b           \\
&\text{anti-symmetry} \quad\quad\quad && \forall a, b    \kern-2pt :
  \kern6pt && a \le b \implies b \ge a                  \\
&\text{transitivity}  \quad\quad\quad && \forall a, b, c \kern-2pt :
  \kern6pt && a \leq b \land b \leq c \implies a \leq c \\
\end{alignat*}
$$

### Bounding

$$
\begin{alignat*}{3}
&\text{bounded below} \quad\quad\quad && \exists b_l \forall a \kern-2pt :
  \kern6pt && b_l \leq a \\
&\text{bounded above} \quad\quad\quad && \exists b_u \forall a \kern-2pt :
  \kern6pt && a \leq b_u \\
\end{alignat*}
$$

## Lemmata

With the above at our disposal, we can prove general, reusable facts.

### Equivalence

$$
\begin{alignat*}{3}
&\text{symmetry}     \quad\quad\quad && \forall a, b    \kern-2pt :
  \kern6pt && a = b \iff b = a                 \\
&\text{transitivity} \quad\quad\quad && \forall a, b, c \kern-2pt :
  \kern6pt && a = b \land b = c \implies a = c \\
\end{alignat*}
$$

### Minimum

$$
\begin{alignat*}{3}
&\text{deflationary} \quad\quad\quad && \forall a, b \kern-2pt :
  \kern6pt && \mathrm{min} \kern3pt a \kern3pt b \leq a, b \\
&\text{monotonicity} \quad\quad\quad && \forall a, b, c, d \kern-2pt :
  \kern6pt && a \leq c \land b \leq d
    \implies \mathrm{min} \kern3pt a \kern3pt b
        \leq \mathrm{min} \kern3pt c \kern3pt d            \\
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
        \leq \mathrm{max} \kern3pt c \kern3pt d            \\
\end{alignat*}
$$

