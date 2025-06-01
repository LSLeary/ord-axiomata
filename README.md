# *ord-axiomata*

When using `Data.Type.Ord`, there are many facts one intuitively expects to hold that GHC is not clever enough to infer.

We rectify this situation with `TotalOrder` and related typeclasses that not only enable comparison of singletons, but also provide axiomata allowing one to safely prove such facts to GHC.

## Axiomata

Due to GHC/Haskell specific details and the expression of equivalence and ordering in terms of `Compare`, the phrasing of the axiomata is a little different than usual—many are reduced to consistency conditions with `~` and the following definitions.

$$
\begin{alignat*}{3}
  &a  <   b &&\iff &&\mathrm{Compare} \kern3pt a \kern3pt b \sim \mathrm{LT} \\
  &a  =   b &&\iff &&\mathrm{Compare} \kern3pt a \kern3pt b \sim \mathrm{EQ} \\
  &a  >   b &&\iff &&\mathrm{Compare} \kern3pt a \kern3pt b \sim \mathrm{GT} \\
  &a \leq b &&\iff &&a < b \lor a = b                                        \\
  &a \neq b &&\iff &&a < b \lor a > b                                        \\
  &a \geq b &&\iff &&a = b \lor a > b
\end{alignat*}
$$

### Equivalence

$$
\begin{alignat*}{3}
&\text{decidability}     \quad\quad\quad && \forall a, b.
  \kern6pt && a = b \lor a \neq b     \\
&\text{reflexivity}      \quad\quad\quad && \forall a, b.
  \kern6pt && a \sim b \implies a = b \\
&\text{substitutability} \quad\quad\quad && \forall a, b.
  \kern6pt && a = b \implies a \sim b \\
\end{alignat*}
$$

### Total Ordering

$$
\begin{alignat*}{3}
&\text{connectivity}                 \quad\quad\quad && \forall a, b.
  \kern6pt && a < b \lor a = b \lor a > b               \\
&\text{anti-symmetry of $\lt$/$\gt$} \quad\quad\quad && \forall a, b.
  \kern6pt && a < b \iff b > a                          \\
&\text{transitivity of $\leq$}       \quad\quad\quad && \forall a, b, c.
  \kern6pt && a \leq b \land b \leq c \implies a \leq c \\
\end{alignat*}
$$

### Bounding

$$
\begin{alignat*}{3}
&\text{bounded below} \quad\quad\quad && \exists b_l \forall a.
  \kern6pt && b_l \leq a \\
&\text{bounded above} \quad\quad\quad && \exists b_u \forall a.
  \kern6pt && a \leq b_u \\
\end{alignat*}
$$

## Lemmata

With the above at our disposal, we can prove general, reusable facts.

### Equivalence

$$
\begin{alignat*}{3}
&\text{symmetry of $=$}     \quad\quad\quad && \forall a, b.
  \kern6pt && a = b \iff b = a                 \\
&\text{symmetry of $\neq$}  \quad\quad\quad && \forall a, b.
  \kern6pt && a \neq b \iff b \neq a           \\
&\text{transitivity of $=$} \quad\quad\quad && \forall a, b, c.
  \kern6pt && a = b \land b = c \implies a = c \\
\end{alignat*}
$$

### Ordering

#### Reflection

$$
\begin{alignat*}{3}
&\text{anti-symmetry of $\leq$/$\geq$} \quad\quad\quad && \forall a, b.
  \kern6pt && a \leq b \iff b \geq a
\end{alignat*}
$$

#### Transitivity

$$
\begin{alignat*}{3}
&\text{transitivity of $\lt$}  \quad\quad\quad && \forall a, b, c.
  \kern6pt && a \lt  b \land b \lt  c \implies a \lt  c \\
&\text{transitivity of $\gt$}  \quad\quad\quad && \forall a, b, c.
  \kern6pt && a \gt  b \land b \gt  c \implies a \gt  c \\
&\text{transitivity of $\geq$} \quad\quad\quad && \forall a, b, c.
  \kern6pt && a \geq b \land b \geq c \implies a \geq c \\
\end{alignat*}
$$


#### Properties of Minimum

$$
\begin{alignat*}{3}
&\text{deflationary} \quad\quad\quad && \forall a, b.
  \kern6pt && \mathrm{min} \kern3pt a \kern3pt b \leq a, b \\
&\text{monotonicity} \quad\quad\quad && \forall a, b, c, d.
  \kern6pt && a \leq c \land b \leq d
    \implies \mathrm{min} \kern3pt a \kern3pt b
        \leq \mathrm{min} \kern3pt c \kern3pt d            \\
&\text{symmetry}     \quad\quad\quad && \forall a, b.
  \kern6pt && \mathrm{min} \kern3pt a \kern3pt b
    \sim \mathrm{min} \kern3pt b \kern3pt a                \\
\end{alignat*}
$$

#### Properties of Maximum

$$
\begin{alignat*}{3}
&\text{inflationary} \quad\quad\quad && \forall a, b.
  \kern6pt && a, b \leq \mathrm{max} \kern3pt a \kern3pt b \\
&\text{monotonicity} \quad\quad\quad && \forall a, b, c, d.
  \kern6pt && a \leq c \land b \leq d
    \implies \mathrm{max} \kern3pt a \kern3pt b
        \leq \mathrm{max} \kern3pt c \kern3pt d            \\
&\text{symmetry}     \quad\quad\quad && \forall a, b.
  \kern6pt && \mathrm{max} \kern3pt a \kern3pt b
    \sim \mathrm{max} \kern3pt b \kern3pt a                \\
\end{alignat*}
$$

