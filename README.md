# *ord-axiomata*

When using `Data.Type.Ord`, there are many facts one intuitively expects to hold that GHC is not clever enough to infer.

We rectify this situation with a `TotalOrder` typeclass that not only enables comparison of singletons, but also provides axiomata allowing one to safely prove such facts to GHC.

## Axiomata

Alongside `TotalOrder`, there are a few other accompanying classes.
$\newcommand{\s}{ \kern3pt }
\newcommand{\narrow}{ \kern6pt }
\newcommand{\wide}{ \quad\quad\quad }
\newcommand{\colon}{ \kern-2pt : }
\newcommand{\min}[2]{ \mathrm{min} \s #1 \s #2 }
\newcommand{\max}[2]{ \mathrm{max} \s #1 \s #2 }$

### Equivalence

$$
\begin{alignat*}{3}
&\text{reflexivity} \wide && \forall a \colon \narrow &&
  a = a \\
&\text{symmetry} \wide && \forall a, b \colon \narrow &&
  a = b \implies b = a \\
&\text{transitivity} \wide && \forall a, b, c \colon \narrow &&
  a = b \land b = c \implies a = c \\
\end{alignat*}
$$

### Total Ordering

$$
\begin{alignat*}{3}
&\text{strong connectivity} \wide && \forall a, b \colon \narrow &&
  a \lt b \lor a = b \lor a \gt b \\
&\text{anti-symmetry} \wide && \forall a, b \colon \narrow &&
  a \le b \implies b \ge a \\
&\text{transitivity} \wide && \forall a, b, c \colon \narrow &&
  a \leq b \land b \leq c \implies a \leq c \\
\end{alignat*}
$$

### Bounding

$$
\begin{alignat*}{3}
&\text{bounded below} \wide && \exists l \forall a \colon \narrow &&
  l \leq a \\
&\text{bounded above} \wide && \exists u \forall a \colon \narrow &&
  a \leq u \\
\end{alignat*}
$$

## Lemmata

With the above at our disposal, we can prove general, reusable facts.
Both for practical use and as demonstration, we provide several lemmata for the `Min` and `Max` type families.

### Minimum

$$
\begin{alignat*}{3}
&\text{deflationary} \wide && \forall a, b \colon \narrow &&
  \min a b \leq a, b \\
&\text{monotonicity} \wide && \forall a, b, c, d \colon \narrow &&
  a \leq c \land b \leq d \implies \min a b \leq \min c d \\
\end{alignat*}
$$

### Maximum

$$
\begin{alignat*}{3}
&\text{inflationary} \wide && \forall a, b \colon \narrow &&
  a, b \leq \max a b \\
&\text{monotonicity} \wide && \forall a, b, c, d \colon \narrow &&
  a \leq c \land b \leq d \implies \max a b \leq \max c d \\
\end{alignat*}
$$

