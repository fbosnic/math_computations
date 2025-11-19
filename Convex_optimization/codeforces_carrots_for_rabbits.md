# Notes on [Codeforces - Carrots for Rabbits](https://codeforces.com/problemset/problem/1428/E)

### Introduction
We will not present the algorithm for solving the problem but focus the key
mathematical insights that allows the greedy approach to work.

### Setup
Let $f : \R \to \R$ be a strictly convex function, $n, m \in \N$ arbitrary and let
$L_1, L_2, \ldots, L_n \in \N$ be an arbitrary sequence of integers.
We are looking to for the miminum
$$ \mathcal{F} \equiv \mathcal{F}\big(n, m, L_1, L_2, \ldots, L_n \big) := \min_{l_1, \ldots, l_{n+m}} \sum_{i=1}^{n+m} f(l_i) $$
under constraints that $l_1, l_2, \ldots, l_{n+m} \in \N$ are such that
$$ \forall i \in \{1, 2, \ldots, n\} \quad \exists k, j_1, j_2, j_k \in \N
\quad L_i = l_{j_1} + l_{j_2} + \ldots + l_{j_k} $$

### Corrollary
Since there are finitely many choices of $l_1, l_2, \ldots, l_{n+m}$, the minimum is always achieved.

### Lemma 1:
Let $f$ be a strictly convex function, $L, m \in \N$ arbitrary.
Then $\mathcal{F}(1, m, L)$
is minimized for
$$l_1 = l_2 = \ldots = l_{m - r} = \left\lfloor \frac{L}{m} \right\rfloor
\quad l_{m - r + 1} = l_{m - r + 2} = \ldots = l_{m} = \left\lceil \frac{L}{m} \right\rceil$$
where $r$ is the remineder of dividing $L$ by $m$.

__Proof:__
Let $l_1', l_2', \ldots, l_{m}'$ be any sequence which minimizes $\mathcal{F}(1, m, L)$.
Let us show by contradiction that $ \vert l_i' - l_j' \vert \leq 1$ for all $i, j$.
Suppose there are $i, j$ such that $\vert l_i' - l_j' \vert \geq 2$. Without loss of generality we can assume $l_i' < l_j'$.
From strict convexity of $f$ (l_i' + 1 < l_j' - 1) we find that
$$f(l_i' + 1) - f(l_i')  < f(l_j') - f(l_j' - 1)$$
and therefore
$$f(l_i' + 1) + f(l_j' - 1) < f(l_i') + f(l_j').$$
But this would mean that replacing $l_i'$ with $l_i' + 1$ and $l_j'$ with $l_j' - 1$ would decrease the value of the sum,
contradicting the fact that $l_1', l_2', \ldots, l_{m}'$ minimizes it.
Therefore we must have $ \vert l_i' - l_j' \vert \leq 1$ for all $i, j$.
Since the average
$$\sum_{i=1}^m l_i' / m  = L / m$$
we must have
$$l_i' \in \left\{ \left\lfloor \frac{L}{m} \right\rfloor, \left\lceil \frac{L}{m} \right\rceil \right\}
\qquad \forall i \in {1, 2, \ldots, m}.$$
Now it is clear that exactly $r$ of the $l_i'$ must be equal to $\left\lceil \frac{L}{m} \right\rceil$ and the rest
must be equal to $\left\lfloor \frac{L}{m} \right\rfloor$. This completes the proof.


### Lemma 2:
Let $f$ be a strictly convex function, $L, m \in \N$ arbitrary.
Then
$$ \mathcal{F}(1, 2 m, 2 L) = 2 \mathcal{F}(1, m, L).$$

__Proof:__

Notice first that if $L = q + r$ then also $2 L = q (2 (m + 1)) + 2 r$.
Since previous lemma describes exactly the optimal choice of $l$-s that minimizes $\mathcal{F}$,
we find that
$$\mathcal{F}(1, 2, 2 L) = 2 (L - r) f\left(\left\lfloor \frac{L}{m} \right\rfloor\right) + 2r f\left(\left\lceil \frac{L}{m} \right\rceil\right)$$
and
$$\mathcal{F}(1, m, L) = (L - r) f\left(\left\lfloor \frac{L}{m} \right\rfloor\right) + r f\left(\left\lceil \frac{L}{m} \right\rceil\right)$$
leading to:
$$ \mathcal{F}(1, 2 m, 2 L) = 2 \mathcal{F}(1, m, L).$$
which completes the poof.

### Lemma 3:
Let $f$ be a strictly convex function, $L, m \in \N$ arbitrary.
Then
$$
\mathcal{F}(1, m, L) - \mathcal{F}(1, m + 1, L) \geq \mathcal{F}(1, m + 1, L) - \mathcal{F}(1, m + 2, L)
$$

__Proof:__
Applying the previous lemma for $m+1$ we have:
$$ \mathcal{F}(1, 2 (m + 1), 2 L) = 2 \mathcal{F}(1, m + 1, L)$$
Furthermore, let $ l_1, l_2, \ldots, l_{m}$ and $ l_1'', l_2'', \ldots, l_{m+2}''$ be the optimal choices of $l$-s for
$\mathcal{F}(1, m, L)$ and $\mathcal{F}(1, m + 2, L)$, respectively.
Then $l_1, l_2, \ldots, l_{m}, l_1'', l_2'', \ldots, l_{m+2}''$ is a
valid (although likely not optimal) choice of $l$-s for $\mathcal{F}(1, 2 (m + 1), 2 L)$. Hence
$$ \mathcal{F}(1, 2 m + 2, 2 L) \leq \sum_{i=1}^{m} f(l_i) + \sum_{i=1}^{m+2} f(l_i'') = \mathcal{F}(1, m, L) + \mathcal{F}(1, m + 2, L)$$
and consesquently (after combining with our previous finding)
$$ 2 \mathcal{F}(1, m + 1, L) \leq \mathcal{F}(1, m, L) + \mathcal{F}(1, m + 2, L)$$
which immediately leads to the desired inequality.
