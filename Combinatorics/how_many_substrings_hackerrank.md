# Complexity of [How many substrings](https://www.hackerrank.com/challenges/how-many-substrings/problem)


## Notions
Let:
* $\mathcal{A}$ be a countable alphabet
* $N \in \N$, $S = s_1 \ldots s_N \in \mathcal{A}$ a string of character
* $SA \equiv SA(S)$ the suffix array of $S$ and $LCP \equiv LCP(S)$ the corresponding longest common prefix array
* $lkp \equiv lkp(S)$ the lookup table from $S$ to $SA$ defined by $lkp[SA[k]] = k$

### Problem ([hackerrank.com - How many substrings](https://www.hackerrank.com/challenges/how-many-substrings/problem))
Given a string of characters $S$ of length $N$ and a list of $N$ queries consisting of a start index $s_k$ and an end index $e_k$, $0 \leq s_k < e_k \leq N$
construct an algorithm that counts the number of unique substrings in $S[s_k: e_k]$ for each $k$.
When $N = 10^5$ the algorithm is supposed to work in under approx. 2 seconds, i.e. is it allowed to make around $10^9$ operations.

_Note - it is likely that the desired complexity is slightly below $\mathcal{O}(N^{\frac{3}{2}} \log(N))$.
Whether the exponent lower than $\frac{3}{2}$ is required is unclear._

### Definition 1:
Let $i, j \in \N$, define
$\pi(i, j) = \min_{x \in [m, M]}LCP[x]$ where $m := \min(lkp[i], lkp[j])$ and $M := \max(lkp[i], lkp[j])$

### Corollary 1.1:
* $\pi(i, j) = \pi(j, i)$
* $\pi(i,j) \geq \min(\pi(i, k), \pi(j, k)) \quad \forall k$

### Definintion 2:
Let $i < k$ be arbitrary. $k$ is said to be distinguished for $i$, written $i \rightarrow k$, if
$$\pi(i, j) < \pi(i, k) \qquad \forall i < j < k$$
*Note that $i+1$ is always distinguished for $i$*

Moreover for $\alpha \in \N$, $k$ is said to be $\alpha$-distinguished for $i$, written $i \xrightarrow{\alpha} k$  if $k$ is distinguished for $i$ and there are exactly $\alpha - 1$ indices in the interval $(i, k)$ which are distinguished for $i$.
Clearly, $\alpha$-distinguished index for $i$ is unique if it exists. Let us denote it by $k_\alpha \equiv k_\alpha(i)$.

### Corollary 1.2:
For all $i$ and $\alpha$:
* $k_1(i) = i + 1$
* $\pi(k_\alpha(i), i) \geq \alpha - 1$

### Lemma 3:
Let $k$ be distinguished for $i$ and $j$, $i < j$. Then
1) $\pi(i, k) > \pi(j, k)$,
2) $\pi(i, j) = \pi(j, k)$

#### Proof:
Clearly $i < j < k$. Suppose the contrary, that $\pi(i,k) \leq \pi(j,k)$. Then $\pi(i,j) \geq \min(\pi(i, k), \pi(j, k)) \geq \pi(i, k)$. But this contradicts the fact that $k$ is distinguished for $i$.
This proves 1).\
For 2) it suffices to note that $\pi(i, j) = \pi(i, k) \wedge \pi(j, k) = \pi(j,k)$ directly from 1).

### Prop 4:
For any $i < j$ there is at most one $k$ which is distinguished for both $i$ and $j$.
#### Proof:
Suppose there are 2 such distinguished elements, $k_1$ and $k_2$.
By previous lemma, this would imply $\pi(j, k_1) = \pi(i, j) = \pi(j, k_2)$ which contradicts the definition of $j \to k_2$.

### Prop 5:
For arbitrary $i$ we have $k_\alpha - k_{\alpha - 1} > \alpha$.
#### Proof:
TODO

Algorithm 1:

    Input:
        1 < n, q < 10^5,
        string S of n character,
        list of queries Q = [(s_k, e_k) for k=1...q]

    Compute suffix_array SA and lowest_common prefix LCP of S

    Initialize reverse lookup lkp so that lkp[SA[k]] = k
    Initialize st_as as min segment tree from array of zeros of length n
    Initialize st_lcp as min segment_tree from array length n filled with value n

    Initialize fwt as Fenwick tree with size n filled with zeros.

    for l = n - 1 down to l = 0:
        update st_as[lkp[l]] = SA[lkp[l]]
        update st_lcp[lkp[l]] = 0

        r = n - 1
        while r > l:
            x = f(l, r)
            fwt.update_range(n - 1 - r, n - 1 - x - lcp.min(l, x), 1)
            r = x - 1

        for (l, j) in Q:
            store (n - 1 - l) * (n - 2 - l) / 2 - fwt(n - 1 - j)


Def 4:
$i, j$ share distinguished element, $i \leftrightarrow j$ if there is a $k$ which is distinguished for both $i$ and $j$.

Example 1: For the sequence
$$
\begin{matrix}
    a & x & x & a & b & y & a & x & a & b & a & x & x & a & b & y \\
    0 & 1 & 2 & 3 & 4 & 5 & 6 & 7 & 8 & 9 & 10 & 11 & 12 & 13 & 14 & 15 \\
\end{matrix}
$$
we have $1 \leftrightarrow 3$, $3 \leftrightarrow 10$, $10 \leftrightarrow 1$
