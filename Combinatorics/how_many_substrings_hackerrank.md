# Complexity of [How many substrings](https://www.hackerrank.com/challenges/how-many-substrings/problem)


## Notions
Let:
* $\mathcal{A}$ be a countable alphabet
* $N \in \N$, $S = s_1 \ldots s_N \in \mathcal{A}$ a string of character
* $SA \equiv SA(S)$ the suffix array of $S$ and $LCP \equiv LCP(S)$ the corresponding longest common prefix array
* $lkp \equiv lkp(S)$ the lookup table from $S$ to $SA$ defined by $lkp[SA[k]] = k$

### Problem (How many substrings) - ...

### Definition 1:
Let $i, j \in \N$, define
$\pi(i, j) = \min_{x \in [m, M]}LCP[x]$ where $m := \min(lkp[i], lkp[j])$ and $M := \max(lkp[i], lkp[j])$

### Korolar 1.1:
* $\pi(i, j) = \pi(j, i)$
* $\pi(i,j) \geq \min(\pi(i, k), \pi(j, k)) \quad \forall k $


### Definintion 2:
Let $i < j$ be arbitrary. Define $f(i, j)$ to be the **smallest** $k \in (i, j]$ such that
* $\pi(i, k) = max_{x} \pi(i, x)$

### Definition 3:
Let $i < k$ be arbitrary. $k$ is said to be distinguished for $i$ if $f(i, k) = k$

### Lemma 1:
Let $k$ be distinguished for $i$ and $j$, $i < j$. Then $\pi(i, k) > \pi(j, k)$.

#### Proof:
Suppose the contrary. Then there must be an $M > 0$ such that
$$S[i:i+M] = S[j:j+M] = S[k:k+M] \quad \text{and} \quad S[i + M] \neq S[k + M].$$
But then $\pi(i, k) = M$, and $\pi(i, j) = M$ contradicting the minimality of $k$ from [definition](#definintion-2)


### Prop 1:
Let $i < j$ be arbitrary. There is at most one index which is distinguished for both $i$ and $j$.

#### Proof:
Suppose there are $k_1$ and $k_2$ which are both distinguished for $i$ and for $j$.
Without the loss of generality we can assume $i < j < k_1 < k_2$.
By [lemma 1](#lemma-1) we have $\pi(j, k_2) < \pi(i, k_2)$ and consequently $\pi(i, j) \geq \pi(j, k_2)$.
Furthermore, minimality of $k_2$ gives $\pi(j, k_1) < \pi(j, k_2)$ and [lemma 1](#lemma-1) once again
shows $\pi(i, k_1) > \pi(j, k_1)$.
But then
$$\pi(j, k_1) \geq \pi(i,j) \wedge \pi(i, k_1) \geq \pi(j, k_2) \wedge \pi(i, k_1) > \pi(j, k_1)$$
leading to a contradiction.


Algorithm 1:

    Input - n, q natural numbers, string S of n character, list of queries Q = [(s_k, e_k) for k=1...q]

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
