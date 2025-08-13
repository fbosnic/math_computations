# Complexity of [How many substrings](https://www.hackerrank.com/challenges/how-many-substrings/problem)

### Setup
Let:
* $\mathcal{A}$ be a countable alphabet
* $N \in \N$, $S = c_1 \ldots c_N \in \mathcal{A}$ a string of characters
* $SA \equiv SA(S)$ the suffix array of $S$ and $LCP \equiv LCP(S)$ the corresponding longest common prefix array
* $lkp \equiv lkp(S)$ the lookup table from $S$ to $SA$ defined by $lkp[SA[k]] = k$


### Definition 0.1
A suffix array $SA$ of $S$ is the array of alphabetically sorted suffixes of $S$.
More precisely, the elements of the $SA$ are integers from $0$ to $\textnormal{len}(S) - 1$
such that value $SA[i] = x$ corresponds to suffix $S[x:]$.
To be specific, let us assume that suffixes are sorted in the ascending order.

### Definition 0.2
A largest common prefix array (LCP-array) of string $S$ together with a suffix array $SA$
is an interger array of same length such that LCP-array at index $i \geq 1$ contains the lengths of the
common prefix of $(i-1)$-th and $i$-th sorted suffix. The value of the LCP-array at index $0$ is defined
to be $0$ but holds no information and can only be used if it is convenient for certain formulas.

### Definition 0.3
Let $I$ be an integer array of lenght $n$. A min-segment tree is a complete binary tree of length
$\lceil \log n \rceil$ such that a leaf node is assigned to each index of $i$.
We will often identify indices $i$ with corresponding nodes of the segment tree.
For nodes $N$ and $M$ we denote the statemnt that $N$ is a descendant of $M$ by $N \preccurlyeq M$.\
Additionally we denote by $N \lll M$ the statement that "$P$ is right of $N$", formally defined as: there being some $P, L, R$
such that $L$ is a left child of $P$, $R$ is the right child of $P$, $N \preccurlyeq L$, $M \preccurlyeq R$.\
Moreover the min segment tree assigns a value $v(N)$ to each of its nodes $N$ so that:
- For every node $N$ we have $v(N) = \min_{i \preccurlyeq N} I(i)$
- Let $P$ be a node with left child $L$ and right child $R$ and suppose $i \preccurlyeq L$, $j \preccurlyeq R$ then $i \leq j$
- If for a leaf node $L$ we have $L \lll n-1$ then there exists some index $i$ such that $L$ is the node of that index ( the
    segment tree is allowed to have additional leaf nodes)
Moreover, the length of the segment tree is defined to be the length of the underlying array. Note that this
is not always equal to the number of leaves of the segment tree.

### Definition 0.4:
A Fenwick-tree-with-ranged-updated (FWT with ranged updates) of $n$ elements is an array $\mathcal{F}$ of $n$
with additional structure so that the following operatorions can be performed efficiently:
1) $\sum_{j=0}^{k} \mathcal{F}(j)$ can be computed in $\mathcal{O}(\log n)$ operations
2) For every $0 \leq s, e < n$ and $v \in \R$, the update
    $$\mathcal{F}'(j) = \mathcal{F}(j) + v \quad \forall j \in [s, e]$$
    can be performed in $\mathcal{O}(\log n)$ operations.

### Problem ([hackerrank.com - How many substrings](https://www.hackerrank.com/challenges/how-many-substrings/problem))
Given a string of characters $S$ of length $N$ and a list of $N$ queries consisting of a start index $s_k$ and an end index $e_k$, $0 \leq s_k < e_k \leq N$
construct an algorithm that counts the number of unique substrings in $S[s_k: e_k]$ for each $k$.
When $N = 10^5$ the algorithm is supposed to work in under approx. 2 seconds, i.e. is it allowed to make around $10^9$ operations.

_Note - it is likely that the desired complexity is slightly below $\mathcal{O}(N^{\frac{3}{2}} \log(N))$.
Whether an exponent lower than $\frac{3}{2}$ is required remains unclear._

### Definition 1:
Let $i, j \in \N$, define $\pi(i, j)$ to be the length of the common prefix of $S[i:]$ and $S[j:]$.\
That is, $\pi(i, j) = \min_{m < x \leq M}LCP[x]$ where $m := \min(lkp[i], lkp[j])$ and $M := \max(lkp[i], lkp[j])$

### Corollary 1.1:
* $\pi(i, j) = \pi(j, i)$
* $\pi(i,j) \geq \min(\pi(i, k), \pi(j, k)) \quad \forall k$

### Lemma 1.2:
For any $i$, $j$ and $k$ if $\pi(i, j) > \pi(i, k)$ then $\pi(i, k) = \pi(j, k)$.

#### Proof:
Note that $\pi(i, j) > \pi(i, k) \geq \pi(i, j) \wedge \pi(j, k)$ and we must have $\pi(i, k) \geq \pi(j, k)$. On the other hand, $\pi(j, k) \geq \pi(i, j) \wedge \pi(i, k) = \pi(i,k)$ and hence $\pi(i, k) = \pi(j, k)$.

### Definintion 2:
Let $i < k$ be arbitrary. $k$ is said to be distinguished for $i$, written $i \rightarrow k$, if
$$\pi(i, j) < \pi(i, k) \qquad \forall i < j < k$$
*Note that $i+1$ is always distinguished for $i$*

Moreover for $\alpha \in \N_{0}$, $k$ is said to be $\alpha$-distinguished for $i$, written $i \xrightarrow{\alpha} k$
if $k$ is distinguished for $i$ and there are exactly $\alpha$ indices in the interval $(i, k)$
which are distinguished for $i$.
Clearly, $\alpha$-distinguished index for $i$ is unique if it exists. Let us denote it by $k_\alpha(i)$.

### Corollary 1.2:
For all $i$ and $\alpha$:
* $k_0(i) = i + 1$ (unless $i = \textnormal{len}(S)$)
* $\pi(k_\alpha(i), i) \geq \alpha$

### Lemma 3:
Let $k$ be distinguished for $i$ and $j$, $i < j$. Then
1) $\pi(i, k) > \pi(j, k)$,
2) $\pi(i, j) = \pi(j, k)$

#### Proof:
Clearly $i < j < k$. If we suppose that $\pi(i,k) \leq \pi(j,k)$, then $\pi(i,j) \geq \min(\pi(i, k), \pi(j, k)) \geq \pi(i, k)$. But this contradicts the fact that $k$ is distinguished for $i$ which proves 1).\
2) follows immediately from one of the previous lemmas.

## Side-note

### Prop 4:
For any $i < j$ there is at most one $k$ which is distinguished for both $i$ and $j$.
#### Proof:
Suppose there are 2 such distinguished elements, $k^1 < k^2$.
By previous lemma, this would imply $\pi(j, k^1) = \pi(i, j) = \pi(j, k^2)$ which contradicts the definition of $j \to k^2$.

### Note
It is possible to have triangles of indices such that each two have a distinguished element. The following example shows this.
Similar cycles with 4, 5 or more elements can also be constructed.

### Def 4.1:
$i, j$ share distinguished element, $i \leftrightarrow j$ if there is a $k$ which is distinguished for both $i$ and $j$.

### Example 4.2:
For the sequence
$$
\begin{matrix}
    a & x & x & a & b & y & a & x & a & b & a & x & x & a & b & y \\
    0 & 1 & 2 & 3 & 4 & 5 & 6 & 7 & 8 & 9 & 10 & 11 & 12 & 13 & 14 & 15 \\
\end{matrix}
$$
we have $1 \leftrightarrow 3$, $3 \leftrightarrow 10$, $10 \leftrightarrow 1$

### Note
The fact that each two indices share at most one distinguished element is a heavy constraint on the total number
of distinguished elements in string $S$. But it should be possible to construct an example containing
$\mathcal{O}(n^{3/2})$ distinguished elements. A indication of this comes from the fact that for a prime $p$
and $n = p^2$ is is possible to construct a set $\mathcal{A}$ of $p^3$ pairs $(x, y)$ such that
$$ \vert \{ (x, y) \in \mathcal{A}: x = x_0 \} \vert \leq 2.$$
This is constructed by looking at the set of all lines in the field $\mathbb{F}_p$ and encoding their graphs
as $p^2$ $0-1$ arrays and stacking them in a matrix. The fact that each two lines have exactly one intersection
point is equivalent to our initial condition.

I supsect that $\mathcal{O}(n^{3/2})$ is in fact sharp estimate in this case, but have no idea how to prove it.

## End-of-side-note

### Def 5.0:
A finite sequence $S$ of length $L$ is said to be $p$-periodic if
$$S[0:L-p] = S[p:L] $$

### Corolary 5.1:
If a finite sequence $S$ of length $L$ is $p$-periodic then every prefix of $S$ is also $p$ periodic. That is,
$$ S[0: l-p] = S[p: l] \quad \forall p < l < L $$

### Definition 5.2
We use $+$ to denote concatenation of two strings $A + B$.\
Conatenation of string $S$ with itself $n$-times is denoted by multiplication $n S$:
$$nS = \underbrace{S + S + \ldots + S}_{n-\textnormal{times}}$$

### Corolary 5.3:
If a finite sequence $S$ of length $L$ is $p$-periodic and $L = q p + r$ for some $q, r \in \N_0$
from division with reminder theorem, then
$$ S = qS[0:p] + S[0:r]$$
In particular, $S[0:np] = nS[0:p]$ for every $n \in \N_0$, $n \leq L/p$.

#### Proof:
Let $0 \leq x \leq L$ be arbitrary and $x = q' p + r'$ (again by division with reminder).
By applying $p$-periodicity of $S$ $q'$ times we have
$$S[x] = S[x - p] = S[x - 2p] = \ldots = S[x - q'p] = S[r']$$
On the other hand, the $x$-th element of the string on the right hand side is
$$(qS[0:p] + S[0:r])[x] = S[r']$$
which completes the proof. The second statment is a particular case.

### Lemma 5.4
Let $S$ of length $L$ be a sequence that is both $p$- and $r$-periodic for arbitrary $p < r$ such that $L > p + r$.
Let $q$ be the reminder of dividing $r$ with $p$ and assume $q \neq 0$.
Then $S[0:L-r+q]$ is $q$-periodic.

#### Proof
Let $x \in \N$ be such that $r = xp + q$.
We apply $p$-periodicity $x$ times to get $S[0: L - xp] = S[xp: L]$.
Looking at the substring $[q:]$ of both sides leads to $S[q: L-xp] = S[r: L]$ but this is equal to $S[0: L - r]$
by $r$-periodicity. Since $L - r = L - xp - q$ we now have:
$$ S[q: L - r + q] = S[0: L - r] $$
which is $q$-periodicity of substring $S[0:L - r + q]$ and the proof is complete.

### Lemma 5.5:
Let $S$ of length $L$ be a sequence that is both $p$-periodic and $r$-periodic, $p \neq r$.
Let also $d := \textnormal{gcd}(p, r)$ be the greatest common divisor of $p$ and $r$. \
If $L > r + p$ then $S[0:L - p - r + d]$ is also $d$-periodic.

#### Proof:
Suppose, without the loss of generality, that $p < r$. We'll follow the Euclidean algorithm.
Let us denote $p_1 := p$, $r_1 := r$, $L_1 := L$ and let $r_2$, $0 \leq r_2 < r_1$ be the reminder
of dividing $r_1$ by $p_1$. Let us also assume that $r_2 \neq 0$ and deal with this case later.
By previous lemma, we find that $S[L_1 - r_1 + r_2]$ is $r_2$-periodic.
Note also that $\textnormal{gcd}(p_1, r_2) = \textnormal{gcd}(p_1, r_1) = d$ by euclidean algorithm. \
Let $p_2$ now be the reminder of dividing $p_1$ with $r_2$ and assume again that $p_2 \neq 0$.
Previous lemma with $r_2, p_1, L_1 - r_1 + r_2$ in place of $p, r, L$
now tells us that $S[0: L_1 - r_1 - p_1 + r_2 + p_2]$ is $p_2$-periodic
(note that the requirement $L_1 - r_1 + r_2 > p_1 + r_2$ is equivalent to the initial assumption $L > p + r$).
Again, we also have: $\textnormal{gcd}(p_2, r_2) = \textnormal{gcd}(p_1, r_2) = \textnormal{gcd}(p_1, r_1) = d$. \
We are now in exactly the same setting as at the beginning of the proof with $p_1$, $r_1$ and $L_1$ replaced by
$p_2$, $r_2$ and $L_2 := L_1 - p_1 - r_1 + p_2 + r_2$.
The procedure can be repeated to get sequences $p_1 > p_2 > p_3 > \ldots \geq 0$, $r_1 > r_2 > r_3 > \ldots \geq 0$
and $L_1 > L_2 > L_3 > \ldots \geq 0$ until either $p_{k+1}=0$ or $r_{k+1} = 0$ for some $k \in \N$,
which must happen eventually since these sequences are strictly decreasing. Notice that this covers the
casese $r_2 = 0$ and $p_2 = 0$ which were skipped in the initial part of the proof. \
So far we have proved that $S[0: L_k]$ will be both $p_k$- and $r_k$-periodic,
$\textnormal{gcd}(p_k, r_k) = d$ and
$$ L_k = L - p - r + p_k + r_k $$
where the last two facts follow from telescoping or by induction. \
Assume first that $r_{k+1} = 0$. But in that case $p_k$ divides $r_k$ and hence $d = \textnormal{gcd}(p_k, r_k) = p_k$.
By substituting $d = p_k$ we see that that $S[0:L_k]$ is $d$-periodic with $L_k > L - p - r + d$ which is
exactly the statement of the lemma. \
Alternatively, suppose that $r_{k+1} > 0$ but $p_{k+1} = 0$. Using the previous lemma one more time, we find that
$S[0: L_k - r_k + r_{k+1}]$ is $r_{k+1}$-periodic.
Since $p_{k+1} = 0$, $r_{k+1}$ divides $p_k$ and hence $\textnormal{gcd}(p_k, r_{k+1}) = r_{k+1}$.
By euclidean algorithm we find that
$r_{k+1} = \textnormal{gcd}(p_k, r_{k+1}) = \textnormal{gcd}(p_k, r_k) = \textnormal{gcd}(p, r) = d$
which proves the statement in this case as well, since
$L_k - r_k + r_{k+1} = L - p - r + p_k + r_{k+1} > L - p - r + d$.

### Lemma 5.6:
Let $i$ be arbitrary and let $\alpha, \beta \in N$ be such that $\alpha < \beta$.
If $k_\beta - k_\alpha < \alpha$ then $S[i:i + \pi(k_\alpha, i)]$ is $(k_\beta - k_\alpha)$-periodic.

#### Proof
By definition of distinguished element $k_\beta$ (note that $\pi(k_\beta,i) > \pi(k_\alpha, i)$) we compute
$$ S[i: i + \pi(k_\alpha, i) - (k_\beta - k_\alpha)] = S[k_\beta: k_\beta + \pi(k_\alpha,i) - (k_\beta - k_\alpha)] =
S[k_\beta: k_\alpha + \pi(k_\alpha, i)]$$
Morover, by definition of $k_\alpha$ we now find:
$$ \ldots = S[k_\alpha + (k_\beta - k_\alpha): k_\alpha + \pi(k_\alpha, i)]
= S[i + (k_\beta - k_\alpha): i + \pi(k_\alpha, i)] $$
which proves $S[i: i + \pi(k_\alpha, i)]$ is $(k_\beta - k_\alpha)$-periodic.

### Theorem 5.7:
For arbitrary $i$ and $\alpha$ we have $k_{2\alpha + 2} (i) - k_{2\alpha} (i) \geq \alpha$,
provided that $k_{2\alpha + 2}$ exists.

#### Proof:
Define $p := k_{2\alpha + 1} - k_{2\alpha}$ and $r := k_{2\alpha + 2} - k_{2\alpha + 1}$
and denote $d := \textnormal{gcd}(p, r)$.
We argue by contradiction and assume that $p + r = k_{2\alpha + 2} - k_{2\alpha} < \alpha$. \
Applying the previous lemma two times, we find that $S[i: i + \pi(k_{2\alpha}, i)]$ is both $p$- and $r$-periodic.
Since $\pi(k_{2\alpha}, i) - p - r \geq 2\alpha - p + r > \alpha$, by second to last lemma we find that
$S[i: \alpha + d]$ is $d$-periodic and so are
$S[k_{2\alpha}: k_{2\alpha} + \alpha + d]$, $S[k_{2\alpha + 1}: k_{2\alpha + 1} + \alpha + d]$
and $S[k_{2\alpha + 2}: k_{2\alpha + 2} + \alpha + d]$. \
Furthermore, let us denot denote $R := S[i: i + d]$.
As $p$ and $r$ are both smaller than $\alpha + d$ and divisible by $d$,
one of the previous corollaries shows that
$$S[k_{2\alpha}: k_{2\alpha + 1}] = S[i: i + p] = \frac{p}{d} R \quad \textnormal{ and }
 \quad S[k_{2\alpha + 1}: k_{2\alpha + 2}] = S[i: i + r] = \frac{r}{d} R$$
Now, by previous lemma, we also know that $S[k_2: k_2 + \pi(k_2, i)]$ is $r$-periodic
and hence that
$$S[k_{2\alpha + 1}: k_{2\alpha + 1} + \pi(k_{2\alpha + 1}, i)] =
a'S[k_{2\alpha +1}: k_{2\alpha + 1} + r] + S[k_{2\alpha +1}:k_{2\alpha + 1} + b']$$
for $a'$ and $b'$ such that $\pi(k_{\alpha +1}, i) = a' r + b'$. \
But then by definition of $k_{2\alpha + 1}$ as distinct element for $i$ we have
$$S[k_{2\alpha + 1}: k_{2\alpha + 1} + \pi(k_{2\alpha + 1}, i)] = a'S[i: i + r] + S[i:i + b']$$
Moreover, combining previous findings we compute that
$$S[k_{2\alpha}: k_{2\alpha + 1} + \pi(k_{2\alpha + 1}, i)] = S[k_{2\alpha}: k_{2\alpha + 1}]
+ S[k_{2\alpha + 1}: k_{2\alpha + 1} + \pi(k_{2\alpha + 1}, i)] =
\frac{p}{d} R + a'S[i: i + r] + S[i:i + b']
$$
and, together with another decomposition $b' = a'' d + b''$, we find
$$ \ldots = \frac{p}{d} R + \frac{a'r}{d} R + a'' R  + R[0:b''].$$
We are only interested in the fact that there are $a, b \in \N_0$ such that
$$S[k_{2\alpha}: k_{2\alpha + 1} + \pi(k_{2\alpha + 1}, i)] = a R + R[0: b].$$
Since $d$ (the length of $R$) divides $k_{2\alpha + 1} - k_{2\alpha}$, from this equation we can read of that
$$S[k_{2\alpha}: k_{2\alpha} + \pi(k_{2\alpha + 1}, i)] = S[k_{2\alpha + 1}: k_{2\alpha + 1} + \pi(k_{2\alpha + 1}, i)] $$
which implies $\pi(k_{2\alpha}, i) \geq \pi(k_{2\alpha + 1}, i)$, contradicts the definition of $k_{2\alpha + 1}$
and completes the proof.


### Theorem 5.8:
Let $L$ be the lenght of string $S$. For any $0 \leq i < L$ there are strictly fewer than
$\sqrt{8(L-i)}$ elements which are distinguished for $i$.

#### Proof:
Let $L$ denote the length of string $S$. Let $\beta \in \N_0$ be the largest even number such
that $k_\beta$ is distinguished for $i$. Let us also assume $\beta > 2$ and write $\beta = 2\alpha + 1$.
From definition of $k_{\beta}$ we know that $\pi(k_\beta, i) \geq \alpha$ so that
$$k_{\beta} + \beta \leq L $$
Combining this with the previous theorem leads to:
$$ L - (2\alpha + 2)  - i \geq k_{2\alpha + 2} - i = (k_{2\alpha + 2} - k_{2\alpha}) + (k_{2\alpha} - i)
\geq \alpha + (k_{2(\alpha - 1)} - i)$$
By telescoping we find that the right side is
$$ ... = \ldots \alpha + (\alpha - 1) + (\alpha - 2) + \ldots + (k_{0} - i) = \frac{(\alpha + 1)\alpha}{2} + 1$$
From here it follows that
$$ L - i \geq \frac{\alpha^2 + 5 \alpha + 6}{2} > \frac{(2\alpha + 4)^2}{8}$$
And therefore
$$ \beta + 1 < 2\alpha + 4 < \sqrt{8(L-i)} $$
Recall that we assumed $\beta > 1$ for this computation but since $L - i \geq 1$ the inequality is clearly true
in that case as well.
Furthermore, there could be at most one more distinguished element $k_{\beta + 1}$ for $i$ so the total number
of $i$-distinguished elements is bounded by $\sqrt{8(L-i)}$.
## Algorithmic solution

### Algorithm
```
def main
    Input:
        1 <= n, q <= 10^5,
        string S of n character,
        list of queries Q = [(s_k, e_k) for k=1...q]
    Output:
        list of n ints - number of different substrings of S in range s_k: e_k (right bound excluded)

    SA, LCP = compute_SA_and_LCP(S)
    lkp = compute_reverse_lookup(SA)
    fwk = empty_fw_tree_with_ranged_updates(n)

    sa_seg_tree = create_simple_segment_tree(
        num_elements=n,
        fill_value=n,
        type="min"
    )
    LCP_seg_tree = convert_into_segment_tree(
        underlying_array=LCP,
        type="min"
    )
    Q, reverse_sort_fn = Q.sort_by_start_indices("descending")
    result = []

    for i = n - 1 down to i = 0:
        pos = lkp[l]

        k_0 < k_1 < ... < k_r = find_distinguished_elements(
            i=i,
            LCP_segment_tree=LCP_seg_tree,
            sa_seg_tree=sa_seg_tree,
            sa_lookup=lkp
        )
        fwt.update_range(start=i, end=i+1, value=1)
        for l=0 up to r-1:
            _progressive_lcp = LCP_seg_tree.min(pos, lkp[k_l])
            fwt.update_range(
                start=k_l + _progressive_lcp,
                end=k_{l+1} + _progressive_lcp,
                value=1
            )
        fwt.update_range(
            start=k_r + LCP_seg_tree.min(pos, lkp[k_r]),
            end=n,
            value=1
        )
        if Q.top().start() == i:
            results.append(fwt.ranged_sum(i, Q.top().end()))
            Q.pop()
        sa_seg_tree.update(pos, i)
    results = reverse_sort_fn(results)
    return results

def update_range:
    Input:
        Fenwick tree fwt
        start - first index of range to update (included)
        end - last index of the range to update (excluded)
        value - the value to update with
    Output:
        updated Fenwick tree fwt

def find_distingiushed_elements:    # Returns distinguished elements for a specific index
    Input:
        i                           # suffix index for which distinguished elements are computed
        LCP_seg_tree                # min segment tree on the LCP array with first element excluded
        sa_seg_tree                 # min segment tree on the partial suffix array. The suffix array
                                    #   must not contain suffixes starting at index <= i. Instead,
                                    #   those places need to be filled with value len(sa_seg_tree)
        sa_lookup                   # inverse lookup for suffix array
    Output:
        Inreasing list k_0 < k_1 < ... < k_r     # distinguished suffix indices for i (i < k_0).
                                                # Empty if i = len(sa_seg_tree)
    if i  = len(sa_seg_tree):
        return []
    pos = sa_lookup[i]
    dist_elem = empty_list()
    r = 0

    lcp_depth = 0
    while True:
        left = find_left_limit(
            LCP_seg_tree,
            start=pos,
            value=lcp_depth
        )
        right = find_right_limit(
            LCP_seg_tree,
            start=pos,
            value=lcp_depth
        )
        if left == right:
            break
        k = sa_seg_tree.min_element(left, right)
        dist_elem.append(k)
        a = min(pos, k)
        b = max(pos, k)
        lcp_depth = LCP_seg_tree.min(a, b) + 1

    return dist_elem


def find_left_limit:  # finds the left-most index j such that
                      # min_seg_tree[x] \geq alpha for all j < x <= start
    Input:
        min_seg_tree  # "min"-segment tree over an lcp array with first element excluded
        start         # element to start the search from
        alpha         # an arbitrary bound
    Output:           # the desired index j
    if start == 0:
        return 0
    if min_segment_tree[start] < alpha:
        return start
    node = min_seg_tree.get_leaf_by_index(start)
    while node != root and (node.is_left_child() or node.parent.left_child().value() >= alpha):
        node = node.parent()
    if node == root:
        return 0
    node = node.parent().left_child()

    while not node.is_leaf():
        if node.right_child().value() < value:
            node = node.right_child()
        else:
            node = node.left_child()
    return = node.index() + 1


def find_right_limit: # finds the right-most index j such that
                      # min_seg_tree[x] \geq alpha for all start < x <= j
    Input:
        min_seg_tree  # "min"-segment tree over an lcp array with first element excluded
        start         # element to start the search from
        alpha         # an arbitrary bound
    Output:           # the desired index j
    if start == min_seg_tree.len():  # Not that the min_seg_tree has one element less than the array
        return start
    if  min_seg_tree[start + 1] < alpha:
        return start
    node = min_seg_tree.get_leaf_by_index(start + 1)
    while node != root and (node.is_right_child() or node.parent().right_child().value() >= alpha):
        node = node.parent()
    if node == root:
        return min_segment_tree.len()  # note - min_seg_tree has one element less than the array

    node = node.parent.right_child()
    while not node.is_leaf():
        if node.left_child.value() < value:
            node = node.left_child()
        else:
            node = node.right_child()
    return = node.index() - 1
```

### Theorem 7.1
Let $\mathcal{A}$ be an LCP-array of length $n$ with is a min-segment tree structure on $\mathcal{A}[1:]$.
(Because the value of $LCP-array at index 0 is undefined).
Let also $i$ be an arbitrary index on $\mathcal{A}$ and $\alpha \in \R$ an arbitrary value.
For input ($\mathcal{A}$, $i$, $\alpha$) the funciton `find_left_limit` works as intended - it
returns the smallest $0 \leq j \leq i$ such that $\mathcal{A}[x] \geq \alpha$ for every $j < x \leq i$. \
Moreover computing `find_left_limit` has complexity $\mathcal{O} (\log n)$

#### Proof:
Note that $j$ is well defined becasue the set
$$ \mathcal{M} := \{l \leq i: \mathcal{A}[x] \geq \alpha \quad \forall l < x \leq i\} $$
contains $l=i$ (the condition is trivially true) so it must have a unique mimimum.\
First of all, we handle the trivial cases.
If $i = 0$ then the function returns $j=0$ which trivially satisfies the requrements.
Next, if $\mathcal{A}[i] < \alpha$ then clearly $\mathcal{M} = \{i\}$ and therefore $j=i$ so
the $i$ is the correct return value.\
Let us assume $i > 0$ and $\mathcal{A}[i] \geq \alpha$ from now on.
Observe that the second assumption implies $j \leq i-1$.
Note that the first while loop travels the ancestors of $i$ from $i$ to the root.\
If $j = 0$ (note that the value of LCP at 0 is undefined) then $\mathcal{A}[x] \geq \alpha$ for all $0 < x \leq i$.
Since the segment tree is defined on $\mathcal{A}[1:]$ (with first element excluded)
this means that for every $P, L, R$ such that $i \preccurlyeq R$ we
have $\mathcal{A}[L] \geq \alpha$. Hence the
loop will only terminate at root. An the algorithm will return 0 which is $j$ by assumption. \
In case, $j > 0$, we need to have $\mathcal{A}[j] < \alpha $ since otherwise $j-1 \in \mathcal{M}$
which is impossible as $j = \min \mathcal{M}$. Let $P$ the first
common ancestor of both $i$ and $j$. Since $j \leq i - 1$, $P$ must be a proper node, $P \neq i$.
If $L$ and $R$ are left and right children of $P$ then we must have $j \preccurlyeq L$ and $i \preccurlyeq R$.
But then $\mathcal{A}[L] \leq \mathcal{A}[j] < \alpha$ so the loop terminates at $R$ (or before $R$).
If the loop would terminate before $R$ there would be $P' \preccurlyeq R$, $L'$, $R'$ such that
$\mathcal{A}[L'] < \alpha$, $i \preccurlyeq R'$. But then $j \lll L' \lll i$ so, from definition of $j$,
for all $x \in L'$ we have $j < x \leq i$ and consequently $\mathcal{A}[x] \geq \alpha$.
This leads to $\mathcal{A}[L'] \geq \alpha$, a contradiction.
Therefore, the first loop terminates exactly at $R$. \
The algorithm then switches from $R$ to $L$ and the second loop travels from $L$ towards leaves.
Clearly it will end up in some leaf node $N \lll R$ and consequently $N \lll i$. But this means that $N$ is a proper
node, i.e. corresponding to some $k \leq i$.
Let $N_1 = L, N_2 \ldots N=k$ be the sequence of nodes produced in the second loop. This must be an ancestor line from
$R$ to $k$.
Suppose that $k \neq j$ and let $P'$ be the common ancestor of $j$ and $k$. Since $P'$ is an ancestor of $k$ it must have
been visited during traversal of the second loop hence $P' = N_\phi$, for some $\phi$.
There are two cases. If $j \leq k$ then $j \preccurlyeq L'$, $k \preccurlyeq R'$,  $j \lll R \lll i$ so
$\mathcal{A}[R] \geq \alpha$. But then the loop would decide $N_{\phi + 1} = L$ wich is a contradiction since
$L$ is not a ancestor of $k$.\
On the other hand, if $k \lll j$ then $k \preccurlyeq L'$, $j \preccurlyeq R'$. But then
$\mathcal{A}[R] \leq \mathcal{A}[j] < \alpha$ so the loop would choose $N_{\phi + 1} = R$ which is again a contradiction
with the fact that we assumed $N_{\phi + 1}$ is an ancestor of k.

As for the compexity estimate. It is clear that both loops repeat at most $\lceil \log n \rceil$ (which is depth
of the segment tree). Assuming that `is_left_child` takes 2 operations in each step of the first loop we perform
at most $1 + 2 + 4 + 1 = 8$ operations, and in the second loop we perform $1 + 3 + 1 = 5$ operations. Hence we perform
under $13 \lceil \log n \rceil + 3$ opertions (some operations are not loop related).
In any case, the complexity is $\mathcal{O}(\log n)$

### Theorem 7.2
Let $\mathcal{A}$ be an LCP-array of length $n$ with is a min-segment tree structure on $\mathcal{A}[1:]$.
Let also $i$ be an arbitrary index on $\mathcal{A}$ and $\alpha \in \R$ an arbitrary value.
For input ($\mathcal{A}$, $i$, $\alpha$) the funciton `find_right_limit` works as intended - it
returns the largest $i \leq j < n$ such that $\mathcal{A}[x] \geq \alpha$ for every $i < x \leq j$. \
Moreover computing `find_right_limit` has complexity $\mathcal{O} (\log n)$

#### Proof:
Note that $j$ is well defined becasue the set
$$ \mathcal{M} := \{l \geq i: \mathcal{A}[x] \geq \alpha \quad \forall i < x \leq l\} $$
contains $l=i$ (the condition is trivially true) so it must have a unique maximum.\
We handle the trivial cases first; if $i$ is equal to the length of the min segment tree
then $i = \textnormal{len}(\mathcal{A}) - 1$ (since the min segment tree ignores the first element) so
there can be no elements other than $i$ in $\mathcal{M}$. The algorithm returns $i$ as expected.
Next, if $\mathcal{A}[i + 1] < \alpha$ (note that $i+1$ is now a valid index) then again
$\mathcal{M} = \{i\}$ and therefore $j=i$ and the algorithm is again correct.\
Let us assume $i < \textnormal{len}(\mathcal{A}) - 1$ and $\mathcal{A}[i + 1] \geq \alpha$ from now on.
Observe that the second assumption implies $j \geq i+1$. \
The first while loop travels the ancestors of $i + 1$ from $i + 1$ to the root.\
If $j = \textnormal{len}(\mathcal{A}) - 1$ then
$\mathcal{A}[x] \geq \alpha$ for all $i < x \leq \textnormal{len}(\mathcal{A}) - 1$.
This means that for every $P, L, R$ such that $i \preccurlyeq L$ we
have $\mathcal{A}[R] \geq \alpha$. Hence the
loop will only terminate at root and the algorithm will return $\textnormal{len}(\mathcal{A}) - 1$
which is $j$ by assumption. \
In case $j < \textnormal{len}(\mathcal{A}) - 1$, we need to have $\mathcal{A}[j+1] < \alpha $
since otherwise $j+1 \in \mathcal{M}$ which contradicts $j = \max \mathcal{M}$.
Let $P$ the first common ancestor of both $i+1$ and $j+1$.
Since $j \geq i + 1$, $P$ must be a non-leaf node, $P \neq i$.
If $L$ and $R$ are left and right children of $P$ then we must have $i + 1 \preccurlyeq L$ and $j + 1 \preccurlyeq R$.
But then $\mathcal{A}[R] \leq \mathcal{A}[j+1] < \alpha$ so the loop terminates at $L$ (or before $L$).
Supposing that the loop terminates before $L$ there would be $P' \preccurlyeq L$ and $L'$, $R'$ such that
$\mathcal{A}[R'] < \alpha$, $i + 1 \preccurlyeq L'$. But then $i + 1 \lll R' \lll j + 1$ so, from definition of $j$,
for all $x \in R'$ we have $i < x \leq j$ and consequently $\mathcal{A}[x] \geq \alpha$.
This leads to $\mathcal{A}[R'] \geq \alpha$, a contradiction.
Therefore, the first loop terminates exactly at $L$. \
The algorithm then switches from $L$ to $R$ and the second loop travels from $R$ towards leaves.
Clearly it will end up in some leaf node $N$.
Let $N_1 = L, N_2 \ldots N$ be the sequence of nodes produced in the second loop. This must be an ancestor line from
$R$ to $N$.
Suppose that $N \neq j + 1$ and let $P'$ be the common ancestor of $j + 1$ and $N$. Since $P'$ is an ancestor of $N$ it must have
been visited during traversal of the second loop hence $P' = N_\phi$, for some $\phi$.
Both $j + 1$ and $N$ are leaf nodes and we assumed $j + 1 \neq N$ so there are two possible cases.
First, if $j + 1 \lll N$ then $j + 1 \preccurlyeq L'$, $N \preccurlyeq R'$, then we know
$\mathcal{A}[L'] \leq \mathcal{A}[j+1] < \alpha$ so the loop would choose $N_{\phi + 1} = L$ wich is a contradiction
as $N_{\phi + 1}$ is not an ancestor of k.
On the other hand, if $N \lll j + 1$ then $N \preccurlyeq L'$, $j + 1 \preccurlyeq R'$. But then
$$\mathcal{A}[L'] = \min_{x \in N} \mathcal{A}[x] \geq \min_{i < x \leq j} \mathcal{A}[x] \geq \alpha$$
by definition of $j$. Hence the loop would choose $N_{\phi + 1} = R$ which again contradicts the fact that
$N_{\phi + 1}$ is an ancestor of k. \
Hence $N = j + 1$ and the algorithm returns $j + 1 - 1 = j$, just as expected.

As for the compexity estimate. It is clear that both loops repeat at most $\lceil \log n \rceil$ (which is depth
of the segment tree). Assuming that `is_left_right` takes 2 operations in each step of the first loop we perform
at most $1 + 2 + 4 + 1 = 8$ operations, and in the second loop we perform $1 + 3 + 1 = 5$ operations. Hence we perform
under $13 \lceil \log n \rceil + 3$ opertions (some operations are not loop related).
In any case, the complexity is $\mathcal{O}(\log n)$


### Theorem 8
Let $\mathcal{L}$ and $A_{sf}$ be the LCP array and the suffix array of string $S$ and let $f$ be the suffix
lookup from $S$ to $A_{sf}$. $A_{sf}$ must not contain suffixes that start at position less or equal to $i$.
Instead, those positions need to be filled with value $\textnormal{len}(S)$.
Let also $i$ be an arbitrary index in $S$. Then function `find find_distinguished_elements` works as intended, that is
it returns the list containing all distinguished elements $k_{0}(i), k_1(i), k_2(i), \ldots$, in this order.
Furthermore, it has time complexity of $ \mathcal{O}(\sqrt{N - i} \log N)$ where $N$ is the length of string $S$.

#### Proof:
The edge case is when $i = \textnormal{len}(S) - 1$ because then there are no distinguished elements for $i$. But in that case
the algorithm returns an empty list which is correct. \
Let us assume that $ < \textnormal{len}(S) - 1$. Let $k_0 < k_1 < \ldots < k_n$ be all distinguished elements for $i$
where $n \in \N$ denotes their number (note that n \geq 1 follows from $i+1$ being the distinguished element).
We will prove that the algorithm return the list containing exactly $[k_1, k_2, \ldots k_n]$ in that order.\

Clearly we start with $p := \textnormal{pos} = f(i)$, an empty list of distinguished elements and
$d := \text{lcp\_depth} = 0$. At each step $s = 0, 1, \ldots$ the while loop will add one element $k'_s$ to the output list and
update the value of $d$ to $d_s$. Note that $d_s$ is updated to be $\pi(i, k) + 1$ which comes directly from the definition
of $\pi$.
We will prove by induction that $k'_s = k_s$ for $s = 0, 1, 2, \ldots n$ and that the loop terminates in the $(n+1)$-th step
before appending values to the list.
Let's start with the base. As $d = 0$, all elements in LCP array are greater or equal to $d$. Thus functions
`find_left_limit` and `find_right_limit` return $l = 0$ and $r = \textnormal{len}(S) - 1$ respectively. Then the algorithm computes
$$k_0' = k = \min{l \leq x \leq r} A_{sf} = \min{x} A_{sf} = i + 1 $$
since places in $A_{sf}$ where indices smaller or equal to $i$ would appear are filled with value $\textnormal{len}(S)$.
This is equal to $k_0$. Also, the loop will continue since $l \neq r$.\
Assume now that $k_s' = k_s$ for some $ 0 < s < n$. Then we know that $d_{s} = \pi(i, k_s) + 1$. Calling functions
`find_left_limit` and `find_right_limit` in step $s + 1$ returns $l$ and $r$ such that
$$ l = \min(x \leq p: \mathcal{L}(y) \geq d_s \quad \forall x < y \leq i) $$
$$ r = \max(p \geq x: \mathcal{L}(y) \geq d_s \quad \forall i < y \leq x) $$

Let us now prove a helper lemma: If $\pi(i, j) \geq d_s$ then $l \leq f(j) \leq r$. Indeed, $A_{sf}$ is sorted so between $f(j)$ and
$p$ (included) there can only be elements $x$ such that $\mathcal{L}(x) \geq \pi(j, i) \geq d_s$.
But $l$ and $r$ we construcuted to contain all such segments.

Notice that $\pi(i, k_{s+1}) \geq \pi(i, k_s) + 1 \geq d_s$ so $f(k_{s+1}) \in [l, r]$. Since we also have $i \in [l, r]$ and
$k_s \neq i$, we must have $l \neq r$ so the loop does not terminate.
Let $k'_{s+1} = \min_{l \leq x \leq r} A_{sf}(x)$ as computed in the function.
We have $l \leq f(k'_{s+1}) \leq r$ (by construction) and therefore
$$\pi(k'_{s+1}, i) = \min_{\min(p, f(k'_{s+1})) < x \leq \max(p, f(k'_{s+1}))} \mathcal{L}(x) \geq \min_{l < x \leq r} \mathcal{L}(x) \geq
d_s > \pi(k_s, i).$$
Suppose that $k'_{s+1}$ is not a distinguished element for $i$. Then there would exist some $i < j < k$ such that
$\pi(i, j) \geq \pi(i, k'_{s+1})$. But that means that $l \leq f(j) \leq r$.
Hence $j = A_{sf}(f(j)) \geq \min_{l < x < r} A_{sf}(x) = k'_s$ leading to
the contradiction.
So far we have proved that $k'_{s+1} is a distinguished element and $k'_{s+1} > k_s$. Suppose $k'_{s+1} != k_{s + 1}$.
In that case we must have $k'_{s+1}> k_s$.
But then $\pi(i, k_{s+1}) \geq \pi(i, k_s) + 1 = d_s$ so $l < f(k_{s+1}) < r$ (analgue conclusion was made a little ago)
so $k_s \geq \min_{l < x < r} A_{sf}(x) = k'_{s+1}$ leading to another contradiction.\
Hence $k'_{s+1} = k_{s+1}$.
The only thing left to show is that the loop terminates in step $n + 1$. If we would have $l \neq r$ then
then $\min_{l \leq x \leq r} A_{sf}(x)$ would be a distinguished element for $i$ (using the same argument from a while ago)
but this is impossible since $k_n$ is the largest distinguished element for $i$. Hence we must have $l = r$ and the loop
will terminate in step $n + 1$ without appending any outputs to the list.

Regarding complexity let $N = \textnormal{len}(S)$, the operations outside of the loop are insignificant. It was a pain to prove (in one of the
main theorems above) there are
at most $\sqrt{N - i}$ distinguished elements for $i$ but this also gives us the upper
bund on the number of steps in the loop. In each step of the loop we compute $l$ and $r$ which has complexity
$\mathcal{O}(log_N)$ in both cases. We also have to compute two minimumums over segment trees for $\mathcal{L}$ and
$A_{sf}$, both of which have complexity $\mathcal{O}(N)$. Therefore, the algorithm has complexity
$$\mathcal{O}(\sqrt{N - i} \log N).$$

### Theorem 9.
Let $n \in \N$ be an arbitrary number and let $S$ be a string of $n$ characters from a finite alphabet.
Let $q_1, q_2, \ldots q_n$ be a collection of queries, $q_j = (s_j, e_j), j=1,2, \ldots n$.
Then function `main` return a list of numbers $a_1, a_2, \ldots a_n$ such that
$$a_j = \# \{\textnormal{string } s: s \textnormal{ is a substring of } S[s_j: e_j] \} $$
Moreovers, the time complexity of the algorithm is $\mathcal{O}(n^{3/2} \log n)$.

#### Proof
Let $a_j$ the actual numbers specified by the above formula and let us use $a'_j$ to denote the outputs of
algorithm. We have to prove that $a_j = a'_j$ and that algorithm finishes after outputing $a'_n$. \
The algorithm starts by constructing the suffix array $A_{sf}$ of $S$, the corresponding LCP-array $\mathcal{L}$
and an empty FW-tree $\mathcal{F}$ with ranged updates. Constructing $A_{sf}$ and $\mathcal{L}$ takes $\mathcal{O}(n)$ operations
according to https://arxiv.org/pdf/1101.3448 (for example), and since $\mathcal{F}$ is empty it is constructed in $O(1)$ time.
We create a reverse lookup $f$ from indices of $S$ to $A_{sf}$ which takes $\mathcal{O}(n)$ time as well.
Then we also create a partial suffix array $P_{sf}$ - an array of length $n$ initially filled with value $n$.
This takes $\mathcal{O}(n)$ time.
Now we build a segment tree on both $P_{sf}$ and $\mathcal{L}$. These are in
fact very special kinds of segment trees and can be constructed on $\mathcal{O}(n)$ time,
see https://cp-algorithms.com/data_structures/segment_tree.html.
Finally, we need to sort the input list of queries which takes $\mathcal{O}(n \log n)$ time.
In summary, the setup is completed in $\mathcal{O}(n \log n)$ time.\
Let us move to the loop with $n$ steps where $i$ counts down from $n-1$ to $0$.
First of all, notice that at the end of each step we update the value of $f(i)$ to the partial array $P_{sf}$ and the correspondig
segment tree so that during the step $i$, $P_{sf}$ contains excatly suffixes from $i+1$ to $n - 1$ with
values in place of missing suffixes set to $n$.
Each such update takes $\mathcal{O}(\log n)$ time.
Let us denote $\mathcal{F}_n = 0$ to be the initial state of $\mathcal{F}$.
We will prove by induction that, at each step $i$, $\mathcal{F}$ is updated so that $\mathcal{F}_i[0:i - 1] = 0$ and
$$\sum_{j = 0}^{e-1}\mathcal{F}_i[j] = \# \{\textnormal{string } x: x \textnormal{ is a substring of } S[i: e] \}
\qquad \forall i < e \leq n$$
Furthermore, each such update is performed in $\mathcal{O}(\log n)$ operations.
The base of the induction is $i = n-1$. This is a special case for function `find_distinguished elements`
which returns an empty list.
Since the list is empty and $\mathcal{F}_n$ was intially filled with zeros,
the algorithm only updates $\mathcal{F}_{n-1}[n-1: n] = \mathcal{F}_{n}[n-1: n] + 1$ so that
for $e = n$ we have
$$\sum_{j = 0}^{e-1}\mathcal{F}_{n-1}[j] = \mathcal{F}_{n-1}[n-1] = 1 $$
and there is naturally only one unique substring of $S[n-1: n]$.
Since this is the only valid choice of $e$ the induction base is proved. \
Let's now suppose that the equation is true for some $i \geq 1$ and prove it is true for $i - 1$.
Notice that the number of unique substrings in $S[i, e]$ (for arbitrary $e$) is equal to the number of nodes in the
suffix tree $ST(i, e)$ build on $S[i: e]$. This is completely described by the suffix array and LCP array
for the $S[i, e]$. Therefore we can also write
$$\sum_{j = i}^{e-1}\mathcal{F}_i[j] =  \vert ST(i, e) \vert \qquad \forall i < e \leq n$$
Moreover, for each $e > i$, $ST(i, e)$ and $ST(i - 1, e)$ are related. One only needs to add the suffix $S[i-1]$ to the
tree $ST(i, e)$ to get the the suffix tree $ST(i-1, e)$. If $p$ is the length of common prefix of
suffix $S[i]$ that already exists in $ST(i,e)$ this will add exactly $e - (i - 1) - p$ nodes.
Let $\pi_e$ be the function computing largest common prefix on string $S[: e]$, that is $\pi_e$ is
exactly $\pi$ as defined before but for string $S[:e]$ instead of $S$. It is easy to see that
$$\pi_e(x, y) = \pi(x, y) \wedge (e - x) \wedge (e - y).$$
Suppose $i \leq k < e$ be such that $\pi_e(i-1, k) = \max_{i-1 < j < e} \pi_e(i-1, k)$. There might be several such $k$
so let us take the smallest one to be specific.
We will prove that $k$ is $\pi$-distinguished for $i-1$. Indeed, if that would not be the case,
there would exist  $i - 1 < j < k$ such that $\pi(i-1, j) \geq \pi(i-1, k)$.
Then $\pi_e(i-1, j) = \pi(i-1, j) \wedge (e - j) \geq \pi(i-1, k) \wedge(e - k) = \pi_e(j, k)$
which cotradict the minimality of $k$. \
So we find that
$$\vert ST(i - 1, e) \vert = \vert ST(i, e) \vert + (e - i + 1) - \max_{i - 1 \rightarrow k} \pi(i-1, k) \wedge (e - k)$$
Let $i - 1 < k_0, k_1, \ldots k_r$ be the distinguished elements for $i-1$ as returned by the function
`find_distinguished_elements`.\
Let us also shorten $\varphi_\alpha := \varphi_\alpha(i - 1) = \pi(i-1, k_\alpha)$ for $\alpha = 1, 2, \ldots r$ and
$$g(e) \equiv g(e, i-1) := \max_{i - 1 \rightarrow k} \pi(i-1, k) \wedge (e - k)$$
For $e < n$ let us consider the difference $g(e + 1) - g(e)$. Note that
$$0 \geq \pi(i-i, k) \wedge (e + 1 - k) - \pi(i-1, k) \wedge (e - k) \geq 1$$
so we must have $g(e + 1) - g(e) \in \{0, 1\}$ since the value is clearly an integer.\
Let us suppose $g(e + 1) - g(e) = 0$. Let $k_{\alpha}$ denote the smallest $k$ for which the
maximum is achieved in $g(e)$. If $\alpha < r$ then we must have
$e \leq k_{\alpha + 1} + \phi_\alpha$; otherwise the maximum would be achieved for
$k_{\alpha + 1}$ because $\pi(i-1, k_{\alpha + 1}) > \pi(i-1, k_{\alpha})$ which contradicts the
construction of $k_\alpha$.
Because of $g(e + 1) - g(e) = 0$ we find
$$0 = \max_{i - 1 \rightarrow k} \pi(i - 1, k) \wedge (e + 1 - k) - \pi(i-1, k_{\alpha}) \wedge (e - k_{\alpha})
\geq \pi(i-1, k_{\alpha}) \wedge (e + 1 - k_{\alpha}) - \pi(i-1, k_\alpha) \wedge (e - k_{\alpha}) \geq 0$$
so $\pi(i-1, k_{\alpha}) \wedge (e + 1 - k_{\alpha}) = \pi(i-1, k_\alpha) \wedge (e - k_{\alpha})$ which is only
possible when $e \geq k_\alpha + \varphi_\alpha$. Moreover for $e = k_{\alpha + 1} + \varphi_{\alpha}$ we
would have $\varphi_{\alpha + 1} \wedge (e + 1 - k_{\alpha + 1}) = \phi_\alpha + 1 > g(e)$ which contradicts
$g(e + 1) - g(e) = 0$.\
Thus $g(e + 1) - g(e) = 0$ implies
$$e \in \bigcup_{\alpha=0}^{r-1} [k_\alpha + \varphi_\alpha, k_{\alpha + 1} + \varphi_\alpha)
\cup [k_r + \varphi_r, n]$$
Conversly, let $e$ be in the set on the left. If $e \geq k_r + \varphi_r$ then $g(e) = \varphi_r$ which
is the highest value $g$ can obtain (since $\varphi_r \geq \varphi_{k'}$ for every $k'$), so
$g(e+1) - g(e) = 0$.\
If $k_\alpha + \varphi_\alpha \leq e < k_{\alpha + 1} + \varphi_\alpha$ for some $\alpha$
then we have the following:
1) $\varphi_{\alpha} \wedge (e + 1 - k_\alpha) = \varphi_{\alpha} \wedge (e - k_\alpha) = \varphi_{\alpha}$,
2) $\varphi_{\alpha'} \wedge (e + 1 - k_\alpha') \leq \varphi_{\alpha'} < \varphi_{\alpha}$ for all $\alpha' < \alpha$,
3) $\varphi_{\alpha''} \wedge (e + 1 - k_\alpha'') \leq (e + 1 - k_{\alpha + 1}) \leq \varphi_{\alpha}$ for all $\alpha < \alpha''$

Combining these three findings we see that $g(e+1) = g(e) = \varphi_\alpha$ so $g(e+1) - g(e) = 0$.\
As $g(i) = 0$ is easily computed, we now have
$$ g(e) = \sum_{j=i}^{e-1} \sum_{\alpha=0}^{r-1} \left( 1 - \mathbf{1}_{[k_\alpha + \varphi_\alpha, k_{\alpha + 1} + \varphi_\alpha)} (j)  +
\mathbf{1}_{[k_r + \varphi_{r}, n]}(j) \right)  = (e - i) -
\sum_{j=i}^{e-1} \sum_{\alpha=0}^{r-1} \left(\mathbf{1}_{[k_\alpha + \varphi_\alpha, k_{\alpha + 1} + \varphi_\alpha)} (j)  +
\mathbf{1}_{[k_r + \varphi_{r}, n]}(j) \right)$$
and thus
$$\vert ST(i - 1, e) \vert = \vert ST(i, e) \vert + (e - i + 1) - g(e) = \vert ST(i, e) \vert + 1 +
\sum_{j=i}^{e-1} \sum_{\alpha=0}^{r-1} \left(\mathbf{1}_{[k_\alpha + \varphi_\alpha, k_{\alpha + 1} + \varphi_\alpha)} (j)  +
\mathbf{1}_{[k_r + \varphi_{r}, n]}(j) \right)$$
If we define
$$ h(j) = \mathbf{1}_{\{i-1\}}(j) + \sum_{\alpha=0}^{r-1} \left(\mathbf{1}_{[k_\alpha + \varphi_\alpha, k_{\alpha + 1} + \varphi_\alpha)} (j)  +
\mathbf{1}_{[k_r + \varphi_{r}, n]}(j) \right) $$
then
$$ \vert ST(i - 1, e) \vert  = \sum_{j=0}^{e-1} \mathcal{F}_i(j) + \sum_{j=0}^{e-1} h(j) =
 \sum_{j=0}^{e-1} \mathcal{F}_i(j) + h(j) $$
with remark that $\mathcal{F}_i(i-1) = 0$ was initialized in the algorithm. So we can set $\mathcal{F}_{i-1} = \mathcal{F}_i + h$
to get
$$\vert ST(i - 1, e) \vert = \sum_{j=i-1}^{e-1} \mathcal{F}_{i-1}(j).$$
But this is exactly the update performed in the algorithm which which proves the induction for $e > i$ (if we note that
$h(j) = 0$ and $\mathcal{F}_i (j) = 0$ for $j < i - 1$.
The case $e = i$ needs to be verified separately. But this is easy since substring $S[i-1: i]$ has only 1 character and thus
has exactly one unique substring. As we have updated $\mathcal{F}_{i-1}(i-1) = 1$ the claim follows.
By mathematical induction, the initial statment is proved.\
Finally, the algorithm initially sorts the input queries then in step $i$ computes outputs for all queries
$q_j = (s_j, e_j)$ such that $s_j = i$. The output is computed as
$$a'_j = \sum_{j=0}^{e-1} \mathcal{F}_{i-1}(j) = \vert ST(i - 1, e) \vert =
\# \{\textnormal{string } s: s \textnormal{ is a substring of } S[i: e_j] \} = a_j $$
which is what we were set up to prove.
The outputs might not be in the inital order but they are reordered in the final step.\
Regarding time complexity, during each setep of the for loop we need to call `find_distinguished_elements`
function, which takes $\mathcal{O}(\sqrt{n} \log n)$ operations, and then also make $r+1$ ranged updates
with the Fenwick tree $\mathcal{F}$, each of which takes $\mathcal{O}(\log n)$ operations. Since we know
from our main estimate that $r \leq \sqrt{8 n}$ we find that the total cost of updates is
$\mathcal{O}(\sqrt{n} \log n)$. Since there are exactly $n$ steps in the for loop, all of this can be performed
in $\mathcal{O}(n^{3/2} \log n)$ operations. It remains to accunt for computing of outputs $a_j'$. Clearly
an output is performed by calling a partial sum operation on the fenwinck tree $\mathcal{F}$ exactly once
for each $j$. The order of $j$ in which this is computed is unclear, but it makes no difference. The cost
of computing each partial sum is $\mathcal{O}(\log n)$ so the total cost of computing all outputs is
$\mathcal{O}(n \log n)$ as there are at $n$ of them.\
The final reordering of outputs can is performed in $\mathcal{O}(n)$ steps so that that the complete algorithm
runs in $\mathcal{O}(n^{3/2} \log n)$ time complexity.\
This completes the proof.
