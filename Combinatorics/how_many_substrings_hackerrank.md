# Complexity of [How many substrings](https://www.hackerrank.com/challenges/how-many-substrings/problem)

### Setup
Let:
* $\mathcal{A}$ be a countable alphabet
* $N \in \N$, $S = c_1 \ldots c_N \in \mathcal{A}$ a string of characters
* $SA \equiv SA(S)$ the suffix array of $S$ and $LCP \equiv LCP(S)$ the corresponding longest common prefix array
* $lkp \equiv lkp(S)$ the lookup table from $S$ to $SA$ defined by $lkp[SA[k]] = k$


### Definition 0.1
A suffix array $SA$ of $S$ is the array of alphabetically sorted suffixes of $S$.
More precisely, the elements of the $SA$ are integers from $0$ to $len(S) - 1$
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

### Definition 0.4:
A Fenwick tree of $n$ elements is an array of $n$ elements such that ...


### Problem ([hackerrank.com - How many substrings](https://www.hackerrank.com/challenges/how-many-substrings/problem))
Given a string of characters $S$ of length $N$ and a list of $N$ queries consisting of a start index $s_k$ and an end index $e_k$, $0 \leq s_k < e_k \leq N$
construct an algorithm that counts the number of unique substrings in $S[s_k: e_k]$ for each $k$.
When $N = 10^5$ the algorithm is supposed to work in under approx. 2 seconds, i.e. is it allowed to make around $10^9$ operations.

_Note - it is likely that the desired complexity is slightly below $\mathcal{O}(N^{\frac{3}{2}} \log(N))$.
Whether an exponent lower than $\frac{3}{2}$ is required remains unclear._

### Definition 1:
Let $i, j \in \N$, define $\pi(i, j)$ to be the length of the common prefix of $S[i:]$ and $S[j:]$.
That is, $\pi(i, j) = \min_{x \in [m, M]}LCP[x]$ where $m := \min(lkp[i], lkp[j])$ and $M := \max(lkp[i], lkp[j])$

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
* $k_0(i) = i + 1$
* $\pi(k_\alpha(i), i) \geq \alpha$

### Lemma 3:
Let $k$ be distinguished for $i$ and $j$, $i < j$. Then
1) $\pi(i, k) > \pi(j, k)$,
2) $\pi(i, j) = \pi(j, k)$

#### Proof:
Clearly $i < j < k$. If we suppose that $\pi(i,k) \leq \pi(j,k)$, then $\pi(i,j) \geq \min(\pi(i, k), \pi(j, k)) \geq \pi(i, k)$. But this contradicts the fact that $k$ is distinguished for $i$ which proves 1).\
2) follows immediately from one of the previous lemmas.

### Prop 4:
For any $i < j$ there is at most one $k$ which is distinguished for both $i$ and $j$.
#### Proof:
Suppose there are 2 such distinguished elements, $k^1 < k^2$.
By previous lemma, this would imply $\pi(j, k^1) = \pi(i, j) = \pi(j, k^2)$ which contradicts the definition of $j \to k^2$.


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
def Main
    Input:
        1 <= n, q <= 10^5,
        string S of n character,
        list of queries Q = [(s_k, e_k) for k=1...q]
    Output:
        list of n ints - number of different substrings of S in the inclusive range s_k, e_k

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

    for l = n - 1 down to l = 0:
        pos = lkp[l]

        k_1 < k_2 < ... < k_r = find_distinguished_elements(
            starting_position=pos,
            lcp_segment_tree=LCP_seg_tree,
            sa_seg_tree=sa_seg_tree,
            sa_lookup=lkp
        )
        fwt.update_range(start=l, end=n, value=1)
        _progressive_lcp = 0
        for i=1 up to r-1:“
            fwt.update_range(
                start=k_i + _progressive_lcp,
                end=k_i + LCP_seg_tree.min(pos, lkp[k_i]),
                value=-1
            )
            _progressive_lcp = LCP_seg_tree.min(pos, lkp[k_i])
        sa_seg_tree.update(pos, l)

def update_range:
    Input:
        Fenwick tree fwt
        start - first index of range to update (included)
        end - last index of the range to update (excluded)
        value - the value to update with
    Output:
        updated Fenwick tree fwt

def find_distingiushed_elements:
    Input:
        l - suffix index for which distinguished elements are computed
        LCP_seg_tree - min segment tree on the full LCP array
        sa_seg_tree - min segment tree on the partial suffix array
        sa_lookup - inverse lookup for suffix array
    Output:
        Inreasing list k_1 < k2 < ... < k_r - distinguished suffix indices for l (l < k_1)

    pos = sa_lookup[l]
    dist_elem = empty_list()
    r = 0

    lcp_depth = 0
    while True:
        left = find_left_limi(
            LCP_seg_tree,
            start=pos,
            value=lcp_depth
        )
        right = find_right_index(
            LCP_seg_tree,
            start=pos,
            value=lcp_depth
        )
        if right < n-1:
            right += 1
        k = sa_seg_tree.min(left, right)
        dist_elem.append(k)
        r = r + 1
        a = min(pos, k)
        b = max(pos, k)
        lcp_depth = LCP_seg_tree.min(a, b)

    return r, dist_elem


def find_left_limit:  # finds the left-most index j such that
                      # min_seg_tree[x] \geq alpha for all j <= x <= start
    Input:
        min_seg_tree  # "min"-segment tree over an arbitrary array
        start         # element to start the search from
        alpha         # an arbitrary bound
    Output:           # the desired index j
    if start == 0:
        return 0
    node = min_seg_tree.get_leaf_by_index(start)
    while node != root and (node.is_left_child() or node.parent.left_child().value() >= alpha):
        node = node.parent()
    if node == root:
        return 0
    if node == start:
        if start.value() >= \alpha
            return start - 1
        else
            return start
    node = node.parent().left_child()

    while not node.is_leaf():
        if node.right_child().value() < value:
            node = node.right_child()
        else:
            node = node.left_child(direction)
    return = node.index() + 1


def find_right_limit: # finds the right-most index j such that
                      # min_seg_tree[x] \geq alpha for all start < x <= j
    Input:
        min_seg_tree  # "min"-segment tree over an arbitrary array
        start         # element to start the search from
        alpha         # an arbitrary bound
    Output:           # the desiderd index j

    node = min_seg_tree.get_leaf_by_index(start)
    while node != root and (node.value() >= alpha):
    while node != root and (node.is_right_child() or node.parent().right_child().value() >= value):
        node = node.parent()
    if node == root:
        return segment_tree.len() - 1

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
Moreover computing `find_index` has complexity $\mathcal{O} (\log n)$

#### Proof:
First of all, if $i = 0$ then the function returns $j=0$ which trivially satisfies the requrements.
So we assume $i > 0$ from now on.
Next, not that such $j$ must exist because the consition is trivially satisfied for $j = i$. Therefore
a maximal such $j$ must exist and is clearly unique. From now on, $j$ will denote that maximal element. \
Note that the first while loop travels the ancestors from $i$ to the root.\
If $j = 0$ (note that the value of LCP at 0 is undefined) then $\mathcal{A}[x] \geq \alpha$ for all $0 < x \leq i$.
But this means that for every $P, L, R$ such that $i \preccurlyeq R$ we have $\mathcal{A}[L] \geq \alpha$ so the
loop will only terminate at root. An the algorithm will return 0 which is exactly $j$. \
In case, $j > 0$, we need to have $\mathcal{A}[j] < \alpha $ since otherwise $j-1$ would be
a smaller element satisfying the same requirements as $j$. Let $P$ the first common ancestor of both $i$ and $j$.
If $L$ and $R$ are left and right children of $P$ then we must have $j \preccurlyeq L$ and $i \preccurlyeq R$.
But then $\mathcal{A}[P] \leq \mathcal{A}[j] < \alpha$ so the loop terminates at $R$ (or before $R$).
If the loop would terminate before $R$ there would be $P_2 \preccurlyeq R$, $L_2$, $R_2$ such that
$\mathcal{A}[L_2] < \alpha$, $i \preccurlyeq R_2$. But then $j \lll L_2$ and, from definition of $j$, we know that
for all $x \in L_2$ we have $j < x \leq i$ and consequently $\mathcal{A}[x] \geq \alpha$.
This leads to $\mathcal{A}[L_2] \geq \alpha$ and a contradiction.
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
of the segment tree). Assuming that `is_right_child` takes 2 operations in each step of the first loop we perform
at most $1 + 2 + 4 + 1 = 8$ operations, and in the second loop we perform $1 + 3 + 4 = 8$ operations. Hence we perform
under $16 \lceil \log n \rceil + 4$ opertions (some operations are not loop related). In any case, the complexity is $\mathcal{O}(\log n)$


### Theorem 8
TODO

Next, we move to `find_distinguished_elements` function.
Note that this function is called within the main function only with the variable `sa_seg_tree` as the segment tree. Call this segment tree $\mathcal{S}_a$ and call the segment tree `LCP_seg_tree` by $\mathcal{S}_l$.
$\mathcal{S}_a$ is initialized with a value of $n$ and element at `pos = lkp[l]` is set to $l$ once the function is called with parameter $l$.
As `lkp` is a bijection, whenever this function is called, $\mathcal{S}_a$ contains values $l, l+1, \ldots n-1$ exactly once and then several times the value $n$.

We will prove by induction that each set of the while loop produces the correct distinguished element. Initially, $v=l$ and all elements in $\mathcal{S}_a$ are larger or equal than that value.
Thus, `left` equals $0$ and `right` equals $n-1$ and consequently `depth` is equal to $\tilde{v}=\min \mathcal{S}_l$.
Clearly all elements of $\mathcal{S}_l$ are larger than $\tilde{v}$ so the second update keeps `left` at $0$ and  `right` at $n-1$.
Recalling the specific structure of $\mathcal{S}_a$ we get that $k = l+1$ which is the first distinguished index $k_1(l)$ in the previous notation. $v$ is set to $l+2$.

We now assume that ...

### Theorem 2. Previous algorithm has time complexity of $\mathcal{O}(n^{3/2}\log n)$

#### Proof:


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
