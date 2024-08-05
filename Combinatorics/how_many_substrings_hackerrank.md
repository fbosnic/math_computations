# Complexity of [How many substrings](https://www.hackerrank.com/challenges/how-many-substrings/problem)


### Setup
Let:
* $\mathcal{A}$ be a countable alphabet
* $N \in \N$, $S = s_1 \ldots s_N \in \mathcal{A}$ a string of characters
* $SA \equiv SA(S)$ the suffix array of $S$ and $LCP \equiv LCP(S)$ the corresponding longest common prefix array
* $lkp \equiv lkp(S)$ the lookup table from $S$ to $SA$ defined by $lkp[SA[k]] = k$

### Problem ([hackerrank.com - How many substrings](https://www.hackerrank.com/challenges/how-many-substrings/problem))
Given a string of characters $S$ of length $N$ and a list of $N$ queries consisting of a start index $s_k$ and an end index $e_k$, $0 \leq s_k < e_k \leq N$
construct an algorithm that counts the number of unique substrings in $S[s_k: e_k]$ for each $k$.
When $N = 10^5$ the algorithm is supposed to work in under approx. 2 seconds, i.e. is it allowed to make around $10^9$ operations.

_Note - it is likely that the desired complexity is slightly below $\mathcal{O}(N^{\frac{3}{2}} \log(N))$.
Whether an exponent lower than $\frac{3}{2}$ is required remains unclear._

### Definition 1:
Let $i, j \in \N$, define
$\pi(i, j) = \min_{x \in [m, M]}LCP[x]$ where $m := \min(lkp[i], lkp[j])$ and $M := \max(lkp[i], lkp[j])$

### Corollary 1.1:
* $\pi(i, j) = \pi(j, i)$
* $\pi(i,j) \geq \min(\pi(i, k), \pi(j, k)) \quad \forall k$

### Lemma 1.2:
For any $i$, $j$ and $k$ if $\pi(i, j) > \pi(i, k)$ then $\pi(i, k) = \pi(j, k)$.

#### Proof:
Note that $\pi(i, j) > \pi(i, k) \geq \pi(i, j) \wedge \pi(j, k)$ and we must have $\pi(i, k) = \pi(j, k)$.

### Definintion 2:
Let $i < k$ be arbitrary. $k$ is said to be distinguished for $i$, written $i \rightarrow k$, if
$$\pi(i, j) < \pi(i, k) \qquad \forall i < j < k$$
*Note that $i+1$ is always distinguished for $i$*

Moreover for $\alpha \in \N$, $k$ is said to be $\alpha$-distinguished for $i$, written $i \xrightarrow{\alpha} k$  if $k$ is distinguished for $i$ and there are exactly $\alpha - 1$ indices in the interval $(i, k)$ which are distinguished for $i$.
Clearly, $\alpha$-distinguished index for $i$ is unique if it exists. Let us denote it by $k_\alpha(i)$.

### Corollary 1.2:
For all $i$ and $\alpha$:
* $k_1(i) = i + 1$
* $\pi(k_\alpha(i), i) \geq \alpha - 1$

### Lemma 3:
Let $k$ be distinguished for $i$ and $j$, $i < j$. Then
1) $\pi(i, k) > \pi(j, k)$,
2) $\pi(i, j) = \pi(j, k)$

#### Proof:
Clearly $i < j < k$. Suppose the contrary, that $\pi(i,k) \leq \pi(j,k)$. Then $\pi(i,j) \geq \min(\pi(i, k), \pi(j, k)) \geq \pi(i, k)$. But this contradicts the fact that $k$ is distinguished for $i$ and proves 1).\
2) follows immediately from one of the previous lemmas.

### Prop 4:
For any $i < j$ there is at most one $k$ which is distinguished for both $i$ and $j$.
#### Proof:
Suppose there are 2 such distinguished elements, $k_1 < k_2$.
By previous lemma, this would imply $\pi(j, k_1) = \pi(i, j) = \pi(j, k_2)$ which contradicts the definition of $j \to k_2$.

### Prop 5:
For arbitrary $i$ and $\alpha$ we have $k_{\alpha + 2} (i) - k_{\alpha} (i) > \alpha / 2$, provided that $k_{\alpha +2}$ exists.

#### Proof:
Let us argue by contradiction.
We know that $\pi(i, k_{\alpha + 1}) \wedge \pi(i, k_{\alpha + 2}) \geq \alpha$.
Let $m$ be the greatest common divisor of $m = gcd(k_{\alpha + 2} - k_{\alpha + 1}, k_{\alpha + 1} - k_{\alpha})$. It is easy to see that $m \leq \alpha/2$ as a consequence of the Euclidean algorithm for the gdc and the assumption $k_{alpha+2} - k_{\alpha} \leq 2\alpha$.
Then $S$ is locally $m$-periodic around $i$, $k_{\alpha + 1}$ and $k_{\alpha + 2}$ in the sense that:
$$S[x: x + m] = S[x + m: x + 2m] \qquad x = i, k_{\alpha + 1}, k_{\alpha + 2}$$
To prove this, notice first that $S[i: i+2m] = S[k_{\alpha + 1}: k_{\alpha + 1} + 2m] = S[k_{\alpha + 2}: k_{\alpha + 2} + 2m]$ due to $\pi(i, k_{\alpha + 1}) \wedge \pi(i, k_{\alpha + 2}) \geq \alpha$ and $2m \leq \alpha$.

If the claim were fase, it would imply that $k_{\alpha +1} - k_{\alpha} \leq \alpha / 2$. Let $P = S[k_{\alpha}: k_{\alpha + 1}]$ but then $S[i + l] = S[i + k_{\alpha}]$

### Algorithm 1:
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

        r, k_1 < k_2 < ... < k_r = find_distinguished_elements(
            starting_position=pos,
            lcp_segment_tree=LCP_seg_tree,
            sa_seg_tree=sa_seg_tree,
            sa_lookup=lkp
        )
        fwt.update_range(start=l, end=k_1, value=1)
        for i=1 up to r:
            fwt.update_range(
                start=k_i + LCP_seg_tree.min(pos, lkp[k_i]),
                end=k_{i+1} + LCP_seg_tree.min(pos, lkp[k_i]),
                value=1
            )
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
        r - number of distinguished elements for pos
        k_1 < k2 < ... < k_r - distinguished suffix indices for l (l < k_1)

    pos = sa_lookup[l]
    dist_elem = empty_list()

    v = pos
    while True:
        left = find_last_larger_or_equal(
            sa_seg_tree,
            direction="left",
            start=pos,
            value=v
        )
        right = find_last_larger_or_equal(
            sa_seg_tree,
            direction="right",
            start=pos,
            value=v
        )
        if left > 0:
            left -= 1
        if right < n-1:
            right += 1
        depth = LCP_seg_tree.min(left, right)
        left = find_last_larger_or_equal(
            LCP_seg_tree,
            direction="left",
            start=pos,
            value=depth
        )
        right = find_last_larger_or_equal(
            LCP_seg_tree,
            direction="right",
            start=pos,
            value=depth
        )
        k = sa_seg_tree.min(left, right + 1)
        dist_elem.append(k)
        v = k - 1


    return r, dist_elem

def find_maximal_index_such_that_all_before_are_larger:
    Input:
        min_seg_tree - "min" segment tree over an arbitrary array
        direction - either "left" or "righ" determining the direction of search
        start - element to start the search from (excluded from search)
        value - an arbitrary bound
    output:
        index of maximal element (in the specified direction) such that all before it are larger than *value*
    node = min_seg_tree.get_leaf_by_index(start)
    while node != root and (node.is_child(direction) or node.parent().child(direction).value() >= value):
        node = node.parent()
    if node == root:
        if direction == "left":
            return 0
        else:
            return segment_tree.len() - 1

    node = node.parent.child(direction)
    while not node.is_leaf():
        if node.child(direction.reverse()).value() < value:
            node = node.child(direction.reverse())
        else:
            node = node.child(direction)
    return = node.index() - 1
```

### Theorem 1. Previous algorithm works as intented

#### Proof:
Let us verify that all functions produce the expected outputs starting from the
`find_maximal_index_such_that_all_before_are_larger`. The input here is a "min" segment tree over an arbitrary
($0$-indexed) array $\mathcal{S}$, together with a starting index $i$, a direction which is either
"left" or "right" and a value $\alpha$. Start by assuming that direction equals "right"
and let $j$ be the desired index, that is
$$ \mathcal{S}_{j+1} < \alpha \qquad \text{and} \qquad \mathcal{S}_x \geq \alpha \quad \forall x \in (i, j]$$
Let $\mathcal{S}(N) := \min_{x \preccurlyeq N} \mathcal{S}_x$ to be the "min operation" on
the segment tree for an arbitrary node $N$ where $x \preccurlyeq N$ indicates that
$x$ is an index such that the leaf at that index is a descendant of $N$.
Define also
$$f(x) = \begin{cases}\min_{(i, x]}\mathcal{S}_x \quad \text{ if } x > i \\ \mathcal{S}_{i+1} \quad \text{ otherwise.} \end{cases}$$
It is easy to extended it
to nodes in the segment tree $\mathcal{S}$ by defining
$f(N) = \min_{x \preccurlyeq N} f(x)$ for any node $N$ in
$\mathcal{S}$.

In case $j$ is the last index in the segment tree then $f(N) \geq \alpha$ for all nodes $N$.
Thus the first wile loop must finish with `node = root` and the algorithm
will return the length of the segment tree minus 1 which is the last index i.e. $j$ by assumption.

Otherwise, $j+1$ is a valid index of the segment tree so let $N$ be the lowest common
ancestor of $i$ and $j+1$ in $\mathcal{S}$. Then the left child
of $N$ must be an ancestor of $i$, call it $L$, and the right child, call it $R$,
must be an ancestor of $j + 1$. It follows that
$f(L) \geq \min_{x \in (i, j]} \geq \alpha$ and $f(R) \vee \mathcal{S}(R) \leq S_{j+1} < \alpha.$
Clearly the first while loop traverses the tree on the direct path from $i$ to the root.
Note that the terminating condition $\mathcal{S}(R) < \alpha$ is satisfied for $L$.
Also, if the loop would terminate before $L$, then there would exist
some $L_1$, it's parent $P_1$ (a descendant of $L$ or $L$ itself) and the
right child $R_1$ of $P_1$ satisfying (according to the termination condition)
$L_1 \neq R_1$ and $\mathcal{S}(R_1) < \alpha$.
But this is impossible because
$i \in L_1$ implies that $i < \min_{x \preccurlyeq R_1} x$ and thus
$f(R_1) \leq \mathcal{S}(R_1)$ from where we find
$\alpha \leq f(L) \leq f(P) \leq f(R_1) \leq \mathcal{S}(R_1)$ whih contradits the assumption.
Hence the first loop terminates exactly at $L$ and, taking into account the intermediate lines,
`node` points to $R$ just before the second loop starts.

As for the second loop, it must terminate as the depth of the `node` increases
at each step and the tree is of finite depth. Let us prove by induction
that $f(`node`) < \alpha$ in every step of the loop.
The statement is true inially as $f(R) < \alpha$.
Suppose that it is true at some step when `node` points to some node $N_2$.
Let $L_2$ and $R_2$ be the left and the right children of $N_2$.
Notice that $i \in L$ implies $i < \min_{x \preccurlyeq R} x$ and the
same is true for all the descendants of $R$, in particular for
$N_2, L_2$ and $R_2$. But this is enugh to conclude that
$f(X) \leq \mathcal{S}(X)$ for $X = N_2, L_2$ or $R_2$.
There are two cases to
consider. Firstly, if $\mathcal{S}(L_2) < \alpha$ then `node` is set to $L_2$ and the
statemnt holds since $f(L_2) \leq \mathcal{S}(L_2)$.  Otherwise, `node` is set to $R_2$
but the statement remains true as $f(R_2)$ = $f(N_2) < \alpha$ by definitition of $f$ and
inductive assumption. Thus, after the loop is finished, `node` points to
some $k$ such that $f(k) < \alpha$. We now show that $f(k - 1) \geq \alpha$.
Indeed, let $P_3$ be the lowest common ancestor of $k-1$ and $k$ and
let $L_3$ and $R_3$ be its left and right child respectively. There must
have been a step of the loop where `node` was pointing to $P_3$. Since
$R_3$ was selected for the next step it must mean that $f(L_3) \geq \alpha$
which implies that $f(k-1) \geq \alpha$.

Now we have that
$f(j) \geq \alpha$, $f(j + 1) < \alpha$, $f(k-1) \geq \alpha$, $f(k) < \alpha$
which implies that $j = k-1$ since $f$ is non-increasing.
Thus we have proved that the function behaves as expected in case the direction
is equal to right.

The case of direction equal to "left" is analoguous (though one still needs to
make sure! TODO)

Next, we move to `find_distinguished_elements` function.

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
