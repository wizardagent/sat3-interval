# The saturation number of 3-term arithmetic progressions in $\{1,\dots,n\}$

Let $\mathrm{sat}_3(n)$ be the least size of a maximal 3-AP-free subset of $[n]=\{1,\dots,n\}$. We prove $\mathrm{sat}_3(n)=\Theta(\sqrt{n})$, with explicit constants $\sqrt{2/3}\le\mathrm{sat}_3(n)/\sqrt{n}<2$. The upper bound is a placement of Csajbók–Nagy $R$-complete sets into the interval (no wrap-around). Exact values for $n\le 40$ are Lean. The spine of the upper bound is formalised in Lean 4 (`lean/`, no `sorry`).

## 1. Definitions

Let $n$ be a positive integer and write $[n]=\{1,2,\dots,n\}$. A *3-term arithmetic progression* (3-AP) is a triple of distinct integers $x,y,z$ with $2y=x+z$ in some order. A set $A\subseteq[n]$ is *3-AP-free* if it contains no 3-AP.

The set $A$ is *maximal* 3-AP-free in $[n]$ if it is 3-AP-free and, for every $t\in[n]\setminus A$, the set $A\cup\{t\}$ contains a 3-AP. Equivalently, every missing point is the third vertex of a 3-AP whose other two vertices lie in $A$.

Write $\mathrm{sat}_3(n)$ for the least cardinality of a maximal 3-AP-free subset of $[n]$. This is the independent domination number of the 3-uniform hypergraph of 3-APs on vertex set $[n]$.

The function is distinct from $r_3(n)$, the maximum size of a 3-AP-free subset of $[n]$ (OEIS A003002). It is also distinct from the minimum size of a complete 3-AP-free set in a cyclic group or vector space, studied by Csajbók and Nagy [1, 2]. Those papers treat $\mathbb{Z}_m$ and $\mathbb{F}_p^n$, not the interval $[n]$. A sequence search on OEIS for
$$
1,2,2,2,3,4,4,4,4,4,4,4,4,4,4,4,5,6,6,6,6,6
$$
returns no match (checked 2026-09-07). Savchev–Chen [3] treat uniqueness of large 3-AP-free subsets of $[n]$, not the minimal maximal ones. Chen [5] and Fang [6], following Kiss–Sándor–Yang [7], study infinite $AP_3$-covering sequences in $\mathbb{N}$: every large enough integer is the third term of a 3-AP with two earlier terms in the sequence. Those sequences need not be 3-AP-free, so the problem is different.

On $\mathbb{Z}$, the relation $c=2a-b$ with $a\neq b$ forces $c\neq a$ and $c\neq b$. Thus a finite set is 3-AP-free if and only if it is $(2,-1)$-avoiding in the sense of [1, 2]. Completeness in $[n]$ still differs from completeness in $\mathbb{Z}_n$: there is no wrap-around.

The results below that are not labelled computational are proved in ordinary mathematics. The spine of the upper bound is formalised in Lean 4 (`lean/`, no `sorry`); see §11. Exact values of $\mathrm{sat}_3(n)$ for $n\le 40$ are Lean (`sat3_eq_*`).

**Theorem 1.1.** For every integer $n\ge 1$,
$$
\mathrm{sat}_3(n)<2\sqrt{n}.
$$
In particular $\mathrm{sat}_3(n)=\Theta(\sqrt{n})$.

The lower bound of matching shape is Proposition 2.2. The proof of the upper bound is Theorem 9.2.

## 2. Pair bound

Each unordered pair in a 3-AP-free set determines at most three third vertices: $2b-a$, $2a-b$, and (when $a+b$ is even) $(a+b)/2$. A set of size $k$ therefore blocks at most $k+3\binom{k}{2}$ points of $[n]$, counting the set itself.

**Lemma 2.1.** For $k\ge 1$,
$$
k+3\binom{k}{2}=\frac{k(3k-1)}{2}.
$$
In particular $2\bigl(k+3\binom{k}{2}\bigr)=k(3k-1)$.

*Proof.* Direct expansion: $k+3k(k-1)/2=(2k+3k^2-3k)/2=(3k^2-k)/2$. The identity $2\cdot\mathrm{pairBound}(k)=k(3k-1)$ is `pairBound_double` in `lean/Sat3/PairBound.lean`.

**Proposition 2.2.** If $A\subseteq[n]$ is maximal 3-AP-free and $|A|=k$, then
$$
n\le \frac{k(3k-1)}{2}.
$$
Hence $\mathrm{sat}_3(n)\ge \min\bigl\{k:k(3k-1)/2\ge n\bigr\}$. In particular $\mathrm{sat}_3(n)=\Omega(\sqrt{n})$, and more precisely
$$
\mathrm{sat}_3(n)\ge \sqrt{\tfrac{2n}{3}}.
$$

*Proof.* Every point of $[n]$ is either in $A$ or a third vertex of a pair from $A$ (`coverList_covers`). The covering list has length $\mathrm{pairBound}(k)$ (`coverList_length`), so $n\le\mathrm{pairBound}(k)$ (`pairBound_of_maximal`, and `HasMaximalOfSize_pairBound` for the existence encoding). The identity $k(3k-1)/2=\mathrm{pairBound}(k)$ is `pairBound_half`. If $n\le\mathrm{pairBound}(k)$ then $2n\le 3k^2$ (`pairBound_quadratic`), hence $k\ge\sqrt{2n/3}$.

The bound is not always tight: $\mathrm{sat}_3(5)=3$ while the pair bound only forces $k\ge 2$, and $\mathrm{sat}_3(18)=6$ while the pair bound only forces $k\ge 4$.

## 3. The 4-point block

For $a\in\mathbb{Z}$ write
$$
S(a)=\{a,\,a+1,\,a+4,\,a+5\}.
$$

**Lemma 3.1.** $S(a)$ is 3-AP-free.

*Proof.* Translate to $S(0)=\{0,1,4,5\}$ and inspect the four-point set. Formalised as `S_AP3Free`.

**Lemma 3.2.** The pair-completions of $S(a)$ fill the interval $[a-5,a+10]$. Explicitly, the third vertices of pairs from $S(0)$ are
$$
\{-5,-4,-3,-2,-1,2,3,6,7,8,9,10\},
$$
so $S(0)$ together with its completions is $\{-5,-4,\dots,10\}$.

*Proof.* The six pairs and their third vertices:

- $\{0,1\}$: $-1,2$
- $\{0,4\}$: $-4,2,8$
- $\{0,5\}$: $-5,10$
- $\{1,4\}$: $-2,7$
- $\{1,5\}$: $-3,3,9$
- $\{4,5\}$: $3,6,9$

Union with $\{0,1,4,5\}$ is $\{-5,\dots,10\}$. Formalised as `S0_covers` and `S_covers_interval`.

**Corollary 3.3.** $S(6)=\{6,7,10,11\}$ is a maximal 3-AP-free subset of $[16]$. Hence $\mathrm{sat}_3(16)\le 4$. Combined with Proposition 2.2 (which forces $k\ge 4$, since $\mathrm{pairBound}(3)=12<16$) one has $\mathrm{sat}_3(16)=4$.

Formalised as `S6_maximal_16`, `sat3_exact_16`, and `sat3_eq_sixteen`. The same pin gives `sat3_eq_one`..`sat3_eq_four` and `sat3_eq_thirteen`..`sat3_eq_fifteen`.

**Lemma 3.4.** Let $d\in\{11,12,13,14,15,16\}$. Then $S(0)\cup S(d)$ is 3-AP-free, and its pair-completions fill the interval $[-d-5,\,d+10]$ with no holes.

*Proof.* A 3-AP with two points in $S(0)$ and one in $S(d)$ would force $d\in 2S(0)-S(0)-S(0)=[-10,10]$, contradicting $d\ge 11$. The same holds with the two blocks swapped. Completions of mixed pairs fill the gap between the two 16-point intervals $[-5,10]$ and $[d-5,d+10]$ precisely when $11\le d\le 16$. Boolean certificates `twoBlock_covers_11` through `twoBlock_covers_16` confirm there are no holes. The $d=16$ case after the translation $a\mapsto a+6$ is also `twoBlocks_maximal_32`.

**Corollary 3.5.** $S(6)\cup S(22)=\{6,7,10,11,22,23,26,27\}$ is a maximal 3-AP-free subset of $[32]$. Hence $\mathrm{sat}_3(32)\le 8$. Formalised as `twoBlocks_maximal_32`. The exact value is $7$ (Theorem 4.1); the two-block set is not a minimiser.

Three copies of $S(\cdot)$ at distance $16$ need not be 3-AP-free: $S(0)\cup S(16)\cup S(32)$ contains the 3-AP $0,16,32$.

## 4. Exact values

**Theorem 4.1.** The values of $\mathrm{sat}_3(n)$ for $1\le n\le 40$ are

$$
\begin{align*}
&n:&&1,2,3,4,5,6\text{–}16,17,18\text{–}26,27\text{–}32,33\text{–}40\\
&\mathrm{sat}_3(n):&&1,2,2,2,3,4,5,6,7,8.
\end{align*}
$$

Explicitly:
$$
\begin{array}{c|cccccccccccccccccccc}
n&1&2&3&4&5&6&7&8&9&10&11&12&13&14&15&16&17&18&19&20\\
\hline
\mathrm{sat}_3(n)&1&2&2&2&3&4&4&4&4&4&4&4&4&4&4&4&5&6&6&6
\end{array}
$$
$$
\begin{array}{c|cccccccccccccccccccc}
n&21&22&23&24&25&26&27&28&29&30&31&32&33&34&35&36&37&38&39&40\\
\hline
\mathrm{sat}_3(n)&6&6&6&6&6&6&7&7&7&7&7&7&8&8&8&8&8&8&8&8.
\end{array}
$$

*Certificate.* For $n=1$ through $40$ the value is Lean (`sat3_eq_*`). Pair-bound pin, two- and three-point enumerations, four-point enumeration at $n=17$, increasing 4- and 5-tuples at $n=18$--$22$, increasing 5-tuples at $n=23$--$26$ (`anyMaximalInc`; `pairBound(4)=22` kills size 4 once $n\ge 23$), 3-AP-free 5- and 6-tuples at $n=27$--$32$ (`anyMaximalFree`), and a recursive 3-AP-free search at $n=33$--$40$ (`anyMaximalSearch`; no maximal 5-, 6-, or 7-set, with `pairBound(5)=35` killing size 5 once $n\ge 36$). An explicit witness for each $n$ is in `data/sat3_values.json`. `scripts/verify_table.py` rechecks that the witness is maximal of the claimed size and that no 3-AP-free set of size $\mathrm{pairBound}$ through $\mathrm{sat}_3(n)-1$ is maximal. For $n\le 26$ the number of distinct minimisers was also counted (see §5).

The search is deterministic and small: $n=26$ takes about one second, $n=40$ about one minute, in CPython, deciding membership of an increasing $k$-tuple by forbidding midpoints already present. Computationally (not Lean), the same backtrack gives $\mathrm{sat}_3(n)=8$ for $n=41$--$46$, with witnesses in `data/sat3_values_ext.json`. The values $n=47,48$ were not finished.

One witness per $n$:

$$
\begin{align*}
n=1&\colon\{1\},&
n=2&\colon\{1,2\},&
n=4&\colon\{2,3\},&
n=5&\colon\{1,3,4\},\\
n=9&\colon\{1,2,4,5\},&
n=16&\colon\{6,7,10,11\},&
n=17&\colon\{1,7,8,11,12\},\\
n=18&\colon\{1,2,4,8,9,11\},&
n=26&\colon\{8,10,11,15,17,18\},\\
n=27&\colon\{1,2,5,11,12,14,18\},&
n=32&\colon\{2,3,14,15,17,22,23\}\quad(\text{size }7;\ S(6)\cup S(22)\text{ is a non-minimal maximal set of size }8),\\
n=33&\colon\{1,2,4,5,13,14,16,17\},&
n=40&\colon\{1,2,5,6,16,17,20,21\}.
\end{align*}
$$

Several of these are (translates of) one or two copies of $S(a)$, sometimes with two extra points at the left end.

**Remark 4.2.** The unique minimiser in $[16]$ is $S(6)$. For $n=17$ there are exactly two minimisers, $\{1,7,8,11,12\}$ and $\{6,7,10,11,17\}$: the unique 4-point set of $[16]$, with either endpoint of $[17]$ adjoined. Neither adjunction is forced by Lemma 3.2, which only covers up to $16$.

## 5. Counts of minimisers

Let $m(n)$ be the number of maximal 3-AP-free subsets of $[n]$ of size $\mathrm{sat}_3(n)$. Exhaustive enumeration gives, for $n\le 26$:

$$
\begin{array}{c|cccccccccccccccc}
n&1&2&3&4&5&6&7&8&9&10&11&12&13&14&15&16\\
\hline
m(n)&1&1&3&1&2&4&10&25&34&24&21&12&7&4&2&1
\end{array}
$$
$$
\begin{array}{c|cccccccccc}
n&17&18&19&20&21&22&23&24&25&26\\
\hline
m(n)&2&154&146&104&78&46&26&13&6&2.
\end{array}
$$

This sequence is also absent from OEIS (checked 2026-09-07). The spike at $n=18$, where $\mathrm{sat}_3$ jumps from $5$ to $6$, is the first $n$ at which no $5$-point maximal set exists; many $6$-point configurations then become available.

## 6. Endpoint covering

Call $t$ an *endpoint completion* of $A$ if $t=2y-x$ for distinct $x,y\in A$ with $t\notin\{x,y\}$. Write $A$ *endpoint-covers* $[lo,hi]$ if every integer of that interval lies in $A$ or is an endpoint completion of $A$. Endpoint covering of $[n]$ implies maximality in $[n]$ (midpoints are not required).

**Lemma 6.1.** Let $d\in\mathbb{Z}$. If $A$ endpoint-covers $[lo,hi]$, then $A+d$ endpoint-covers $[lo+d,hi+d]$.

*Proof.* If $t\in A$ then $t+d\in A+d$. If $t=2y-x$ then $t+d=2(y+d)-(x+d)$. Formalised as `endpoint_covers_translate`.

**Lemma 6.2.** Let $A\subseteq\mathbb{Z}$ be 3-AP-free. Then $A+d$ is 3-AP-free. Formalised as `AP3Free_shift`.

## 7. $R$-complete sets

The following definition is due to Csajbók–Nagy [2, Definition 3.1], who used it to produce complete $(2,-1)$-avoiding subsets of $\mathbb{Z}_m$. We use it on the interval $[n]$, with a placement that does not wrap around.

**Definition 7.1.** Let $R$ be a nonnegative integer. A set $A\subseteq[0,R]$ is *$R$-complete* if it is 3-AP-free and its endpoint completions fill $[-R,2R]$.

Write $I(A)=[2\min A-\max A,\,2\max A-\min A]$ for the far-endpoint interval of a finite set $A$. If $A\subseteq[0,R]$ and $0,R\in A$, then $I(A)=[-R,2R]$.

**Lemma 7.2 (placement, left).** Let $A$ be $R$-complete and let $n$ satisfy $R+1\le n\le 2R+1$. Then $A+1$ is a maximal 3-AP-free subset of $[n]$.

*Proof.* The points of $A+1$ lie in $[1,R+1]\subseteq[n]$. Freeness is Lemma 6.2. Lemma 6.1 translates the covering of $[-R,2R]$ to $[1-R,2R+1]$. The interval $[1,n]$ is contained in $[1-R,2R+1]$ because $n\le 2R+1$. Formalised as `rcomplete_place_left`.

**Lemma 7.3 (placement, right).** Let $A$ be $R$-complete and let $n$ satisfy $2R+1\le n\le 3R+1$. Then $A+(n-2R)$ is a maximal 3-AP-free subset of $[n]$.

*Proof.* Write $s=n-2R$, so $s\ge 1$. The points of $A+s$ lie in $[s,R+s]=[n-2R,n-R]\subseteq[n]$. Freeness is Lemma 6.2. Lemma 6.1 translates the covering of $[-R,2R]$ to $[n-3R,n]$. The hypothesis $n\le 3R+1$ gives $n-3R\le 1$, so $[1,n]\subseteq[n-3R,n]$. Formalised as `rcomplete_place_right`.

**Corollary 7.4.** If an $R$-complete set of size $k$ exists and $R+1\le n\le 3R+1$, then $\mathrm{sat}_3(n)\le k$.

*Proof.* If $n\le 2R+1$ use Lemma 7.2; if $n\ge 2R+1$ use Lemma 7.3. At $n=2R+1$ the two shifts coincide. Formalised as `rcomplete_place`.

The modular analogue in [2, Lemma 3.2] requires the stricter window $2R<m\le 3R+1$, because wrap-around is used to cover the left end. On the interval the left end is covered by a unit shift, so the window is longer.

## 8. Admissible digits

The next two statements are the interval form of [2, Lemma 3.3 and Corollary 3.5]. The proofs are written out so that they can be checked without the group-theoretic paper. The inductive covering step is `rcomplete_admissible_step`. The greedy digit sequence for every $R\in I_k$ is `greedyDigits_admissible`.

**Lemma 8.1.** Let $A\subseteq[0,S]$ be $S$-complete, with $S\ge 0$, and let $d$ be an integer satisfying $2S+1\le d\le 3S+1$. Then $A\cup(A+d)$ is $(S+d)$-complete.

*Proof.* Write $U=A\cup(A+d)$. The points of $U$ lie in $[0,S+d]$.

*Freeness.* The set $A$ lies in $[0,S]$ and $A+d$ lies in $[d,S+d]$ with $d\ge 2S+1$, hence $2\max A=2S<d\le\min(A+d)$. If a 3-AP has two points in $A$ and one in $A+d$, the point of $A+d$ is either $2y-x$ with $x,y\in A$, hence at most $2S$, or the middle of two points of $A$, hence at most $S$; both contradict membership in $A+d$. If it has two points in $A+d$ and one in $A$, the point of $A$ is either $2u-v$ with $u,v\in A+d$, hence at least $2d-(S+d)=d-S\ge S+1$, or the middle of two points of $A+d$, hence at least $d$; both lie to the right of $A$. Formalised as `separated_union_AP3Free`.

*Covering.* Write $I=[-S,2S]$. The endpoint completions of $U$ include the four families
$$
I-d,\qquad I,\qquad I+d,\qquad I+2d,
$$
namely $2A-(A+d)$, the given covering of $I$, its translate by $d$, and $2(A+d)-A$. Distinctness of mixed triples uses $d>2S$ as in the freeness paragraph (formalised as `mixed_left_I` and `mixed_right_I`).

These four intervals abut or overlap because $d\le 3S+1$: the right end of $I$ is $2S$ and the left end of $I+d$ is $d-S$, and $d-S\le 2S+1$ is exactly $d\le 3S+1$. The same comparison joins $I-d$ to $I$ and $I+d$ to $I+2d$. Their union is $[-(S+d),2(S+d)]$. Formalised as `admissible_shift_covers`.

**Lemma 8.2.** Let $d_1=1$ and $S_i=d_1+\cdots+d_i$. Suppose $2S_i+1\le d_{i+1}\le 3S_i+1$ for each $i=1,\dots,k-1$. Let
$$
P=\Bigl\{\sum_{i=1}^k \varepsilon_i d_i:\varepsilon_i\in\{0,1\}\Bigr\}.
$$
Then $P$ is an $S_k$-complete set of size $2^k$. Covering and freeness of the nested union $A\cup(A+d_2)\cup\cdots$ are Lean (`rcomplete_from_admissible`, iterating `rcomplete_admissible_step` from `{0,1}`). Distinctness of the nested doubling is Lean (`nodup_growFrom`): $P\subseteq[0,S]$ and $d\ge 2S+1$ force $P$ and $P+d$ to be disjoint, so the grown list is duplicate-free. The greedy nested union is exactly that list (`greedy_set_iff`) of length $2^k$ (`greedy_growFrom_length`).

*Proof.* *Distinctness.* Nested doubling: if $P\subseteq[0,S]$ is duplicate-free and $d\ge 2S+1$, then $P$ and $P+d$ are disjoint, so $|P\cup(P+d)|=2|P|$. Formalised as `nodup_growFrom`. (Equivalently, a nonempty signed sum $\sum\delta_i d_i=0$ with $\delta_i\in\{-1,0,1\}$ is impossible: the largest nonzero coefficient has size $d_j>S_{j-1}$.)

*Freeness and covering.* Iterate Lemma 8.1 from $\{0,1\}$. Formalised as `rcomplete_from_admissible`. The greedy nested union is exactly the grown list (`greedy_set_iff`) of length $2^k$ (`greedy_growFrom_length`).

Write
$$
I_k=\Bigl[\tfrac{3^k-1}{2},\,\tfrac{4^k-1}{3}\Bigr]\cap\mathbb{Z},
$$
and $\ell_k=(3^k-1)/2$, $u_k=(4^k-1)/3$, so $I_k=[\ell_k,u_k]$.

**Corollary 8.3.** For every $k\ge 1$ and every integer $R\in I_k$ there exists an $R$-complete set of size $2^k$.

*Proof.* Construct digits by downward induction. For $k=1$, $I_1=\{1\}$ and $d_1=1$. Given $R\in I_{k+1}$, set
$$
S=\min\bigl(u_k,\,\lfloor(R-1)/3\rfloor\bigr),\qquad d=R-S.
$$
Then $S\in I_k$ and $2S+1\le d\le 3S+1$. Indeed $S\le u_k$ by construction, while $R\ge \ell_{k+1}=3\ell_k+1$ forces $\lfloor(R-1)/3\rfloor\ge \ell_k$, hence $S\ge \ell_k$. The lower digit bound is $3S\le R-1$. For the upper bound: if $S=u_k$ then $R\le u_{k+1}=4u_k+1=4S+1$; if $S=\lfloor(R-1)/3\rfloor$ then $R\le 3S+3$, and $3S+3\le 4S+1$ once $S\ge 2$. The remaining case $k=1$ has $I_2=\{4,5\}$ and $S=1=u_1$, so it falls in the first alternative. Formalised as `greedyPred_spec` (`k=1` by computation on $I_2=\{4,5\}$; `k\ge 2` from $\ell_k\ge 4$). The inductive hypothesis supplies an admissible sequence for $S$; adjoining $d$ yields one for $R$. Formalised as `greedyDigits_admissible`. Iterating the one-step covering along that list yields an $R$-complete set (`greedy_rcomplete`). The nested union is a duplicate-free list of length $2^k$ (`greedy_growFrom_nodup`, `greedy_growFrom_length`, `greedy_set_iff`). Implemented in `scripts/rcomplete.py`.

(The same recurrence also shows that the attainable sums fill $I_k$: each $S\in I_k$ contributes the block $[3S+1,4S+1]$, consecutive blocks meet once $S\ge 2$ because $3S+4\le 4S+2$ (`consecutive_images_overlap`), and after $k=1$ one has $S\ge 4$. This overlapping-union picture is not used below.)

The extreme choice $d_i=4^{i-1}$ recovers the base-$4$ subset sums of Csajbók–Nagy [1, 2]: then $S_k=(4^k-1)/3$ and $d_{k+1}=3S_k+1$.

## 9. Every $n$

**Lemma 9.1.** Let $n\ge 2$ and let $k\ge 1$ be the integer with $4^{k-1}<n\le 4^k$. Then $R=\max\bigl(\ell_k,\,\lceil(n-1)/3\rceil\bigr)$ lies in $I_k$ and satisfies $R+1\le n\le 3R+1$.

*Proof.* The comparison $\ell_k\le u_k$ is `Ilo_le_Ihi`. The identity $4^k=3u_k+1$ is `four_pow_Ihi`, so $n\le 4^k$ gives $\lceil(n-1)/3\rceil\le u_k$. Thus $R\le u_k$. The identity $3^k=2\ell_k+1$ is `three_pow_Ilo`. The inequality $3^k\le 2\cdot 4^{k-1}+1$ is `lower_window`, hence $\ell_k+1\le 4^{k-1}+1\le n$. Also $\lceil(n-1)/3\rceil+1\le n$ for $n\ge 2$. Thus $R+1\le n$. Finally $3\lceil(n-1)/3\rceil\ge n-1$, so $n\le 3R+1$. Formalised as `chosenR_window`.

**Theorem 9.2.** For every integer $n\ge 2$,
$$
\mathrm{sat}_3(n)\le 2^k<2\sqrt{n},
$$
where $k$ is defined by $4^{k-1}<n\le 4^k$. For $n=1$ one has $\mathrm{sat}_3(1)=1<2$.

*Proof.* Lemma 9.1 supplies $R\in I_k$ with $R+1\le n\le 3R+1$. Corollary 8.3 supplies an $R$-complete set of size $2^k$. Corollary 7.4 places it into $[n]$, so $\mathrm{sat}_3(n)\le 2^k$. Since $n>4^{k-1}$ one has $(2^k)^2=4^k=4\cdot 4^{k-1}<4n$, hence $2^k<2\sqrt{n}$. Formalised as `sat3_theta` for every $n\ge 1$: `HasMaximalOfSize n (sat3Upper n)` with `sat3Upper 1 = 1` and `sat3Upper n = 2^k` for $n\ge 2$, together with $(2^k)^2<4n$ when $n\ge 2$, and $2n\le 3k^2$ for every maximal set of size $k$. The construction is `sat3_construction`. The numerical function is the Lean `sat3 n` (`sat3_spec`, `sat3_le_upper`, `sat3_sq_lt`).

Theorem 1.1 is Theorem 9.2 together with Proposition 2.2. Formalised as `sat3_theta_num`: $\mathrm{sat}_3(n)\le\mathrm{sat3Upper}(n)$, $2n\le 3\,\mathrm{sat}_3(n)^2$, and $\mathrm{sat}_3(n)^2<4n$ when $n\ge 2$. The one-step inequality is `sat3_succ_le`. Exact values through $n=40$ are `sat3_eq_one`..`sat3_eq_forty`.

**Lemma 9.4.** $\mathrm{sat}_3(n+1)\le\mathrm{sat}_3(n)+1$.

*Proof.* Let $A$ be maximal 3-AP-free in $[n]$. If $n+1$ is already an endpoint completion of $A$, then $A$ remains maximal in $[n+1]$. Otherwise $A\cup\{n+1\}$ is 3-AP-free (a 3-AP through $n+1$ would be an endpoint completion) and covers $[n+1]$. Formalised as `maximal_extend_right`, `HasMaximalOfSize_succ`, and `sat3_succ_le`.

**Corollary 9.5.** For $k\ge 1$ and $t\ge 0$,
$$
\mathrm{sat}_3(4^k+t)\le 2^k+t.
$$
In particular $\mathrm{sat}_3(5)\le 3$ and $\mathrm{sat}_3(17)\le 5$. Formalised as `sat3_le_interp`, `sat3_le_five`, `sat3_le_seventeen_num`. The pair bound at $n=5$ only forces $k\ge 2$ (`pairBound 2=5`). Exactness $\mathrm{sat}_3(5)=3$ is `sat3_eq_five`.

Walking $t$ steps from $4^k$ is linear. It improves the construction $2^{k+1}$ only for $t<2^k$, a $\Theta(\sqrt{n})$ neighbourhood of each $4^k$, and does not improve the global constant $2$ in Theorem 9.2.

**Remark 9.6.** The implicit constants are $\sqrt{2/3}\le \mathrm{sat}_3(n)/\sqrt{n}<2$. Along $n=4^k$ the construction uses $2^k=\sqrt{n}$ points, so the upper constant $2$ is an artefact of the worst $n$ just after a power of $4$. For $n\le 40$ the construction size equals $\mathrm{sat}_3(n)$ at every $n=4^k$ in the table ($n=1,4,16$), and also throughout $n=6..16$ and $n=33..40$. Just after each power of $4$, Corollary 9.5 is tighter than Theorem 9.2 ($n=5,17$). No attempt is made here to optimise the constant.

## 10. A weaker Cantor construction

The following statements were the previous upper bound. They are correct and are recorded for comparison. They are not used in Theorem 9.2.

Let $T=\{0,1,4,5\}$ and let $B$ be the nonnegative integers whose ternary digits lie in $\{0,1\}$. Let $\mathcal{A}=\bigcup_{b\in B}S(6+11b)$. Then $\mathcal{A}$ is 3-AP-free: a 3-AP rearranges to $2t-t'-t''=11(b'+b''-2b)$ with left side in $[-10,10]$, so both sides vanish, and $B$ and $T$ are degenerate. Write $B_k=B\cap[0,3^k)$ and $\mathcal{A}_k=\bigcup_{b\in B_k}S(6+11b)$, $L_k=11\cdot 3^k+5$.

If $A\subseteq[1,d+5]$ endpoint-covers $[1,d+5]$ and $d>0$, then $A\cup(A+d)$ endpoint-covers $[1,3d+5]$ (formalised as `mixed_fills_right`). The Cantor recurrence $\mathcal{A}_{k+1}=\mathcal{A}_k\cup(\mathcal{A}_k+11\cdot 3^k)$ therefore yields that $\mathcal{A}_k$ is maximal 3-AP-free in $[L_k]$, hence $\mathrm{sat}_3(L_k)\le 4\cdot 2^k=O(L_k^{\log_3 2})$. A one-point repair at the two residues $n=c(n)+3,c(n)+4$ of the last centre extends the bound to every $n$, still of order $n^{\log_3 2}$.

Base-$4$ centres are the right-hand extreme of Lemma 8.2 and already give $O(\sqrt{n})$ on each interval $[\max\mathcal{A}_k^{(4)},\,2\max-\min]$, a positive-density set of $n$. The complementary gaps are of length $\Theta(4^k)$. Those gaps are filled by the variable digits of Lemma 8.2, not by a one-point repair.

## 11. What is formalised

Lean 4 project `lean/`, no mathlib, no `sorry`.

Proved:

- `S_AP3Free`, `S0_covers`, `S_covers_interval`, `S6_maximal_16`, `twoBlocks_maximal_32`, `twoBlock_covers_11`..`16`
- `pairBound_double`, `pairBound_half`, `pairBound_quadratic`, `pairBound_of_maximal`, `HasMaximalOfSize_pairBound`
- `T_degenerate`
- `endpoint_covers_translate`, `mixed_fills_right`
- `IsRComplete`, `rcomplete_01`
- `separated_union_AP3Free`, `mixed_left_I`, `mixed_right_I`, `admissible_shift_covers`, `rcomplete_admissible_step`
- `rcomplete_place_left`, `rcomplete_place_right`
- `Ilo`, `Ihi`, `Ilo_le_Ihi`, `four_pow_Ihi`, `three_pow_Ilo`, `lower_window`
- `two_pow_sq_lt`, `chosenR_window`
- `greedyPred_spec`, `admissible_sum_in_I`, `consecutive_images_overlap`
- `greedyDigits`, `greedyDigits_length`, `greedyDigits_sum`, `greedyDigits_last_admissible`, `greedyDigits_admissible`
- `rcomplete_from_admissible`, `greedy_rcomplete`, `greedy_subsetSums_length`, `buildFrom_spec`, `greedy_support`
- `nodup_growFrom`, `greedy_growFrom_nodup`, `greedy_growFrom_length`, `greedy_set_iff`
- `rcomplete_place`, `placedGreedy_maximal`, `placedGreedy_iff`, `windowK_spec`, `sat3_construction`, `sat3_upper`, `HasMaximalOfSize`, `HasMaximalOfSize_one`, `sat3Upper`, `sat3_O_sqrt`, `sat3_theta`
- `pairBound_mono`, `HasMaximalOfSize_ge`, `sat3_exact_when_pin`, `sat3_exact_1`..`4`, `sat3_exact_13`..`16`
- `maximal_extend_right`, `HasMaximalOfSize_succ`, `Sat3Le`, `Sat3Le_succ`, `sat3_interp`, `sat3_le_five`, `sat3_le_seventeen`
- `not_maximal_pair_five`, `not_HasMaximalOfSize_5_2`, `sat3_exact_5`
- `exists_least_maximal`, `sat3_min`, `sat3_min_O_sqrt`, `sat3`, `sat3_spec`, `sat3_le_upper`, `sat3_sq_lt`, `sat3_succ_le`, `sat3_theta_num`
- `sat3_eq_one`..`sat3_eq_forty`, `sat3_le_interp`, `sat3_le_seventeen_num`
- `anyMaximal3_6`..`12`, `anyMaximal4_17`, `anyMaximalInc` (increasing tuples), `anyMaximalFree` (3-AP-free tuples), `anyMaximalSearch` (DFS), `sat3_eq_eighteen`..`forty`
- boolean certificates `cert_n*` and `maximal_of_cert_n*` for the table witnesses of Theorem 4.1. The checker is equivalent to maximality: `maximal_iff` (`maximal_sound` and `maximal_complete`)

Not formalised (paper proofs, marked above):

- a computable closed form for $\mathrm{sat}_3(n)$. Lean has a noncomputable `sat3 n`. Exact values through $n=40$ are Lean (`native_decide` on the enumerators above).
- the Cantor arguments of §10, except `mixed_fills_right`

## References

[1] B. Csajbók and Z. L. Nagy, Complete $3$-term arithmetic progression free sets of small size in vector spaces and other abelian groups, arXiv:2401.06283.

[2] B. Csajbók and Z. L. Nagy, Small complete $3$-term progression free sets in cyclic groups and vector spaces, arXiv:2606.30186.

[3] S. Savchev and F. Chen, A note on maximal progression-free sets, Discrete Math. 306 (2006), 2131–2133.

[4] OEIS Foundation, Sequence A003002, $r_3(n)$; Sequence A003278, integers with ternary digits in $\{0,1\}$.

[5] Y. G. Chen, On $AP_3$-covering sequences, C. R. Math. 356 (2018), 121–124.

[6] J. H. Fang, A note on $AP_3$-covering sequences, Period. Math. Hungar. 83 (2021), 67–70.

[7] S. Z. Kiss, C. Sándor, and Q.-H. Yang, On generalized Stanley sequences, arXiv:1710.01939. They introduce $AP_3$-covering sequences (saturating, not necessarily 3-AP-free).
