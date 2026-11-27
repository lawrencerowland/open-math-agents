# From the 22-step certificate to the continuous-path value

Take the start positions to be 0 and 2. A local route starts at 0, is continuous in nonnegative time and has Lipschitz constant at most one. The route space carries the Borel σ-algebra of the compact-open topology, as in `RendezvousStatement.lean`.

## Measurability of the first meeting time

Fix two signs a and b in {−1,1}. For local routes f and g put h(s) = 2 + b g(s) − a f(s), and let T be the infimum of its zero set, with the infimum of the empty set equal to infinity. The zero set is closed. If T is finite it is attained.

For each finite u ≥ 0, T ≤ u if and only if, for every integer j ≥ 1, there is a nonnegative rational q ≤ u with |h(q)| < 1/j. For the forward implication, use continuity and the density of the rationals in [0,u], including approximation of the right endpoint from the left. At u = 0 use q = 0. Conversely, compactness of [0,u] supplies a convergent subsequence of any such rational approximants, and its limit is a zero.

For fixed q, evaluation at q is continuous in the compact-open topology. Hence each displayed test is measurable for the product of the two route σ-algebras. Countable unions and intersections show that T is extended-real measurable. This proof works directly for the product σ-algebra used by the product measure. Averaging the four extended nonnegative meeting times gives a measurable integrand.

## One admissible law on the route space

Let N = 22. Independently for each player and each block, sample a word w with probability weight(w)/1,000,000,007 and a fair private sign ε. During that block use the successive velocities ε times the word's signed letters. Each block returns to its starting point. Linear interpolation produces a continuous path starting at 0, and the unit speed bound on each linear segment gives the global one-Lipschitz bound by subdivision of every finite time interval.

Equip the finite alphabet of (word, sign) with the discrete topology. The map from an infinite sequence of letters of this alphabet to a route is continuous in the product and compact-open topologies. Agreement on the first k symbols gives identical paths on [0,kN], and every compact time set lies in such an interval. The image law μ of the iid product measure is therefore a Borel probability law on routes.

The two players use independent copies of μ. Nature can supply each player with a fair orientation sign fixed for the entire run. Conditional on any of the four choices by Nature, the global signs in successive blocks are the private iid signs multiplied by two fixed constants. Their joint law is unchanged. Thus the four-orientation average used by `expectedTime` is exactly the expectation computed for independent oriented words. The only common information used by the players is the deterministic block length and their common starting time.

## The exact expectation

For each tick t of one block, let S_t be the integer weight of oriented ordered pairs that have survived through t, and D = S_0 = 4(1,000,000,007)². The gap starts at 2 and changes by 0 or ±2 at each tick. All gaps at ticks are even. Linear interpolation can produce a first meeting only at an integer tick. If L(s) and R(s) count positive steps of the left and right players, survival through t is equivalent to L(s) ≤ R(s) for every integer s ≤ t.

The independent checker `check_rendezvous_dominance.py` computes these weighted dominance relations for sets of right-hand paths simultaneously. It gives D = 4,000,000,056,000,000,196, S_22 = 3,383,065,596,638,476 and Σ_{0≤t<22} S_t = 17,004,259,653,205,463,428. Both players return home on every unsuccessful block. Future private draws are independent of past failures.

For k ≥ 0 and 0 ≤ t < 22, P(T > 22k+t) = (S_22/D)^k S_t/D. The hit probability per block is positive. Summing these tails gives

```
E[T] = (Σ_{0≤t<22} S_t)/(D − S_22)
     = 4,251,064,913,301,365,857 / 999,154,247,600,840,430
     = 4.254663304999185…
```

The infimum over all Borel probability laws is at most this value. The calculation leaves the conjecture that this infimum equals 17/4 open. The argument above is a mathematical bridge; the available Lean statement and integer checker do not constitute a kernel proof of the measure-theoretic inequality.

## Comparison

Han, Du, Vera and Zuluaga's Table 2 in the SODA version of *Improved bounds for the symmetric rendezvous value on the line* gives 4.2574 for 15-step blocks using 128 generators. Their Remark 3.3 says explicitly that the table retains four decimal places. The refereed Operations Research abstract also gives 4.2574. The difference from that printed number is approximately 0.002736695. The certificate is an upper bound on the classic two-unit-distance problem with identical independent strategies. It leaves mathematical priority and optimality separate.

- [Table 2, Equation (3.2) and Remark 3.3](https://pure.uvt.nl/ws/files/1303232/improved_bounds.pdf)
- [Han et al., Operations Research 56 (2008), 772–782](https://doi.org/10.1287/opre.1070.0439)
