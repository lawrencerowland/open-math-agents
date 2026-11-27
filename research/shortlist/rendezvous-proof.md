# A 22-step upper bound for symmetric rendezvous on a line

Two agents start two units apart on a line, move at speed at most one, and have no shared direction. They use identical instructions, private randomness and a common start time. For this model the policy below has expected meeting time

\[
\frac{4251064913301365857}{999154247600840430}=4.254663304999\ldots.
\]

Han, Du, Vera and Zuluaga reported an upper bound of 4.2574 and conjectured a value of 4.25. This construction improves on their reported upper bound. Optimality and the conjectured value remain open. [Operations Research paper](https://doi.org/10.1287/opre.1070.0439) · [Author-hosted manuscript](https://pure.uvt.nl/ws/files/1303232/improved_bounds.pdf)

## Policy

At the beginning of every 22-step block, each agent independently chooses a fair local forward direction and draws one row of `rendezvous-22.tsv`, with probability proportional to its positive integer weight. The agent follows the row, one unit per letter, F forward and B backward. Both agents stop at the first meeting. If no meeting occurs, they independently draw again. Each word has eleven of each letter, so both agents have returned to their own starting points. The block's movement never uses information about the other agent.

The table has 1,178 distinct words of total weight 1,000,000,007. Its SHA-256 digest is `f15c8fa331249ff637c629c186cfe5524118c0fc381a5ed76b44767715049bdd`.

## Exact first-passage calculation

Place the agents initially at 0 and 2. Write a and b for their signed displacements. At integer times both have the parity of the time. The physical gap starts at two and changes by zero or two in magnitude per unit step. Its first arrival at zero must be at an integer time, including when trajectories are followed continuously between ticks. A signed prefix pair survives through t exactly when a(s) ≤ b(s) at every integer s up to t.

Let S(t) be the total integer weight of all ordered signed word pairs that survive through t. In particular,

- S(0) = 4000000056000000196.
- S(22) = 3383065596638476.
- The sums treat each sign for each chosen word as a separate equally weighted option.

One block has expected elapsed time equal to the sum of its survival probabilities from t=0 through 21. On failure, the conditional expected remaining time equals the original expectation, since the agents return home and redraw. Thus

\[
E[T]=\frac{\sum_{t=0}^{21} S(t)}{S(0)-S(22)}.
\]

The denominator is positive, so eventual meeting has probability one. The reported rational is the evaluation of this identity with integers only.

Two standard-library Python programs give independent checks. From the directory containing the files, run

```
python3 check_rendezvous.py rendezvous-22.tsv
python3 check_rendezvous_survival.py rendezvous-22.tsv
```

The first tests the four sign combinations for every unordered pair of words, counting off-diagonal word pairs twice. Reflection about the initial midpoint proves the symmetry used in that count. The second constructs a tree of all signed prefixes and propagates only pairs whose full histories have survived. Prefix weights include every possible continuation.

## Comparison and discovery

The two-step out-and-back baseline has a one-quarter chance of meeting at time one. A missed block costs two; the expected time is seven. Alpern's three-step FBB strategy gives five: with fresh independent signs, it meets at time one or three with probability one quarter each. In the remaining half of cases the agents move in the same direction throughout and remain two units apart.

The 22-step table was found by a heuristic search over distributions of closed paths. For each block length the search adjusted the probabilities on an active set and proposed alternative paths by exchanging a forward and backward step. It grew from four steps to 22 in increments of two, using the previous policy to start the next search. Approximate weights were rounded to integers before the exact calculation. Only the final integer policy is needed for the upper bound.
