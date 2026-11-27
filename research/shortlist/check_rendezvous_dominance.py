"""Recompute a closed-block rendezvous bound by finite weighted path dominance.

For two walks starting at 0 and 2, let L(t), R(t) count their positive steps
by tick t. The gap is 2(1 + R(t) - L(t)). Survival through t is equivalent
to L(s) <= R(s) for all s <= t, since the gap in half-units changes by at
most one. For each possible left walk, track the entire set of possible
surviving right walks as a bitset, and compute its integer weight by bit planes.
"""
from argparse import ArgumentParser
from collections import defaultdict
from fractions import Fraction
from hashlib import sha256
from pathlib import Path


def survival_weights(words):
    if not words or len(dict(words)) != len(words):
        raise ValueError("Expected a nonempty list of distinct words")
    n = len(words[0][0])
    oriented = []
    for word, weight in words:
        if (len(word) != n or not word.startswith("F") or weight <= 0
                or set(word) - {"F", "B"} or 2 * word.count("F") != n):
            raise ValueError("Expected positive integer weights and closed canonical words of equal length")
        for forward in "FB":
            increments = tuple(int(step == forward) for step in word)
            oriented.append((increments, weight))
    weights = [w for _, w in oriented]
    total = sum(weights)
    planes = [sum(1 << i for i, w in enumerate(weights) if w & (1 << k))
              for k in range(max(weights).bit_length())]
    popcount = getattr(int, "bit_count", lambda x: bin(x).count("1"))

    def weight(mask):
        return sum(popcount(mask & plane) << k for k, plane in enumerate(planes))

    count = len(oriented)
    survivors = [(1 << count) - 1] * count
    heights = [0] * count
    result = [total ** 2]
    for step in range(n):
        at_height = [0] * (step + 2)
        for i, (word, _) in enumerate(oriented):
            heights[i] += word[step]
            at_height[heights[i]] |= 1 << i
        for level in reversed(range(len(at_height) - 1)):
            at_height[level] |= at_height[level + 1]
        # All right words satisfying the new dominance constraint survive if
        # and only if they already satisfied all earlier prefix constraints.
        grouped = defaultdict(int)
        for i, left_weight in enumerate(weights):
            survivors[i] &= at_height[heights[i]]
            grouped[survivors[i]] += left_weight
        result.append(sum(left_weight * weight(mask) for mask, left_weight in grouped.items()))
    assert result[0] == sum(w for _, w in words) ** 2 * 4
    assert all(a >= b for a, b in zip(result, result[1:]))
    return result


def audit(path):
    words = []
    data = path.read_bytes()
    for line in data.decode("ascii").splitlines():
        word, weight = line.split()
        words.append((word, int(weight)))
    survival = survival_weights(words)
    hit = survival[0] - survival[-1]
    if hit <= 0:
        raise ValueError("This strategy never meets")
    # An uncompleted closed block puts both players at their original locations.
    # Each player chooses a fresh independent word and orientation for each block.
    mean = Fraction(sum(survival[:-1]), hit)
    print(path.name, "support", len(words), "sum weights", sum(w for _, w in words))
    print("sha256", sha256(data).hexdigest())
    print("survival masses", *survival)
    print("block hit mass", hit, "charged time mass", sum(survival[:-1]))
    print("mean", mean, float(mean))
    return mean


if __name__ == "__main__":
    parser = ArgumentParser(description=__doc__)
    parser.add_argument("tsv", nargs="+", type=Path)
    args = parser.parse_args()
    assert survival_weights([("FB", 1)]) == [4, 3, 3]  # (4+3)/(4−3) = 7
    assert survival_weights([("FBBF", 1)]) == [4, 3, 3, 2, 2]  # (4+3+3+2)/2 = 6
    for file in args.tsv:
        audit(file)
