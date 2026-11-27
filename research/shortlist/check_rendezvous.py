"""Verify an explicit symmetric block policy with integer arithmetic.

Usage: python3 check_rendezvous.py rendezvous-22.tsv
Each row is a word in F/B and a positive integer sampling weight. Both agents
choose a word and an independent random orientation anew at every block.
"""
from collections import Counter
from fractions import Fraction
from itertools import accumulate, product
from pathlib import Path
import sys


def load_policy(path):
    rows = []
    for line in path.read_text().splitlines():
        word, weight = line.split()
        assert word and set(word) <= {"F", "B"} and int(weight) > 0
        positions = tuple(accumulate(1 if symbol == "F" else -1 for symbol in word))
        rows.append((positions, int(weight)))
    assert rows and len({len(positions) for positions, _ in rows}) == 1
    assert len({positions for positions, _ in rows}) == len(rows)
    return rows


def evaluate(rows):
    """Count first hits among ordered independent word and sign choices."""
    n = len(rows[0][0])
    counts = Counter()
    for i, (left, wi) in enumerate(rows):
        for j in range(i + 1):
            right, wj = rows[j]
            # Reflection across the initial midpoint exchanges the two words
            # and changes both signs. The four signs account for either order.
            mass = wi * wj * (1 if i == j else 2)
            for a, b in product((-1, 1), repeat=2):
                for t, (x, y) in enumerate(zip(left, right), 1):
                    if a*x == 2 + b*y:
                        counts[t] += mass
                        break
                else:
                    # A fresh block is valid only if failures preserve separation.
                    assert abs(2 + b*right[-1] - a*left[-1]) == 2
                    counts[None] += mass
    weight = 4 * sum(w for _, w in rows)**2
    assert sum(counts.values()) == weight
    failures = counts[None]
    hit_weight = weight - failures
    assert hit_weight > 0
    elapsed = n * failures + sum(t * c for t, c in counts.items() if t is not None)
    return Fraction(elapsed, hit_weight), Fraction(failures, weight), counts


if __name__ == "__main__":
    path = Path(sys.argv[1])
    rows = load_policy(path)
    expectation, failure, _ = evaluate(rows)
    print(f"{len(rows)} words, {len(rows[0][0])} steps, total weight {sum(w for _, w in rows)}")
    print(f"E[T] = {expectation} = {float(expectation):.12f}")
    print(f"failure probability = {failure} = {float(failure):.12f}")
