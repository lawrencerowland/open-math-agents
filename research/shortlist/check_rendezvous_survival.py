"""Independent exact verifier using weighted prefixes and survival probabilities.

The agents start at 0 and 2. All displacements at time t have parity t.
Until a meeting, left displacement <= right displacement. At a first violation
their physical positions coincide. All submitted words must return home.
"""
from collections import defaultdict
from fractions import Fraction
from pathlib import Path
import sys


def verify(path):
    rows = [line.split() for line in path.read_text().splitlines()]
    n = len(rows[0][0])
    children = [{}]
    masses = [0]
    heights = [0]
    for word, units in rows:
        weight = int(units)
        assert len(word) == n and set(word) <= {"F", "B"} and weight > 0
        assert word.count("F") == word.count("B")
        for sign in (-1, 1):
            parent = 0
            masses[parent] += weight
            for symbol in word:
                step = sign if symbol == "F" else -sign
                if step not in children[parent]:
                    children[parent][step] = len(masses)
                    masses.append(0)
                    children.append({})
                    heights.append(heights[parent] + step)
                parent = children[parent][step]
                masses[parent] += weight

    active = [(0, 0)]
    survival = [masses[0]**2]
    for _ in range(n):
        following = []
        count = 0
        for i, j in active:
            for a in children[i].values():
                for b in children[j].values():
                    if heights[a] <= heights[b]:
                        following.append((a, b))
                        count += masses[a] * masses[b]
        active = following
        survival.append(count)
    assert all(a >= b for a, b in zip(survival, survival[1:]))
    return Fraction(sum(survival[:-1]), survival[0] - survival[-1]), survival


if __name__ == "__main__":
    expectation, survival = verify(Path(sys.argv[1]))
    print("E[T] =", expectation, "=", f"{float(expectation):.12f}")
    print("Survival weights from t=0 to block end:", *survival)
