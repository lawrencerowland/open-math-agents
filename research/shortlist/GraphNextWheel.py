"""Complete labelled enumeration of the six-activity wheel puzzle, Python 3."""

from collections import Counter
from itertools import combinations, permutations

VERTICES = range(6)
EDGES = list(combinations(VERTICES, 2))
INDEX = {edge: i for i, edge in enumerate(EDGES)}
INCIDENT = [sum(1 << i for i, edge in enumerate(EDGES) if v in edge)
            for v in VERTICES]


def edge_mask(edges):
    return sum(1 << INDEX[tuple(sorted(edge))] for edge in edges)


def wheel_labellings():
    labelled = set()
    for hub, *rim in permutations(VERTICES):
        spokes = [(hub, v) for v in rim]
        cycle = list(zip(rim, rim[1:] + rim[:1]))
        labelled.add(edge_mask(spokes + cycle))
    return labelled


def check():
    expected = wheel_labellings()
    matches = set()
    for mask in range(1 << len(EDGES)):
        card_sizes = Counter(bin(mask & ~inc).count("1") for inc in INCIDENT)
        if card_sizes == {5: 1, 7: 5}:
            matches.add(mask)
    assert matches == expected
    print(f"{1 << len(EDGES)} labelled graphs; {len(matches)} matches; one isomorphism class.")


if __name__ == "__main__":
    check()
