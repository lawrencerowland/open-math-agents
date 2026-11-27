"""Verify the anonymous deck by examining every simple graph on five labels."""
from itertools import combinations, permutations

def canonical(vertices, edges):
    return min(tuple(frozenset((a, b)) in edges for a, b in combinations(order, 2))
               for order in permutations(vertices))

def graph(pairs):
    return {frozenset(pair) for pair in pairs}

def deck(edges):
    return tuple(sorted(canonical([v for v in range(5) if v != removed], edges)
                        for removed in range(5)))

def main():
    four = range(4)
    path = canonical(four, graph([(0, 1), (1, 2), (2, 3)]))
    paw = canonical(four, graph([(0, 1), (1, 2), (2, 0), (0, 3)]))
    diamond = canonical(four, graph([(0, 1), (1, 2), (2, 3), (3, 0), (0, 2)]))
    target = tuple(sorted([path, paw, paw, diamond, diamond]))
    pairs = list(combinations(range(5), 2))
    matches = [g for mask in range(2 ** len(pairs))
               if deck(g := graph(e for i, e in enumerate(pairs) if mask >> i & 1)) == target]
    shapes = {canonical(range(5), g) for g in matches}
    gem = graph([(0, 1), (1, 2), (2, 3), (0, 4), (1, 4), (2, 4), (3, 4)])
    assert shapes == {canonical(range(5), gem)}
    assert len(matches) == 60
    print("1024 labelled graphs checked; 60 matches; 1 isomorphism class (the gem).")

if __name__ == "__main__":
    main()
