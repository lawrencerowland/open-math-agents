"""Enumerate labelled five-activity union-closed families with full support.
Every nonempty scope contains at least three activities. The empty scope is optional.
A candidate partner is a scope containing the target and containing the source.
"""
from collections import Counter
from itertools import combinations


def families(n=5):
    top = (1 << n) - 1
    if n < 3:
        return
    scopes = [x for x in range(top) if x == 0 or bin(x).count('1') >= 3]
    for size in range(len(scopes) + 1):
        for part in combinations(scopes, size):
            family = set(part) | {top}
            if all(x | y in family for x, y in combinations(part, 2)):
                yield family


def matching(neighbors):
    used = {}
    def augment(x, seen):
        for y in neighbors[x]:
            if y in seen:
                continue
            seen.add(y)
            if y not in used or augment(used[y], seen):
                used[y] = x
                return True
        return False
    return all(augment(x, set()) for x in neighbors)


def class_of(family, a):
    left = sorted(x for x in family if not x & a)
    right = sorted(family.difference(left))
    if len(right) < len(left):
        return 0
    if any(len({x | m for x in left}) == len(left) for m in right):
        return 4
    for b in [1, 2, 4, 8, 16]:
        if b == a:
            continue
        if all(any((flag or not m & b) and len({x | m for x in group}) == len(group)
                   for m in right)
               for flag, group in [(v, [x for x in left if bool(x & b) == v]) for v in [False, True]]):
            return 3
    if matching({x: [y for y in right if x | y == y] for x in left}):
        return 2
    return 1


if __name__ == '__main__':
    for n in range(3, 6):
        total = 0
        for family in families(n):
            assert any(matching({x: [y for y in family if y & a and x | y == y]
                                 for x in family if not x & a}) for a in [1 << i for i in range(n)])
            total += 1
        print(f'{n} activities: containment matching exists for some target in all {total} families')
    pairs, groups = Counter(), Counter()
    first = {}
    for family in families():
        scores = [class_of(family, 1 << i) for i in range(5)]
        pairs.update(scores)
        groups[max(scores)] += 1
        for i, score in enumerate(scores):
            first.setdefault(score, (sorted(family), i))
    print('Exclusive categories: 0 below half, 1 frequent without monotone matching,')
    print('2 monotone matching, 3 binary marker, 4 single package')
    print('Designated pairs:', sorted(pairs.items()))
    print('Families by best designated element:', sorted(groups.items()))
    print('First witnesses by designated-pair category:', first)
