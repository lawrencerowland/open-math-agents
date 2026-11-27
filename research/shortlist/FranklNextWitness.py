"""Replay the one-marker certificate on five labelled activities.

A family has full support and is union-closed, so it contains the full set.
All nonempty members of these families have size at least three. Bit i
represents activity i. Running the file checks the published counts and the
six-member example by an exhaustive search.
"""
from itertools import combinations

ACTIVITIES = (1, 2, 4, 8, 16)
FULL = 31


def separates(sources, package):
    return len({source | package for source in sources}) == len(sources)


def witnesses(family, target):
    absent = [x for x in family if not x & target]
    packages = [m for m in family if m & target]
    if any(separates(absent, m) for m in packages):
        return True, None
    for marker in ACTIVITIES:
        if marker == target:
            continue
        low = [x for x in absent if not x & marker]
        high = [x for x in absent if x & marker]
        if not low or not high:
            continue
        for lo in packages:
            if lo & marker or not separates(low, lo):
                continue
            for hi in packages:
                if separates(high, hi):
                    return False, (marker, lo, hi)
    return False, None


def main():
    allowed = [x for x in range(32) if x == 0 or bin(x).count("1") >= 3]
    families = old_families = extra_families = 0
    old_targets = extra_targets = 0
    residual = set()
    for mask in range(1 << len(allowed)):
        family = frozenset(x for i, x in enumerate(allowed) if mask >> i & 1)
        if FULL not in family or any(x | y not in family for x, y in combinations(family, 2)):
            continue
        families += 1
        has_single = has_marker = False
        for target in ACTIVITIES:
            single, marker = witnesses(family, target)
            old_targets += single
            extra_targets += bool(marker)
            has_single |= single
            has_marker |= bool(marker)
        old_families += has_single
        extra_families += has_marker and not has_single
        if not (has_single or has_marker):
            residual.add(family)

    assert (families, old_families, extra_families) == (9890, 9734, 154)
    assert (families * 5, old_targets, extra_targets) == (49450, 31575, 8020)
    assert residual == {frozenset(allowed), frozenset(allowed) - {0}}
    sample = {0, 7, 26, 27, 30, 31}
    assert all(x | y in sample for x, y in combinations(sample, 2))
    assert not witnesses(sample, 1)[0]
    assert {x: x | (27 if x & 8 else 7) for x in sample if not x & 1} == {
        0: 7, 26: 27, 30: 31
    }
    print("Full-support families, one package, additional by marker:",
          families, old_families, extra_families)
    print("Designated targets, one package, additional by marker:",
          families * 5, old_targets, extra_targets)
    print("Residual families: all size-at-least-three sets, with or without the empty set.")


if __name__ == "__main__":
    main()
