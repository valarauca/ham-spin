"""Check the K_10 rank statements of Remark 7.15 and Theorem 8.7.

For a family of perfect matchings F_1, ..., F_k of {0, ..., 9}, this script
builds the k x 945 matrix (H[F_t, P])_{t, P} over F_2, where H[F, P] = 1
exactly when F and P form a Hamiltonian pair (the union F u P is one
10-cycle). Its rows are the fingerprints phi(F_t), so its rank is dim R(F).

Two families are checked:

* the perfect 1-factorization of K_10 listed in Remark 7.15, expected rank 8,
  with every row sum of the matrix equal to 0 over F_2;
* the round-robin factorization GK_10 on Z/9 u {oo}, with oo written as 9,
  expected rank 9.

Run with `python3 k10_factor_ranks.py`. Standard library only.
"""

from itertools import combinations

N = 10

P1F = [
    [(0, 1), (2, 3), (4, 5), (6, 7), (8, 9)],
    [(0, 2), (1, 4), (3, 6), (5, 8), (7, 9)],
    [(0, 3), (1, 5), (2, 7), (4, 9), (6, 8)],
    [(0, 4), (1, 3), (2, 8), (5, 7), (6, 9)],
    [(0, 5), (1, 2), (3, 9), (4, 6), (7, 8)],
    [(0, 6), (1, 8), (2, 4), (3, 7), (5, 9)],
    [(0, 7), (1, 9), (2, 6), (3, 5), (4, 8)],
    [(0, 8), (1, 7), (2, 9), (3, 4), (5, 6)],
    [(0, 9), (1, 6), (2, 5), (3, 8), (4, 7)],
]


def round_robin(q):
    """Return the factors F_c of GK_{q+1}, with the vertex oo written as q."""
    factors = []
    for c in range(q):
        edges = [(q, c)]
        for x in range(q):
            y = (2 * c - x) % q
            if x < y:
                edges.append((x, y))
        factors.append(edges)
    return factors


def perfect_matchings(points):
    """Return every perfect matching of the given points as a list of edges."""
    if not points:
        return [[]]
    first, rest = points[0], points[1:]
    result = []
    for i, partner in enumerate(rest):
        remaining = rest[:i] + rest[i + 1:]
        for tail in perfect_matchings(remaining):
            result.append([(first, partner)] + tail)
    return result


def partner_map(matching):
    """Return the involution of a matching as a list indexed by vertex."""
    mate = [None] * N
    for a, b in matching:
        mate[a] = b
        mate[b] = a
    return mate


def is_hamiltonian_pair(f, p):
    """Return True when the union of the two matchings is one cycle on all vertices."""
    mf, mp = partner_map(f), partner_map(p)
    v, length = 0, 0
    while True:
        v = mp[mf[v]]
        length += 2
        if v == 0:
            return length == N


def rank_f2(rows):
    """Return the rank over F_2 of integer bitmask rows."""
    basis = []
    for row in rows:
        for b in basis:
            row = min(row, row ^ b)
        if row:
            basis.append(row)
    return len(basis)


def check_factorization(factors):
    """Assert that the factors partition the edges of K_N into perfect matchings."""
    seen = set()
    for f in factors:
        assert sorted(v for e in f for v in e) == list(range(N))
        for a, b in f:
            e = (min(a, b), max(a, b))
            assert e not in seen
            seen.add(e)
    assert len(seen) == N * (N - 1) // 2


def report(name, factors, matchings):
    """Print the rank, the row parities and the pairwise Hamiltonicity of a family."""
    check_factorization(factors)
    rows = []
    for f in factors:
        bits = 0
        for j, p in enumerate(matchings):
            if is_hamiltonian_pair(f, p):
                bits |= 1 << j
        rows.append(bits)
    total = 0
    for r in rows:
        total ^= r
    pairwise = all(
        is_hamiltonian_pair(factors[s], factors[t])
        for s, t in combinations(range(len(factors)), 2)
    )
    print(f"{name}: factors={len(factors)} perfect={pairwise} "
          f"rank={rank_f2(rows)} rows_sum_to_zero={total == 0}")
    return rank_f2(rows), total == 0, pairwise


def main():
    matchings = perfect_matchings(list(range(N)))
    assert len(matchings) == 945
    print(f"perfect matchings of K_{N}: {len(matchings)}")
    r1, z1, p1 = report("P1F of Remark 7.15", P1F, matchings)
    r2, _, _ = report("GK_10", round_robin(N - 1), matchings)
    assert p1 and r1 == 8 and z1
    assert r2 == 9
    print("OK")


if __name__ == "__main__":
    main()
