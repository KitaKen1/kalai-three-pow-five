#!/usr/bin/env python3
"""Exact finite checks for the mathematical manuscript; standard library only.

This checks the planar Gale catalogue and selected arithmetic consequences.
It does not verify the geometric full-facet arguments or the whole theorem.
Run: python3 -m verification.verify_mathematics
"""
from collections import Counter
from itertools import combinations
import json

U_TABLE={
 (1,1,2,3,6,7,10):(1,2,0,3,5,6,4),
 (1,2,2,4,5,8,9):(0,1,2,3,5,6,4),
 (1,3,3,4,5,8,9):(3,1,2,0,4,6,5),
 (1,4,5,6,6,8,9):(5,3,0,1,2,4,6),
 (1,4,5,7,7,8,9):(5,6,4,1,2,0,3),
 (1,4,5,8,9,10,10):(3,5,6,4,0,1,2),
 (2,3,4,4,6,7,10):(3,0,1,2,4,6,5),
 (2,3,5,5,6,7,10):(5,3,1,2,0,4,6),
 (2,3,6,7,8,8,10):(5,6,4,0,1,2,3),
 (2,3,6,7,9,9,10):(3,5,6,4,1,2,0)}


def require(condition, message):
    if not condition:
        raise ValueError(message)


def codes(n):
    """Sorted signed-line codes, with occupied lines numbered consecutively."""
    def extend(prefix, largest):
        if len(prefix) == n:
            yield tuple(prefix)
            return
        for c in range(prefix[-1] if prefix else 0, 2 * (largest + 1) + 3):
            yield from extend(prefix + [c], max(largest, line(c)) if c else largest)
    yield from extend([], -1)


def line(c):
    return (c - 1) // 2


def positive(c):
    return c % 2 == 1


def rank(cs, mask):
    return min(2, len({line(c) for i, c in enumerate(cs) if c and mask >> i & 1}))


def circuits(cs):
    """Minimal supports of a nonnegative dependence, read from signed order."""
    out = [1 << i for i, c in enumerate(cs) if not c]
    for i, j in combinations(range(len(cs)), 2):
        a, b = cs[i], cs[j]
        if a and b and line(a) == line(b) and positive(a) != positive(b):
            out.append((1 << i) | (1 << j))
    for indices in combinations(range(len(cs)), 3):
        if any(not cs[i] for i in indices):
            continue
        if len({line(cs[i]) for i in indices}) != 3:
            continue
        i, j, k = sorted(indices, key=lambda i: line(cs[i]))
        if positive(cs[i]) == positive(cs[k]) != positive(cs[j]):
            out.append(sum(1 << i for i in indices))
    return out


def covered(circ, mask):
    union = 0
    for c in circ:
        if c & mask == c:
            union |= c
    return union == mask


def separators(cs):
    """All sign partitions of a functional, at and between occupied lines."""
    out = []
    m = len({line(c) for c in cs if c})
    for pivot in range(m):
        for orientation in (-1, 1):
            for at_line in (True, False):
                p = q = 0
                for i, c in enumerate(cs):
                    if not c or (at_line and line(c) == pivot):
                        continue
                    side = (1 if line(c) > pivot else -1) if at_line else (
                        1 if line(c) >= pivot else -1)
                    sign = orientation * (1 if positive(c) else -1) * side
                    if sign > 0:
                        p |= 1 << i
                    else:
                        q |= 1 << i
                out.append((p, q))
    return out


def refuted(seps, mask):
    return any(mask & q == 0 and mask & p != 0 for p, q in seps)


def weights(row):
    n, e, p, r, j = row
    return (9 * p - 5 * e - n - j - 15,
            12 * n - 10 * e + 12 * p - 3 * j - 20 + 5 * (n == 7),
            16 * n + 2 * p + 31 * r - 10 * j - 48 + 12 * (n == 7),
            j - 3 * n - 3 * r + 10)


def dual(row):
    n, e, p, r, j = row
    return (r, p, e, n, j)


def catalogue():
    stats, rows = Counter(), set()
    profiles = {}
    for n in (5, 6, 7):
        for cs in codes(n):
            stats['sorted_codes'] += 1
            full = (1 << n) - 1
            if rank(cs, full) != n - 5:
                continue
            stats['rank_compatible_codes'] += 1
            circ, seps = circuits(cs), separators(cs)
            decisions = [covered(circ, s) for s in range(full + 1)]
            for s, yes in enumerate(decisions):
                require(yes != refuted(seps, s), ('coverage', cs, s))
            if not all(decisions[full ^ (1 << i)] for i in range(n)):
                stats['invalid_vertex_codes'] += 1
                continue
            faces = {}
            for f in range(1, full + 1):
                s = full ^ f
                if decisions[s]:
                    dim = 4 - s.bit_count() + rank(cs, s)
                    require(0 <= dim <= 4, ('dimension', cs, f, dim))
                    faces[f] = dim
            fvec = [sum(d == k for d in faces.values()) for k in range(5)]
            facets = [f for f, d in faces.items() if d == 3]
            j = sum(f.bit_count() for f in facets)
            row = tuple(fvec[:4]) + (j,)
            require(fvec[0] == n and fvec[4] == 1, ('vertex count', cs))
            rows.add(row)
            stats['valid_codes'] += 1
            six_facets = sum(f.bit_count() == 6 for f in facets)
            six_degree_vertices = sum(sum(bool(f >> i & 1) for f in facets) == 6
                                      for i in range(n))
            profiles.setdefault(row, set()).add((six_facets, six_degree_vertices))
            if row==(7,17,19,9,38):
                require(cs in U_TABLE,('U code missing',cs))
                pi=U_TABLE[cs]
                require(sorted(pi)==list(range(7)),('U permutation',cs))
                relabel=lambda m:sum(1<<pi[i] for i in range(7) if m>>i&1)
                require(sorted(relabel(t) for t in facets)==[15,23,27,29,46,86,102,122,124],
                        ('U incidence mismatch',cs))
                stats['u_incidence_codes']+=1
            for rr,ff,fac in ((row,faces,facets),
                    (dual(row),{sum(1<<i for i,t in enumerate(facets) if f&t==f):3-d
                     for f,d in faces.items() if d<4},
                     [sum(1<<j for j,t in enumerate(facets) if t>>i&1) for i in range(n)])):
                special={(7,15,14,6,29):9,(7,16,16,7,32):4,
                         (8,18,17,7,36):15,(8,18,17,7,35):10,(8,19,18,7,35):9}
                if rr in special:
                    quads=[q for q,d in ff.items() if d==2 and q.bit_count()==4]
                    b=sum(all(t.bit_count()==5 for t in fac if q&t==q) for q in quads)
                    eta=sum(q.bit_count()-3 for q,d in ff.items() if d==2)
                    require(len(quads)-3*b+2*eta>=special[rr],('Q55 small row weight',cs,rr))
                    stats['q55_weight_codes']+=1
                if rr==(8,18,17,7,35):
                    triples=[(t.bit_count(),sum(d==1 and f&t==f for f,d in ff.items()),
                              sum(d==2 and f&t==f for f,d in ff.items())) for t in fac]
                    pyramids=triples.count((5,8,5));prisms=triples.count((6,9,5))
                    require((prisms>0 and pyramids<3) or
                            (any(t[0]==7 for t in triples) and pyramids>0),
                            ('R35 zero-stress obstruction',cs,triples))
                    stats['R35_G0_profile_codes']+=1
                    require(any(t in ((6,10,6),(7,11,6)) for t in triples),
                            ('R35 special ridge',cs,triples))
                    stats['R35_special_ridge_codes']+=1
                if rr in ((7,17,18,8,36),(8,18,17,7,36)):
                    triples=Counter((t.bit_count(),sum(d==1 and f&t==f for f,d in ff.items()),
                                     sum(d==2 and f&t==f for f,d in ff.items())) for t in fac)
                    require(set(triples)<={(4,6,4),(5,8,5),(6,9,5)},
                            ('positive small ridge types',cs,rr,triples))
                    if rr[0]==7:
                        require(triples==Counter({(4,6,4):4,(5,8,5):4}),
                                ('positive D profile',cs,triples))
                    stats['positive_small_ridge_codes']+=1
                if rr==(8,19,18,7,35):
                    quads=[q for q,d in ff.items() if d==2 and q.bit_count()==4]
                    require(any(any(q&a==q and q&b==q and a|b==255
                                    for a,b in combinations(fac,2)) for q in quads),
                            ('Z full-cover quadrilateral',cs))
                    stats['Z_full_cover_codes']+=1
            if row==(7,17,17,7,32):
                triples=Counter((t.bit_count(),sum(d==1 and f&t==f for f,d in faces.items()),
                                 sum(d==2 and f&t==f for f,d in faces.items())) for t in facets)
                require(triples==Counter({(4,6,4):3,(5,8,5):2,(5,9,6):2}),
                        ('J ridge profile',cs,triples))
                require(sum(d==2 and f.bit_count()==4 for f,d in faces.items())==1,
                        ('J unique quad',cs))
                stats['J_profile_codes']+=1
            if row in ((7,15,14,6,29),(7,16,16,7,32)):
                quads=[q for q,d in faces.items() if d==2 and q.bit_count()==4]
                excess=sum(q.bit_count()-3 for q,d in faces.items() if d==2)
                require(all(sum(t.bit_count()==5 and q&t==q for t in facets)==1
                            for q in quads),('quadrilateral five-ridge incidence',cs))
                require(excess==(3 if row[1]==15 else 2),('quadrilateral excess',cs))
                if row[1]==15:
                    require(len(quads)==3,('Y quadrilaterals',cs))
                stats['quadrilateral_link_codes']+=1
            if row == (7, 15, 14, 6, 29):
                base = [f for f in facets if f.bit_count() == 6]
                require(len(base) == 1, 'pyramid base')
                require((full ^ base[0]).bit_count() == 1, 'pyramid apex')
            if row == (6, 14, 16, 8, 32):
                # In the polar, original facets become vertices; original vertices
                # become facets. The omitted pairs on its four sides give a matching.
                df = [sum(1 << j for j, f in enumerate(facets) if f >> i & 1)
                      for i in range(n)]
                tetra = [f for f in df if f.bit_count() == 4]
                sides = [f for f in df if f.bit_count() == 6]
                dfull = (1 << len(facets)) - 1
                require(len(tetra) == 2 and len(sides) == 4, 'prism facet sizes')
                require(tetra[0] & tetra[1] == 0 and tetra[0] | tetra[1] == dfull,
                        'opposite tetrahedra')
                omitted = [dfull ^ f for f in sides]
                require(sum(omitted) == dfull and len(set(omitted)) == 4,
                        'matching prism edges')
                require(all((m & tetra[0]).bit_count() == 1 and
                            (m & tetra[1]).bit_count() == 1 for m in omitted),
                        'each prism side omits one matched pair')
    require(len(rows) == 24, ('row count', len(rows)))
    require(stats['u_incidence_codes']==10,'U incidence coverage')
    y = (7, 15, 14, 6, 29)
    zd = (7, 18, 19, 8, 35)
    require(all(a == 1 for a, _ in profiles[y]), 'Y has one six-vertex ridge')
    require(all(b == 2 for _, b in profiles[zd]), 'Z dual has two vertices of degree six')
    require(all(row[0] - row[1] + row[2] - row[3] == 0 for row in rows), 'Euler')
    require(all(min(weights(row)) >= 0 for row in rows), 'local nonnegativity')
    exceptions = [r for r in sorted(rows) if weights(r)[1] - 5 * (r[0] == 7) < 0]
    require(exceptions == [y], ('M22 exception', exceptions))
    return sorted(rows), stats


def check_sixteen_twenty_two(rows):
    """Exhaust the small budget in the written proof, after the prism exclusion."""
    prism, z = (8, 16, 14, 6, 32), (8, 19, 18, 7, 35)
    eight = {dual(r) for r in rows if r[3] == 8} - {prism}
    # For n=8 and r>=8, Euler and J+32<=4e give the following finite box.
    # The upper edge bound e<=28 and g>=0 imply r<=22.
    for r in range(8, 23):
        for e in range(16, 29):
            p = e + r - 8
            for j in range(14 + 3 * r, 4 * e - 31):
                if j + 4 * r <= 4 * p:
                    eight.add((8, e, p, r, j))
    lx = lambda r: weights(r)[0] + 9 * (r[0] == 8)
    require(all(lx(r) >= 13 for r in eight), 'full row cost >=13')
    require(all(lx(r) >= 14 for r in eight if weights(r)[3] == 0), 'zero stress full cost >=14')
    require([r for r in sorted(eight) if weights(r)[3] == 0 and lx(r) == 18] == [z], 'unique Z')
    low_nonfull = {lx(r) for r in rows if lx(r) <= 9}
    require(low_nonfull == {0, 5}, ('small pair costs', low_nonfull))
    zero_costs = {r for r in rows if weights(r)[3] == 0 and lx(r) == 0}
    require(zero_costs == {(5, 10, 10, 5, 20), (7, 15, 14, 6, 29)}, 'zero cost rows')
    # 2A+4m+3G<=9, with A and G even, m a number of full pairs.
    positive = [(a, m, g) for a in range(0, 6, 2) for m in range(12)
                for g in range(2, 12, 2) if 2*a + 4*m + 3*g <= 9]
    require(positive == [(0, 0, 2)], ('positive G', positive))
    require(all((699 + 3*g) % 6 != 0 for _, _, g in positive), 'positive G residue')
    # For G=0, A=0 by polygon localization. Then m=0 or 1.
    budget = [(m, t, 6*t - 699 + 9*m) for m in (0, 1)
              for t in range(0, 119, 2) if 6*t - 699 + 9*m >= 14*m]
    require(budget == [(0, 118, 9), (1, 118, 18)], ('zero G budget', budget))
    require(9 not in {0, 5}, 'm=0 cannot pay cost nine')
    require(18 - 14 not in {0, 5}, 'cost fourteen leaves impossible four')
    counts = [(s, y, zz) for s in range(0, 23, 2) for y in range(0, 23, 2)
              for zz in (2,) if s+y+zz == 22 and 5*s+7*y+8*zz == 144]
    require(counts == [(6, 14, 2)], ('profile', counts))
    require((6*0 + 14*1 + 2*2) % 4 == 2, 'six-vertex ridge parity')
    return {'eight_vertex_box_rows': len(eight), 'forced_profile': counts[0],
            'six_vertex_ridge_incidences': 18,
            'scope': 'conditional on the written geometric and rigidity inputs'}


def main():
    rows, stats = catalogue()
    pairs = [(v, h) for v in range(14, 41, 2) for h in range(v, 41-v, 2)
             if (v-8)*(h-8) >= 40]
    expected = [(14, h) for h in (16,18,20,22,24,26)] + [
        (16, h) for h in (16,18,20,22,24)] + [(18, h) for h in (18,20,22)] + [(20,20)]
    require(pairs == expected, ('fifteen pairs', pairs))
    data = {'status': 'passed', 'whole_theorem_verified_by_this_script': False,
            'catalogue': dict(stats), 'rows': rows, 'counterexample_pairs': pairs,
            'sixteen_twenty_two': check_sixteen_twenty_two(rows),
            'limits': ['rigidity theorem is a mathematical input',
                       'full-facet arguments are not verified by this script',
                       'the other endpoint certificates have separate checkers']}
    print(json.dumps(data, indent=2))


if __name__ == '__main__':
    main()
