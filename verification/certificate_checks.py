#!/usr/bin/env python3
"""Exact arithmetic for printed local-cost certificates, independent of a proof assistant.

All arithmetic uses integers or fractions. A certificate is accepted only when
every local row has nonnegative cost and the displayed nonnegative combination
of global inequalities is a strictly negative constant. This module does not
establish the geometric hypotheses supplying those inequalities.
"""
from fractions import Fraction
from functools import lru_cache
from math import gcd, lcm
import json

from .paths import ROOT
NAMES = ('t', 'e', 'I', 'G', 'S', 'nF5', 'nF6', 'rF5', 'rF6',
         'nS5', 'nS6', 'rS5', 'rS6', 'kF', 'kS', 'nF8', 'rF8', 'nS8', 'rS8', 'QW')


def vector(**terms):
    return tuple(terms.get(k, 0) for k in NAMES) + (terms.get('constant', 0),)


def add(*rows):
    return tuple(sum(r[i] for r in rows) for i in range(len(NAMES) + 1))


def scale(c, row):
    return tuple(c * v for v in row)


def quantities(v, h):
    t, e, I, G, S = (vector(**{k: 1}) for k in NAMES[:5])
    r = add(t, scale(-1, e))
    p = add(t, vector(constant=2-v-h))
    x = vector(G=1, e=-1, t=3, constant=2*v-3*h-4)
    y = vector(S=1, e=1, t=2, constant=-3*v+2*h-4)
    f03 = add(I, x, scale(-2, e))
    f14 = add(I, y, scale(-2, r))
    A = vector(I=2, G=-1, S=-1, constant=26-8*(v+h))
    B = vector(I=-1, G=-1, S=2, e=9, t=-3, constant=-8*v+7*h-4)
    C = vector(I=-1, G=2, S=-1, e=-9, t=6, constant=7*v-8*h-4)
    out = dict(t=t, e=e, r=r, p=p, I=I, x=x, y=y, G=G, S=S,
               A=A, B=B, C=C, f03=f03, f14=f14)
    out.update({k: vector(**{k: 1}) for k in NAMES[5:]})
    return out


def summed_cost(cost, side, v, h, q):
    c0, cn, ce, cp, cr, cj, a5, a6, b5, b6 = cost
    if side == 'F':
        values = [vector(constant=h), q['I'], q['f14'], q['y'],
                  scale(2, q['r']), scale(2, q['f03'])]
        counts = ['nF5', 'nF6', 'rF5', 'rF6']
    else:
        values = [vector(constant=v), q['I'], q['f03'], q['x'],
                  scale(2, q['e']), scale(2, q['f14'])]
        counts = ['nS5', 'nS6', 'rS5', 'rS6']
    return add(*(scale(c, z) for c, z in zip(cost[:6], values)),
               *(scale(c, q[k]) for c, k in zip(cost[6:], counts)))


def global_inequalities(leaf):
    v, h = leaf['endpoint']
    q = quantities(v, h)
    rows = [(k+' >= 0', q[k]) for k in ('e','p','r','I','x','y','G','S','A','B','C')]
    rows += [(k+' >= 0', q[k]) for k in NAMES[5:13]]
    rows += [('2I <= vh', vector(I=-2, constant=v*h)),
             ('t <= 118', vector(t=-1, constant=118))]
    for side in ('F', 'S'):
        cost = summed_cost(leaf['cost'+side], side, v, h, q)
        if 'threshold'+side in leaf:
            ag, tau = leaf['threshold'+side]
            cost = add(cost, scale(ag, q['k'+side]))
        if 'full'+side in leaf:
            a8, b8 = leaf['full'+side]
            cost = add(cost, scale(a8,q['n'+side+'8']),scale(b8,q['r'+side+'8']))
        if 'quad'+side in leaf:
            cost = add(cost, scale(leaf['quad'+side], q['QW']))
        rows.append(('sum '+side+' cost >= 0',cost))
    if leaf.get('quad_budget'):
        rows.extend([('QW >= 0',q['QW']),
                     ('quadrilateral budget',add(scale(4,q['A']),scale(4,q['f03']),
                      scale(4,q['f14']),scale(-4,q['I']),scale(-6,q['y']),scale(-1,q['QW'])))])
    for side in ('F','S'):
        if leaf.get('threshold'+side,[0])[0]:
            rows.extend([('k'+side+' >= 0',q['k'+side]),
                         ('k'+side+' <= 2',add(vector(constant=2),scale(-1,q['k'+side])))])
        if 'full'+side in leaf:
            rows.extend([(k+' >= 0',q[k]) for k in ('n'+side+'8','r'+side+'8')])
    for k, sense, bound in leaf['bounds']:
        z = q[k]
        if sense == '>=':
            rows.append((k+' >= '+str(bound), add(z, vector(constant=-bound))))
        elif sense == '<=':
            rows.append((k+' <= '+str(bound), add(scale(-1,z), vector(constant=bound))))
        elif sense == '=':
            rows.extend([(k+' >= '+str(bound), add(z, vector(constant=-bound))),
                         (k+' <= '+str(bound), add(scale(-1,z), vector(constant=bound)))])
        else:
            raise ValueError(sense)
    return rows


def primitive(row, combination):
    d = 0
    for z in row[:-1]:
        d = gcd(d, abs(z))
    if not d:
        return row, combination
    return tuple(z//d for z in row[:-1]) + (Fraction(row[-1])/d,), {k: w/d for k,w in combination.items()}


def contradiction(rows, max_rows=100000):
    """Fourier--Motzkin elimination, retaining a nonnegative proof combination."""
    active = [(tuple(row), {i: Fraction(1)}) for i, (_, row) in enumerate(rows)]
    todo = list(range(len(NAMES)))
    while True:
        by_direction = {}
        for row, weights in active:
            if not any(row[:-1]):
                if row[-1] < 0:
                    denomin = lcm(*(w.denominator for w in weights.values()))
                    integers = {i:int(w*denomin) for i,w in weights.items()}
                    combined = add(*(scale(w, rows[i][1]) for i,w in integers.items()))
                    if any(combined[:-1]) or combined[-1] >= 0 or any(w < 0 for w in integers.values()):
                        raise ValueError('Invalid elimination certificate')
                    return {'multipliers': integers, 'constant': combined[-1]}
                continue
            row, weights = primitive(row, weights)
            direction = row[:-1]
            previous = by_direction.get(direction)
            if previous is None or row[-1] < previous[0][-1]:
                by_direction[direction] = (row, weights)
        active = list(by_direction.values())
        if not todo:
            raise ValueError('No contradiction established')
        def complexity(k):
            pos = sum(r[k]>0 for r,_ in active)
            neg = sum(r[k]<0 for r,_ in active)
            return pos*neg, pos+neg, k
        k = min(todo, key=complexity)
        todo.remove(k)
        positive = [(r,w) for r,w in active if r[k]>0]
        negative = [(r,w) for r,w in active if r[k]<0]
        following = [(r,w) for r,w in active if not r[k]]
        for r,a in positive:
            for s,b in negative:
                cr, cs = -s[k], r[k]
                common = gcd(cr,cs)
                cr, cs = cr//common, cs//common
                z = add(scale(cr,r), scale(cs,s))
                weights = {i:cr*w for i,w in a.items()}
                for i,w in b.items():
                    weights[i] = weights.get(i, Fraction(0))+cs*w
                following.append(primitive(z, weights))
        if len(following) > max_rows:
            raise ValueError('Elimination row limit reached')
        active = following


def local_cost(cost, row):
    n,e,p,r,j = row
    return sum(a*b for a,b in zip(cost[:6], (1,n,e,p,r,j))) + sum(
        a*(z==k) for a,z,k in zip(cost[6:], (n,n,r,r), (5,6,5,6)))


def extended_local_cost(leaf, side, row):
    result = local_cost(leaf['cost'+side],row)
    if 'threshold'+side in leaf:
        ag,tau=leaf['threshold'+side]
        result += ag*(tau < 2*(row[4]-3*row[0]-3*row[3]+10))
    if 'full'+side in leaf and row[0]==8:
        a8,b8=leaf['full'+side]
        result += a8+b8*row[3]
    if 'quad'+side in leaf:
        weight = 9*(row==(7,15,14,6,29))+4*(row==(7,16,16,7,32))
        if leaf.get('row_weight') in ('q55','q55strong','q55refined','q55bfive','q55bsix'):
            weight={(7,15,14,6,29):9,(7,16,16,7,32):4,
                    (8,18,17,7,36):15,(8,18,17,7,35):10,(8,19,18,7,35):9,
                    (8,19,19,8,38):1,(8,18,18,8,40):18,
                    (8,19,19,8,39):4,(8,19,19,8,40):8}.get(row,0)
            if leaf['row_weight'] in ('q55strong','q55refined','q55bfive','q55bsix'):
                weight={(8,19,19,8,38):3,(8,20,20,8,39):3,
                        (8,19,19,8,39):8,(8,19,19,8,40):10,
                        (8,19,20,9,41):8,(8,19,19,8,41):12}.get(row,weight)
            if leaf['row_weight']=='q55refined' and row==(8,19,19,8,38):weight=4
            if leaf['row_weight']=='q55bfive' and row==(8,19,19,8,38):weight=5
            if leaf['row_weight']=='q55bsix' and row==(8,19,19,8,38):weight=6
        result += leaf['quad'+side]*weight
    return result


@lru_cache(maxsize=None)
def small_catalogue():
    from .verify_mathematics import catalogue
    return tuple(tuple(row) for row in catalogue()[0])


@lru_cache(maxsize=None)
def universe(nmax, cap, exclusions):
    from .verify_mathematics import dual
    if not 5 <= nmax <= 11:
        raise ValueError('Unsupported vertex bound')
    small = small_catalogue()
    small_all = set(small) | {dual(row) for row in small}
    result = {row for row in small_all if row[0] <= nmax and
              0 <= 2*(row[4]-3*row[0]-3*row[3]+10) <= cap and row not in exclusions}
    for n in range(8,nmax+1):
        emax = n*(n-1)//2
        for e in range(0,emax+1):
            for r in range(8, (4*e-7*n+10)//3+1):
                p = e+r-n
                lo = 3*n+3*r-10
                hi = min(4*e-4*n, 4*p-4*r, lo+cap//2)
                for j in range(lo,hi+1):
                    row=(n,e,p,r,j)
                    if row not in exclusions:
                        result.add(row)
    return tuple(sorted(result))


def verify_leaf(leaf):
    checked=[]
    for side in ('F','S'):
        exclusions = tuple(tuple(row) for row in leaf['excluded'+side])
        rows = universe(leaf['nmax'+side], leaf['cap'+side], exclusions)
        if leaf.get('four_r'):
            rows=tuple(row for row in rows if row[4]>=4*row[3])
        bad = [row for row in rows if extended_local_cost(leaf,side,row)<0]
        if bad:
            raise ValueError((leaf['label'], side, 'negative local cost', bad[0]))
        checked.append(len(rows))
    rows = global_inequalities(leaf)
    proof = contradiction(rows)
    return {'label':leaf['label'], 'local_rows':checked,
            'inequality_labels':[label for label,_ in rows],
            'inequalities':[list(row) for _,row in rows], **proof}


if __name__ == '__main__':
    data = json.loads((ROOT/'certificates'/'mathematical-certificate-data.json').read_text())
    proofs = [verify_leaf(leaf) for leaf in data['leaves']]
    print(json.dumps({'status':'passed','scope':'Local costs and exact global contradictions only',
                      'whole_theorem_verified':False, 'certificates':proofs}, indent=2))
