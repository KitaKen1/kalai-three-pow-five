#!/usr/bin/env python3
"""Exact vertices of a balanced box with widths linear in height.

The cell boundaries used below are derived in the manuscript, not inferred
from numerical sampling. Fractions evaluate one representative of each cell.
"""
from fractions import Fraction as Q
from itertools import product,combinations
import json

SIGNS=tuple(product((-1,1),repeat=4))

def independent_vertices(r,d):
    """Independent active-matrix enumeration in coordinates (u0,u1,u2,t)."""
    r=tuple(map(Q,r));d=Q(d)
    inequalities=[]
    for j in range(4):
        for sign in (-1,1):
            if j<3:
                a=[Q(0)]*4;a[j]=sign;a[3]=r[j]
            else:a=[Q(-sign)]*3+[sign*d+r[j]]
            inequalities.append((a,Q(1)))
    inequalities.append(([Q(0)]*3+[Q(-1)],Q(0)))
    out=set()
    for chosen in combinations(inequalities,4):
        matrix=[a[:]+[b] for a,b in chosen]
        for col in range(4):
            pivot=next((j for j in range(col,4) if matrix[j][col]),None)
            if pivot is None:break
            matrix[col],matrix[pivot]=matrix[pivot],matrix[col]
            v=matrix[col][col];matrix[col]=[z/v for z in matrix[col]]
            for j in range(4):
                if j!=col:
                    v=matrix[j][col]
                    matrix[j]=[a-v*b for a,b in zip(matrix[j],matrix[col])]
        else:
            x=tuple(matrix[j][4] for j in range(4))
            if x[3]<=0:continue
            if all(sum(a*b for a,b in zip(row,x))<=rhs for row,rhs in inequalities):
                t=x[3];u=x[:3]+(d*t-sum(x[:3]),)
                out.add((t,u))
    return out

def vertices(r,d):
    r=tuple(map(Q,r));d=Q(d)
    R=sum(r);T=min(1/max(r),4/(abs(d)+R))
    out=set()
    for s in SIGNS:
        k=sum(s);den=d+sum(a*b for a,b in zip(s,r))
        if not k or not den:continue
        t=Q(k)/den
        if 0<t<T:
            u=tuple(a*(1-b*t) for a,b in zip(s,r))
            assert sum(u)==d*t
            out.add((t,u))
    b=tuple(1-a*T for a in r)
    nz=[i for i,a in enumerate(b) if a]
    # Vertices of a box cut by one sum equation have at most one
    # coordinate strictly between its two endpoints.
    for free in nz:
        others=[i for i in nz if i!=free]
        for s in product((-1,1),repeat=len(others)):
            u=[Q(0)]*4
            for i,a in zip(others,s):u[i]=a*b[i]
            u[free]=d*T-sum(u)
            if abs(u[free])<=b[free]:out.add((T,tuple(u)))
    if not nz and d*T==0:out.add((T,(Q(0),)*4))
    assert out
    return tuple(sorted(out))

def marked(V,r,edges=(),segments=()):
    return tuple(v for v in V if
        any(v[1][j]==s*(1-Q(r[j])*v[0]) for j,s in edges) or
        any(abs(v[1][j])==1 for j in segments))

def records(a):
    r=(Q(a),Q(1),Q(0),Q(0))
    levels=sorted(set((-(3-a),-(1+a),-(1-a),1-a,1+a,3-a)))
    cells=[]
    for k,b in enumerate(levels):
        cells.append(('point '+str(b),b))
        if k:cells.append(('open '+str(levels[k-1])+' .. '+str(b),(levels[k-1]+b)/2))
    cells += [('below',levels[0]-1),('above',levels[-1]+1)]
    out=[]
    for label,d in sorted(cells,key=lambda x:x[1]):
        V=vertices(r,d)
        out.append({'cell':label,'d':str(d),'positive':len(V),
                    'aligned':len(marked(V,r,((0,1),(1,1)))),
                    'opposed':len(marked(V,r,((0,1),(1,-1)))),
                    'edge_and_segment':len(marked(V,r,((0,1),),(2,))),
                    'edge1_and_segment':len(marked(V,r,((1,1),),(2,))),
                    'zero_pair':len(marked(V,r,(),(2,3))),
                    'both_edges0':len(marked(V,r,((0,1),(0,-1)))),
                    'both_edges1':len(marked(V,r,((1,1),(1,-1)))),
                    'edge0':len(marked(V,r,((0,1),))),
                    'edge1':len(marked(V,r,((1,1),)))})
    return out

def main():
    a=Q(1,2);unequal=records(a);equal=records(Q(1))
    equal_noextra=[v for v in equal if Q(v['d']) not in (-2,0,2)]
    assert min(v['aligned'] for v in unequal+equal_noextra)>=2
    assert min(v['opposed'] for v in unequal+equal_noextra)>=3
    assert min(v['edge_and_segment'] for v in unequal+equal_noextra)>=3
    assert min(v['edge1_and_segment'] for v in unequal+equal_noextra)>=3
    assert min(v['zero_pair'] for v in unequal+equal_noextra)>=4
    assert min(v['both_edges0'] for v in unequal+equal_noextra)>=4
    assert min(v['both_edges1'] for v in unequal+equal_noextra)>=4
    for v in unequal:
        d=Q(v['d'])
        if d>=a-1:assert v['aligned']>=4
        if d>=-1-a:assert v['aligned']>=3
        if d>-1-a:assert min(v['edge0'],v['edge1'])>=2
    for v in equal_noextra:
        d=Q(v['d'])
        if d>=0:assert v['aligned']>=4
        if d>-2:assert min(v['edge0'],v['edge1'])>=2
    one=[]
    for d in map(Q,(-4,-3,-2,-1,0,1,2,3,4)):
        V=vertices((1,0,0,0),d)
        one.append({'d':str(d),'positive':len(V),
                    'two_zero_segments':len(marked(V,(1,0,0,0),(),(1,2))),
                    'one_zero_segment':len(marked(V,(1,0,0,0),(),(1,))),
                    'edge_and_segment':len(marked(V,(1,0,0,0),((0,1),),(1,)))})
    assert min(v['two_zero_segments'] for v in one if Q(v['d']) not in (-3,-1,1,3))>=5
    assert min(v['one_zero_segment'] for v in one)>=3
    assert [Q(v['d']) for v in one if v['edge_and_segment']==3]==[-1,1]
    checks=0
    # Independent active-constraint enumeration tests all cells and all
    # equality rows; additional ratios corroborate the symbolic cell argument.
    for ratio in (Q(1,7),Q(1,3),Q(1,2),Q(2,3),Q(6,7),Q(1)):
        rr=(ratio,1,0,0)
        expected=unequal if ratio<1 else equal
        for v,template in zip(records(ratio),expected):
            for key in template:
                if key not in ('cell','d'):assert v[key]==template[key],(ratio,v,template)
            dd=Q(v['d'])
            assert set(vertices(rr,dd))==independent_vertices(rr,dd)
            checks+=1
    for v in one:
        dd=Q(v['d'])
        assert set(vertices((1,0,0,0),dd))==independent_vertices((1,0,0,0),dd)
        checks+=1
    print(json.dumps({'status':'passed','whole_theorem_verified':False,
                     'independent_matrix_checks':checks,
                     'unequal':unequal,'equal':equal,'one_width':one},indent=2))

if __name__=='__main__':main()
