#!/usr/bin/env python3
"""Independent necessary ridge-pattern search; no Lean imports or execution."""
from itertools import combinations
from collections import Counter,defaultdict
from functools import lru_cache
import json
from .verify_mathematics import codes,rank,circuits,covered,dual
from .check_ridge_counts import TYPES,profiles,local_possible,parity_possible,strong_weight_values
from .certificate_checks import extended_local_cost
from .paths import ROOT
SMALLINCIDENCES=defaultdict(set)

def small_patterns():
    out=defaultdict(set)
    for n in (5,6,7):
        for cs in codes(n):
            full=(1<<n)-1
            if rank(cs,full)!=n-5:continue
            circ=circuits(cs)
            if not all(covered(circ,full^(1<<i)) for i in range(n)):continue
            ff={f:4-(full^f).bit_count()+rank(cs,full^f) for f in range(1,full+1) if covered(circ,full^f)}
            fac=[f for f,d in ff.items() if d==3]
            row=tuple(sum(d==i for d in ff.values()) for i in range(4))+(sum(t.bit_count() for t in fac),)
            for R,faces,ridges in ((row,ff,fac),(dual(row),{sum(1<<i for i,t in enumerate(fac) if f&t==f):3-d for f,d in ff.items() if d<4},[sum(1<<j for j,t in enumerate(fac) if t>>i&1) for i in range(n)])):
                if R[0]>8:continue
                tt=Counter((t.bit_count(),sum(d==1 and f&t==f for f,d in faces.items()),sum(d==2 and f&t==f for f,d in faces.items())) for t in ridges)
                c=tuple(tt[t] for t in TYPES)
                if sum(c)!=R[3]:raise ValueError(('unlisted ridge',R,tt))
                q=sum(d==2 and f.bit_count()==4 for f,d in faces.items())
                b=sum(all(t.bit_count()==5 for t in ridges if f&t==f) for f,d in faces.items() if d==2 and f.bit_count()==4)
                eta=R[4]+R[0]-R[1]-3*R[3]
                out[R].add((c,q,b,q-3*b+2*eta))
                if R[0]==7:
                    SMALLINCIDENCES[R].add((tuple(sorted(faces.items())),c,q,b,q-3*b+2*eta))
    return out

@lru_cache(None)
def row_options(R):
    if R in SMALL:return tuple(sorted(SMALL[R]))
    vals=[]
    lb=extended_local_cost({'costF':[0]*10,'quadF':1,'row_weight':'q55bsix'},'F',R)
    if R==(8,19,19,8,39):lb=12
    for c in profiles(R):
        if not local_possible(c) or not parity_possible(c):continue
        # Three tetrahedra and otherwise square pyramids need 22 edges.
        if c[0]==3 and c[1]==R[3]-3 and sum(c[2:])==0 and R[1]<22:continue
        # Bipyramid/prism shell lemma proved separately in the manuscript.
        if c==(3,3,1,1,0,0,0,0,0,0,0,0) and R[1]<20:continue
        if any(k and f+1>R[3] for k,(n,e,f) in zip(c,TYPES)):continue
        if any(k and n==7 and R[3]>f+1 for k,(n,e,f) in zip(c,TYPES)):continue
        for q,b,w in strong_weight_values(R,c):
            if c[3] and b:continue
            if w<lb:continue
            vals.append((c,q,b,w))
    return tuple(vals)

SMALL=small_patterns()

def main():
    D=json.loads((ROOT/'evidence/positive-profile-checks.json').read_text());R=[tuple(r) for r in D['catalogue']]
    out=[]
    for cell in D['cells'][:4]:
        survivors=[]
        for ids in cell['profiles']:
            rows=[R[i-1] for i in ids];limit=78-3*cell['S']
            # Seven small pairs supply at most seven ridge neighbours;
            # the other full pair supplies at most two actual neighbours.
            if any(r[0]==8 and r[3]>9 for r in rows):continue
            opts=[row_options(r) for r in rows]
            if any(not a for a in opts):continue
            suffix=[0]*10
            for i in reversed(range(9)):suffix[i]=suffix[i+1]+min(a[3] for a in opts[i])
            witnesses=[]
            def rec(i,w,chosen):
                if w+suffix[i]>limit:return
                if i==9:
                    sums=[sum(a[0][j] for a in chosen) for j in range(12)]
                    if any(s%2 for s in sums):return
                    # Every ridge has a distinct non-antipodal partner. At most
                    # one ridge of a given type can be shared by two facets.
                    for j,(n,e,f) in enumerate(TYPES):
                        carriers=[k for k,a in enumerate(chosen) if a[0][j]]
                        for k in carriers:
                            cap=sum(1 if min(rows[k][0],rows[l][0])<2*n else 2 for l in carriers if l!=k)
                            if chosen[k][0][j]>cap:return
                    # Any set of ridges with >=5 vertices needs different
                    # antipodal partner pairs. For a seven-vertex facet this
                    # is true also for its tetrahedral ridges.
                    for k,a in enumerate(chosen):
                        types=[j for j,v in enumerate(a[0]) if v and (TYPES[j][0]>=5 or rows[k][0]==7)]
                        for mask in range(1,1<<len(types)):
                            js=[j for l,j in enumerate(types) if mask>>l&1]
                            demand=sum(a[0][j] for j in js)
                            supply=sum(any(chosen[l][0][j] for j in js) for l in range(9) if l!=k)
                            if demand>supply:return
                    # A >=5-vertex ridge shared by the two full pairs leaves
                    # no second full neighbour. The small/full adjacency
                    # count then gives r(F)+r(H)<=16.
                    fullids=[k for k,r in enumerate(rows) if r[0]==8]
                    if sum(rows[k][3] for k in fullids)>16:
                        for k in fullids:
                            types=[j for j,v in enumerate(chosen[k][0]) if v and TYPES[j][0]>=5]
                            for mask in range(1,1<<len(types)):
                                js=[j for l,j in enumerate(types) if mask>>l&1]
                                demand=sum(chosen[k][0][j] for j in js)
                                smallsupply=sum(any(chosen[l][0][j] for j in js) for l in range(9) if rows[l][0]==7)
                                if demand>smallsupply:return
                    # A two-face lies in at least three facets, and cannot
                    # lie in both members of an antipodal facet pair.
                    if 0<sum(rows[k][4]+rows[k][0]-rows[k][1]-3*rows[k][3]-a[1]>0 for k,a in enumerate(chosen))<3:return
                    witnesses.append(tuple(chosen));return
                for a in opts[i]:rec(i+1,w+a[3],chosen+(a,))
            rec(0,0,())
            if witnesses:survivors.append({'ids':ids,'local_witnesses':len(witnesses),'first':witnesses[0]})
        out.append({'G':cell['G'],'S':cell['S'],'survivors':survivors})
    print(json.dumps({'status':'passed','whole_theorem_verified':False,'small_patterns':{str(r):sorted(v) for r,v in SMALL.items()},'row_options':[(r,len(row_options(r))) for r in R],'cells':out},indent=2))
if __name__=='__main__':main()
