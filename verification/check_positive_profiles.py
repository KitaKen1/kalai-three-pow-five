#!/usr/bin/env python3
"""Exact nine-pair arithmetic; uses only the independent small catalogue."""
from itertools import combinations_with_replacement
import json
from .certificate_checks import universe,extended_local_cost

from .paths import ROOT
CELLS=((2,2),(2,4),(2,6),(2,8),(2,10),(4,2),(4,4),(4,6))

def support():
    exclusion=tuple(tuple(x) for x in json.loads((ROOT/'certificates'/'low18-certificate-data.json').read_text())['leaves'][0]['excludedF'])
    rows=universe(8,2,exclusion)
    seven=tuple(R for R in rows if R[0]==7 and R[4]>=4*R[3])
    full=tuple(R for R in rows if R[0]==8 and 7<=R[3]<=11 and R[1]+3*R[3]<=R[4]+R[0] and R[4]>=4*R[3])
    assert len(seven)==15 and len(full)==32,(len(seven),len(full))
    return seven,full

def main():
    seven,full=support();catalogue=seven+full
    leaf={'costF':[0]*10,'quadF':1,'row_weight':'q55bsix'}
    weight=lambda R:extended_local_cost(leaf,'F',R)
    g=lambda R:R[4]-3*R[0]-3*R[3]+10
    candidates=[]
    # Each pair list has seven non-full entries and two full entries.
    # The ridge-excess budget is four, so every row beyond it is pruned.
    def rec(i,remaining,budget,items):
        if not remaining:
            yield items;return
        if i==len(seven):return
        R=seven[i];cost=R[3]-R[0]+1
        for m in range(remaining+1):
            if m*cost>budget:break
            yield from rec(i+1,remaining-m,budget-m*cost,items+(R,)*m)
    for F,H in combinations_with_replacement(full,2):
        b=4-(F[3]-7)-(H[3]-7)
        if b<0:continue
        for small in rec(0,7,b,()):candidates.append(small+(F,H))
    assert len(candidates)==1914,len(candidates)
    results=[]
    for G,S in CELLS:
        profiles=[l for l in candidates if
            2*sum(R[1] for R in l)==288+S and sum(g(R) for R in l)==G-1 and
            sum(R[3]-R[0]+1 for R in l)==4 and sum(weight(R) for R in l)<=78-3*S]
        results.append({'G':G,'S':S,'profiles':[[catalogue.index(R)+1 for R in l] for l in profiles]})
    assert [len(x['profiles']) for x in results]==[42,54,34,14,1,4,1,1]
    print(json.dumps({'status':'passed','whole_theorem_verified':False,
                     'catalogue':[list(R) for R in catalogue],
                     'candidate_multisets':len(candidates),'cells':results},indent=2))

if __name__=='__main__':main()
