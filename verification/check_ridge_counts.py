#!/usr/bin/env python3
"""Exact nonnegative integer ridge-count checks; no proof-assistant dependency.

The geometric hypotheses are proved in the manuscript. This script checks
only the enumerations and arithmetic consequences of those hypotheses.
"""
from functools import lru_cache
import json

TYPES=((4,6,4),(5,8,5),(5,9,6),(6,9,5),(6,10,6),(6,11,7),(6,12,8),
       (7,11,6),(7,12,7),(7,13,8),(7,14,9),(7,15,10))
FAKE=((8,18,18,8,38),(8,18,18,8,39),(8,19,21,10,44),
      (8,20,23,11,47),(8,20,23,11,48),(8,19,20,9,42))
WEIGHTS={(8,18,18,8,40):18,(8,19,19,8,38):1,
         (8,19,19,8,39):4,(8,19,19,8,40):8}
STRONG={(8,19,19,8,38):4,(8,20,20,8,39):3,
        (8,19,19,8,39):8,(8,19,19,8,40):10,
        (8,19,20,9,41):8,(8,19,19,8,41):12}

@lru_cache(None)
def enumerate_counts(i,r,j,p):
    if r<0 or j<0 or p<0:return ()
    if i==len(TYPES):return ((),) if (r,j,p)==(0,0,0) else ()
    v,_,f=TYPES[i];out=[]
    for k in range(min(r,j//v,p//f)+1):
        rr,jj,pp=r-k,j-v*k,p-f*k
        if rr and (jj<min(t[0] for t in TYPES[i:])*rr or
                   jj>max(t[0] for t in TYPES[i:])*rr or
                   pp<min(t[2] for t in TYPES[i:])*rr or
                   pp>max(t[2] for t in TYPES[i:])*rr):continue
        out.extend((k,)+c for c in enumerate_counts(i+1,rr,jj,pp))
    return tuple(out)


def profiles(row):return enumerate_counts(0,row[3],row[4],2*row[2])

def local_possible(c):
    nonsimp=sum(k for k,(_,e,p) in zip(c,TYPES) if 2*e>3*p)
    return not ((c[3] and nonsimp<4) or (c[7] and nonsimp<3) or
                (c[3]>=2 and c[1] and nonsimp<5))

def parity_possible(c):
    # These two exclusions are proved by vertex-figure parity in the text.
    return c not in ((2,6,0,0,0,0,0,0,0,0,0,0),(1,6,1,0,0,0,0,0,0,0,0,0))

def minimum_weight(row,c):
    eta=row[4]+row[0]-row[1]-3*row[3]
    vals=[q-3*b+2*eta for q in range(eta+1) for b in range(min(q,c[1]//2)+1)
          if 2*q>=c[1]+3*c[3]]
    return min(vals) if vals else None

def strong_weight_values(row,c):
    eta=row[4]+row[0]-row[1]-3*row[3]
    out=[]
    for q in range(eta+1):
        # A nonquadrilateral nonsimplex polygon contributes at least two.
        if eta-q==1:continue
        for b in range(min(q,c[1]//2)+1):
            if 2*q<c[1]+3*c[3]:continue
            if sum(c[7:]) and (b or q<c[1]):continue
            if c[3] and b+3>q:continue
            if c[3]>=2 and b+5>q:continue
            if q==eta:
                # All polygons are triangles/quads; non-five-vertex ridges
                # reserve their exact three-dimensional polygon excess.
                if any(k and b+(2*e-3*f)>q for k,(n,e,f) in zip(c,TYPES) if n!=5):continue
            out.append((q,b,q-3*b+2*eta))
    return out

def main():
    fake=[]
    for r in FAKE:
        raw=profiles(r);remaining=[c for c in raw if local_possible(c)]
        if remaining:raise ValueError(('fake row survives',r,remaining))
        fake.append({'row':r,'raw_profiles':raw,'remaining_profiles':0})
    weighted=[]
    for r,lb in WEIGHTS.items():
        raw=profiles(r);surviving=[c for c in raw if local_possible(c) and parity_possible(c)]
        vals=[minimum_weight(r,c) for c in surviving]
        vals=[v for v in vals if v is not None]
        if vals and min(vals)<lb:raise ValueError(('weight too small',r,min(vals)))
        weighted.append({'row':r,'claimed_bound':lb,'minimum':min(vals) if vals else None,
                         'raw_profiles':raw,'admissible_count_profiles':len(surviving)})
    strong=[]
    for row,lb in STRONG.items():
        raw=profiles(row)
        survivors=[c for c in raw if local_possible(c) and parity_possible(c)]
        values=[(c,q,b,w) for c in survivors for q,b,w in strong_weight_values(row,c)]
        minimum=min((w for c,q,b,w in values),default=None)
        if minimum is not None and minimum<lb:raise ValueError(('strong weight',row,lb,minimum))
        strong.append({'row':row,'claimed_bound':lb,'minimum':minimum,
                       'raw_profiles':raw,'admissible_count_profiles':len(survivors),
                       'weight_minimizers':[(c,q,b) for c,q,b,w in values if w==minimum]})
    print(json.dumps({'status':'passed','whole_theorem_verified':False,
                      'fake_rows':fake,'weak_weights':weighted,'strong_weights':strong},indent=2))

if __name__=='__main__':main()
