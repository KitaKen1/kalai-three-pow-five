#!/usr/bin/env python3
"""Exact signed-vertex necessary conditions for four full facets."""
from functools import lru_cache
from itertools import product
import json
from .check_positive_geometry import SMALLINCIDENCES,row_options,TYPES
from .paths import ROOT

@lru_cache(None)
def carriers(R,k):
    ans=set();full=127
    for faces,c,q,b,w in SMALLINCIDENCES[R]:
        ff=dict(faces);ff[0]=-1
        masks=[s for s,d in ff.items() if d<4 and (full^s) in ff and ff[full^s]<4]
        for s,u in product(masks,repeat=2):
            ns,nu=full^s,full^u
            a=s&u;bmask=ns&nu;cc=s&nu;d=ns&u
            if a.bit_count()+bmask.bit_count()>k or cc.bit_count()+d.bit_count()>8-k:continue
            for mask in (a,bmask,cc,d):
                if mask not in ff:raise ValueError(('intersection not face',R))
            jF=next((TYPES.index(t) for t in TYPES if t[0]==s.bit_count() and ff[s]==3 and t==triple(ff,s)),None)
            if jF is None:jF=next((TYPES.index(t) for t in TYPES if ff[ns]==3 and t==triple(ff,ns)),None)
            jH=next((TYPES.index(t) for t in TYPES if ff[u]==3 and t==triple(ff,u)),None)
            if jH is None:jH=next((TYPES.index(t) for t in TYPES if ff[nu]==3 and t==triple(ff,nu)),None)
            # Polygons in the positive and negative full intersections,
            # counted from the containing ridge of F and H separately.
            stat=[]
            for x,y in ((s,u),(s,nu)):
                nx,ny=full^x,full^y
                zs=((x&y,x,y),(nx&ny,nx,ny))
                for side in (1,2):
                    polys=[z for z,vx,vy in zs if ff[z]==2 and ff[(vx,vy)[side-1]]==3]
                    stat.extend((len(polys),sum(z.bit_count() for z in polys)))
            # A nine-bit incidence parity is sufficient as ridge classes
            # are represented in the twelve-type order.
            parity=sum((v%2)<<j for j,v in enumerate(c))
            ans.add((jF,jH,w,parity,tuple(stat)))
    return tuple(sorted(ans,key=str))

def triple(ff,s):
    return (s.bit_count(),sum(d==1 and t&s==t for t,d in ff.items()),sum(d==2 and t&s==t for t,d in ff.items()))

def solve(rows,limit):
    F,H=rows[-2:];small=rows[:-2];total=0;examples=[]
    for of,oh in product(row_options(F),row_options(H)):
        if of[3]+oh[3]>limit:continue
        for k in range(4,8):
            # Seven common vertices split off the remaining antipodal
            # segment; its nonempty-face count is at least 3*81.
            if k==7:continue
            common=[j for j,t in enumerate(TYPES) if t[0]==k and of[0][j] and oh[0][j]]
            shares=[()]+[(j,) for j in common]
            if k==4 and of[0][0]>=2 and oh[0][0]>=2:shares.append((0,0))
            for share in shares:
                if not share and k>=5:
                    # Their intersection is a k-gon if it is not a ridge.
                    # Its excess k-3 must be paid outside the quadrilaterals.
                    if any(R[4]+R[0]-R[1]-3*R[3]-a[1]<k-3 for R,a in ((F,of),(H,oh))):continue
                targetF=list(of[0]);targetH=list(oh[0]);starget=[0]*8
                for pos,j in enumerate(share):
                    targetF[j]-=1;targetH[j]-=1
                    t=TYPES[j]
                    starget[4*pos:4*pos+4]=[t[2],2*t[1],t[2],2*t[1]]
                if sum(targetF)+sum(targetH)>14:continue
                opts=[carriers(R,k) for R in small]
                if any(not x for x in opts):continue
                ptarget=sum(((of[0][j]+oh[0][j])%2)<<j for j in range(12))
                @lru_cache(None)
                def rec(i,tf,th,st,parity,budget):
                    if budget<0:return 0
                    if i==7:return int(not any(tf) and not any(th) and not any(st) and parity==ptarget)
                    count=0
                    for jF,jH,w,p,stats in opts[i]:
                        if w>budget:continue
                        if jF is not None and tf[jF]==0:continue
                        if jH is not None and th[jH]==0:continue
                        # With no shared ridge, its polygon sums are unused.
                        stats=stats[:4*len(share)]+(0,)*(8-4*len(share))
                        if any(a>b for a,b in zip(stats,st)):continue
                        nf=list(tf);nh=list(th)
                        if jF is not None:nf[jF]-=1
                        if jH is not None:nh[jH]-=1
                        count+=rec(i+1,tuple(nf),tuple(nh),tuple(b-a for a,b in zip(stats,st)),parity^p,budget-w)
                    return count
                n=rec(0,tuple(targetF),tuple(targetH),tuple(starget),0,limit-of[3]-oh[3])
                if n:
                    total+=n;examples.append({'k':k,'share':share,'of':of,'oh':oh,'count':n})
    return total,examples

def main():
    D=json.loads((ROOT/'evidence/positive-profile-checks.json').read_text());cat=[tuple(R) for R in D['catalogue']]
    former=json.loads((ROOT/'evidence/positive-geometry-checks.json').read_text())
    out=[]
    for cell in former['cells']:
        results=[]
        for s in cell['survivors']:
            ids=s['ids'];rows=[cat[i-1] for i in ids]
            n,ex=solve(rows,78-3*cell['S'])
            results.append({'ids':ids,'witness_count':n,'full_options':ex})
        out.append({'G':cell['G'],'S':cell['S'],'profiles':results})
    assert all(s['witness_count']==0 for c in out for s in c['profiles'])
    print(json.dumps({'status':'passed','positive_two_pair_branch_excluded':True,'whole_theorem_verified':False,'cells':out,
      'carrier_patterns':[{'row':R,'k':k,'patterns':carriers(R,k)} for R in set(cat[:15]) for k in range(4,8)]},indent=2))
if __name__=='__main__':main()
