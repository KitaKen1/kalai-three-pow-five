#!/usr/bin/env python3
"""Integer-only certificates for continuous cube lifts, without Lean.

The script proves statements conditional on four independent full normals.
It checks these finite certificates, not the other geometric endpoint proofs
or the whole theorem.
"""
from itertools import combinations_with_replacement
from collections import Counter
import gzip, json

from .paths import ROOT

def require(ok, message):
    if not ok:raise ValueError(message)

def dot(x,y):
    require(len(x)==len(y),'dot dimensions')
    return sum(a*b for a,b in zip(x,y))

def lin(terms,d):
    terms=list(terms)
    return [sum(c*u[j] for c,u in terms) for j in range(d)]

def span(us,C,D):
    d=len(us)
    return D!=0 and len(C)==d and all(len(u)==d for u in us+C) and all(
        sum(C[j][k]*us[k][i] for k in range(d))==(D if i==j else 0)
        for j in range(d) for i in range(d))

def sign(x):return (x>0)-(x<0)
def strict(xs):return all(a<b for a,b in zip(xs,xs[1:]))
def rep(c,d=4):return [1]+[-1 if c&(1<<j) else 1 for j in range(d-1)]
def negative(u):return [-a for a in u]
def full(mask,m):return all(bool(mask&(1<<i))!=bool(mask&(1<<(i+m))) for i in range(m))
def anti(mask,m):return (mask>>m)|((mask&((1<<m)-1))<<m)
def meet(gens,mask,m):
    r=(1<<(2*m))-1
    for g in gens:
        if mask&g==mask:r&=g
    return r

def reduction(data):
    m=data['pairs'];families=data['families'];tab=data['reduction']
    allseq=[list(s) for s in combinations_with_replacement(range(8),m)
            if all(s[i]!=s[i+2] for i in range(m-2))]
    require([c for c,_ in tab]==allseq,'exhaustive base reduction')
    hist=Counter()
    for c,node in tab:
        op,*a=node;qs=[rep(k) for k in c]
        if op=='nonspan':
            n,=a;require(len(n)==4 and any(n) and all(dot(n,q)==0 for q in qs),'nonspan')
        else:
            require(op=='map','unknown reduction')
            f,A,d,B,e,tau,eps=a
            require(0<=f<len(families) and d!=0 and e!=0,'map denominator')
            require(span(A,B,e),'inverse of base map')
            require(sorted(tau)==list(range(m)) and len(eps)==m and all(s in (-1,1) for s in eps),'map labels')
            target=families[f]['F']['qs']
            require(all(dot(row,[eps[w]*x for x in qs[tau[w]]])==d*target[w][i]
                        for w in range(m) for i,row in enumerate(A)),'base map values')
            hist[f]+=1
    for X in families:
        F=X['F'];b=X['basis'];free=X['free']
        require(len(b)==4 and len(free)==m-4 and sorted(b+free)==list(range(m)),'shear labels')
        require(span([F['qs'][i] for i in b],X['N'],X['D']),'shear inverse')
        require(all(F['zeta'][i]==[0]*(m-4) for i in b),'zero heights')
        require(all(F['zeta'][i]==[int(j==k) for j in range(m-4)] for k,i in enumerate(free)),'free heights')
    return dict(sequences=len(allseq),nonspanning=len(tab)-sum(hist.values()),uses=dict(hist))

def family_check(F,m):
    d=m-4;n=2*m;qs=F['qs']+[negative(q) for q in F['qs']]
    zs=F['zeta']+[negative(z) for z in F['zeta']];planes=F['planes'];stats=Counter()
    require(len(qs)==n and len(zs)==n and all(len(q)==4 and all(x in (-1,1) for x in q) for q in qs),'base points')
    require(all(len(z)==d for z in zs+planes),'height dimensions')
    def plane(p):
        require(0<=p<len(planes),'plane index');return planes[p]
    def entform(ent):
        p,c=ent
        return [0]*d if p is None else [c*x for x in plane(p)]
    records=F['facets'] if m==7 else F['recs']
    for r in records:
        if m==7:
            indices,eps,C,c4,C5,ent=r
            require(len(C)==4 and len(C5)==d and eps in (-1,1),'record dimensions')
            require(sorted(w for w,p,c in ent)==list(range(n)),'record point labels')
            entries=[None]*n
            for w,p,c in ent:entries[w]=[p,c]
        else:
            T,C,c4,C5,entries,o,lam,k,B,D,sp=r
            require(len(T)==5 and len(set(T))==5 and all(0<=w<n for w in T),'five spanning points')
            require(len(entries)==n and all(entries[w][0] is None for w in T),'tight spanning points')
            require(len(lam)==5 and 0<=k<5 and lam[k]!=0,'base dependency')
            require(lin(zip(lam,[qs[w] for w in T]),4)==[0]*4,'base dependence identity')
            require(span([qs[w] for j,w in enumerate(T) if j!=k],B,D),'four independent bases')
            require(C5==entform(o) and o[1]!=0,'constant form')
            require(lin(zip(lam,[zs[w] for w in T]),d)==entform(sp) and sp[1]!=0,'height span identity')
        require(len(C)==4 and all(len(u)==d for u in C),'record normal')
        for w in range(n):
            actual=lin([(qs[w][j],C[j]) for j in range(4)]+[(c4,zs[w]),(1,C5)],d)
            require(actual==entform(entries[w]),'functional value identity')
    vf=F.get('vf',[])
    for normal,bound,mask,kind in vf:
        require(len(normal)==4 and bound>0,'vertical normal')
        vals=[dot(normal,q) for q in qs]
        require(max(vals)<=bound and mask==sum(1<<w for w,x in enumerate(vals) if x==bound),'vertical support')
        if kind is None:require(full(mask,m),'vertical full facet')
        else:
            w,z,b,C,D=kind
            require(0<=w<n and 0<=z<n and w!=z and qs[w]==qs[z] and mask&(1<<w) and mask&(1<<z),'vertical duplicated fibre')
            require(len(b)==4 and all(0<=i<n and mask&(1<<i) for i in b) and span([qs[i] for i in b],C,D),'vertical spanning')
    require(strict([v[2] for v in vf]),'distinct vertical facets')
    def mask(rindex,facts):
        if not 0<=rindex<len(records):return None
        r=records[rindex]
        if m==7:
            _,eps,_,_,_,entries=r;vals=[None]*n
            for w,p,c in entries:
                if p is not None and p not in facts:return None
                val=0 if p is None else eps*c*facts[p]
                if val>0:return None
                vals[w]=val
        else:
            _,_,c4,_,entries,o,_,_,_,_,sp=r
            if o[0] not in facts or sp[0] not in facts:return None
            orient=sign(o[1])*facts[o[0]]
            if orient==0 or facts[sp[0]]==0 or orient*c4>=0:return None
            vals=[]
            for p,c in entries:
                if p is not None and p not in facts:return None
                val=0 if p is None else sign(c)*facts[p]
                if val not in (0,orient):return None
                vals.append(val)
        return sum(1<<w for w,v in enumerate(vals) if v==0)
    def combo(facts,cert):
        terms=[];positive=False
        for idx,c in cert:
            require(0<=idx<len(facts),'fact index');p,s=facts[idx]
            require(s==0 or c>=0,'nonnegative strict combination')
            positive |= s!=0 and c>0
            terms.append((c*(s or 1),plane(p)))
        return lin(terms,d),positive
    def walk(node,path,top=True):
        op,*a=node;stats[op]+=1;facts=dict(path)
        require(len(facts)==len(path),'no repeated fact')
        if op=='branch':
            p,*children=a;plane(p);require(p not in facts,'unassigned branch')
            for s,child in zip((-1,0,1),children):
                walk(child,([(p,s)]+path) if m==7 else (path+[(p,s)]),top)
        elif op=='leaf':
            if m==7:
                rs,faces=a;require(all(0<=r<len(records) for r in rs),'face record index')
                gens=[g for r in rs if (g:=mask(r,facts)) is not None]
                require(len(faces)>=243 and strict(faces) and all(0<f<(1<<n) and meet(gens,f,m)==f for f in faces),'243 face intersections')
            else:
                rs,=a;ms=[mask(r,facts) for r in rs]
                require(all(g is not None for g in ms) and len(ms)>=F['need'] and strict(ms),'upper facets')
                require(len(vf)+2*F['need']>=21,'facet threshold')
        elif op=='rank5':
            g=mask(a[0],facts);require(g is not None and full(g,m),'fifth independent full normal')
        elif op=='count':
            rs,faces=a;ms=[g for r in rs if (g:=mask(r,facts)) is not None]
            gens=[v[2] for v in vf]+ms+[anti(g,m) for g in ms]
            require(len(faces)>=242 and strict(faces) and all(0<f<(1<<n) and any(f&g==f for g in gens) and meet(gens,f,m)==f for f in faces),'242 proper face intersections')
        elif op=='refuted':
            if m==7:
                cert,=a;terms=[];pos=False
                for p,s,c in cert:
                    require(facts.get(p)==s and (s==0 or c>=0),'refuting fact')
                    pos |= s!=0 and c>0;terms.append((c*(s or 1),plane(p)))
                require(pos and lin(terms,d)==[0]*d,'refutation identity')
            else:
                u,pos=combo(path,a[0]);require(pos and u==[0]*d,'refutation identity')
        elif op=='zeroRank3':
            p,q,r=a;u,v,w=[plane(k) for k in a]
            det=u[0]*(v[1]*w[2]-v[2]*w[1])-u[1]*(v[0]*w[2]-v[2]*w[0])+u[2]*(v[0]*w[1]-v[1]*w[0])
            require(all(facts.get(k)==0 for k in a) and det!=0,'zero parameter')
        elif op=='zero':
            p,q,r,s,C,D=a;require(all(facts.get(k)==0 for k in (p,q,r,s)) and span([plane(k) for k in (p,q,r,s)],C,D),'zero parameter')
        elif op=='invalid':
            i,j=a[:2];require(0<=i<n and 0<=j<n and i!=j and qs[i]==qs[j],'duplicate bases')
            diff=lin([(1,zs[i]),(-1,zs[j])],d)
            if m==7:
                cert,den=a[2:];require(den!=0 and all(facts.get(k)==0 for k,c in cert) and lin([(c,plane(k)) for k,c in cert],d)==[den*x for x in diff],'duplicate height identity')
            else:require(not any(diff) or any(s==0 and plane(p) in (diff,negative(diff)) for p,s in path),'duplicate heights')
        elif op=='implied':
            p,s,cert,den,child=a;plane(p);require(p not in facts and s in (-1,0,1),'implied plane')
            u,pos=combo(path,cert)
            if s==0:require(den!=0 and all(path[k][1]==0 for k,c in cert),'implied equality')
            else:require(den>0 and pos,'implied strict sign')
            require(u==[den*(s or 1)*x for x in plane(p)],'implied identity')
            walk(child,path+[(p,s)],top)
        elif op=='sub':
            k,=a;require(top and 0<=k<len(F['subs']),'subtree reference')
            start,child=F['subs'][k];require(start==[list(t) for t in path],'subtree hypotheses');walk(child,path,False)
        else:raise ValueError(('unknown terminal',op))
    walk(F['tree'],[])
    return dict(records=len(records),planes=len(planes),vertical_facets=len(vf),nodes=dict(stats))

def sign_cube():
    data=json.loads(gzip.decompress((ROOT/'certificates'/'cube-5-sign-certificates.json.gz').read_bytes()))
    reps=data['reps'];certs=data['certs'];table=data['table'];results=[]
    require([e[0] for e in table]==[m for m in range(65536) if m.bit_count()==8],'all 12870 sign subsets')
    for M,r,p,eps in table:
        require(sorted(p)==list(range(5)) and 0<=r<len(reps),'signed permutation')
        out=[]
        for c in range(16):
            if not M&(1<<c):continue
            q=rep(c,5);g=[(-1 if eps&(1<<j) else 1)*q[p[j]] for j in range(5)]
            out.append(sum(1<<(j-1) for j in range(1,5) if g[j]!=g[0]))
        require(sorted(out)==reps[r],'cube representative map')
    for r,cert in zip(reps,certs):
        op,a=cert;qs=[rep(c,5) for c in r]
        if op=='nonspan':
            require(len(a)==5 and any(a) and all(dot(a,q)==0 for q in qs),'cube nonspan');results.append(0)
        else:
            require(op=='faces' and len(a)>=242,'cube faces');masks=[]
            for den,z,mask in a:
                require(den>0 and len(z)==5,'cube witness')
                vals=[dot(z,q) for q in qs]
                actual=sum(1<<i for i,x in enumerate(vals) if x==den)+sum(1<<(i+8) for i,x in enumerate(vals) if x==-den)
                require(max(map(abs,vals))<=den and mask==actual and mask!=0,'cube support witness');masks.append(mask)
            require(strict(masks),'distinct cube faces');results.append(len(masks)+1)
    return {'subsets':len(table),'representatives':len(reps),'certified_face_counts':results}

if __name__=='__main__':
    result={'whole_theorem_verified':False,'five_full_normals':sign_cube()}
    for m in (7,8):
        data=json.loads(gzip.decompress((ROOT/'certificates'/f'cube-{2*m}-certificates.json.gz').read_bytes()))
        report={'reduction':reduction(data),'families':[family_check(x['F'],m) for x in data['families']]}
        result[str(2*m)+'_vertices']=report
        print(2*m,'vertices: all families and reduction entries passed',flush=True)
    (ROOT/'evidence/cube-lift-checks.json').write_text(json.dumps(result,indent=2)+'\n')
    print('Five full normals: all 12870 subsets passed. Whole theorem: not asserted.')
