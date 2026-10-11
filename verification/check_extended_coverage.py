#!/usr/bin/env python3
"""Exhaustive even-integer interval coverage of the printed conditional costs."""
import json,itertools,time
from .paths import ROOT as P
def holds(z,s,b):return z>=b if s=='>=' else z<=b if s=='<=' else z==b

def covered(group,v,h,roots,residual=None,only_cells=None):
 bound=v*h-8*(v+h)+26;axes=set();used=set();n=0
 for fixedextra in roots:
  for G in range(0,bound+2,2):
   for S in range(0,bound-G+2,2):
    fixed={'G':G,'S':S,**fixedextra}
    if only_cells is not None and (G,S) not in only_cells[fixedextra['nF8']//2]:continue
    if residual and (G,S) in residual[fixedextra['nF8']//2]:continue
    active=[]
    for leaf in group:
     if any(not holds(fixed[k],s,b) for k,s,b in leaf['bounds'] if k in fixed):continue
     if any(k=='A' and not ((G==0 or S==0) and s=='=' and b==0) for k,s,b in leaf['bounds']):continue
     active.append(leaf)
    # Always enumerate exact local maxima; these are integers bounded by G/2,S/2.
    for mF,mS in itertools.product(range(G//2+1),range(S//2+1)):
     viable=[]
     for leaf in active:
      ok=True
      for side,g,m in [('F',G,mF),('S',S,mS)]:
       if 2*m>leaf['cap'+side]:ok=False;break
       ag,tau=leaf.get('threshold'+side,[0,1000])
       if ag and not (2*m<=tau or 2*m>=g-tau):ok=False;break
      if not ok:continue
      cond=[]
      for k,s,b in leaf['bounds']:
       if k in fixed or k=='A' or (k=='t' and s=='<=' and b==118):continue
       cond.append((k,s,b))
      viable.append((leaf['label'],cond))
     axes=sorted({k for _,c in viable for k,_,_ in c});cuts={}
     for k in axes:
      C={0}
      for _,c in viable:
       for var,s,b in c:
        if var==k:
         if b%2:raise ValueError(('non-even cutoff',k,b))
         C.add(max(0,b));C.add(max(0,b+2))
      cuts[k]=sorted(z for z in C if k!='t' or z<=118)
     for vals in itertools.product(*(cuts[k] for k in axes)):
      point=dict(zip(axes,vals));n+=1
      match=[label for label,c in viable if all(holds(point[k],s,b) for k,s,b in c)]
      if not match:raise ValueError(('uncovered',v,h,fixed,mF,mS,point))
      used.update(match)
 return {'status':'passed','cells_and_maxima':n,'leaves_used':len(used),'global_slack_bound':bound}
def main():
 D=json.loads((P/'certificates'/'extended-certificate-data.json').read_text())['leaves'];out={}
 for pre,v,h,exlen,roots in [('E1820',18,20,2,[{}]),('E1818',18,18,3,[{}]),('E16k',16,16,0,[{}]),('E16k',16,18,0,[{}]),('E16f',16,16,1,[{'nF8':2*k,'rF8':k*(16+2*k-4)} for k in (1,2,3)]),('E20f',16,20,1,[{'nF8':2*k,'rF8':k*(20+2*k-4)} for k in (7,8,9,10)])]:
  group=[x for x in D if x['label'].startswith(pre+'_') and x['endpoint']==[v,h] and len(x['excludedF'])==exlen]
  out[pre+'_'+str(h)]=covered(group,v,h,roots)
 D=json.loads((P/'certificates'/'weighted20-certificate-data.json').read_text())['leaves']
 if any(x.get('quadS') for x in D):raise ValueError('Unexpected polar quadrilateral budget')
 out['weighted20']=covered(D,16,20,[{'nF8':2*k,'rF8':k*(20+2*k-4)} for k in (1,2,3)])
 D=json.loads((P/'certificates'/'extended-certificate-data.json').read_text())['leaves']
 for label,axis,minimum in [('E1818_B1','e',72),('E1818_B2','r',72),('E1818_B3','e',64),('E1818_B4','r',64),('E1820_B2','r',66)]:
  leaf=next(x for x in D if x['label']==label)
  out[label]=covered([leaf],*leaf['endpoint'],[{axis:minimum}])
 group=[x for x in D if x['label'].startswith('E1820_B3')]
 out['E1820_prism']=covered(group,18,20,[{'e':64}])
 D=json.loads((P/'certificates'/'low18-certificate-data.json').read_text())['leaves']
 residual={1:{(0,10)},2:{(0,10),(2,2),(2,4),(2,6),(2,8),(2,10),(4,2),(4,4),(4,6)},
           3:{(0,10),(2,2),(2,4),(2,6),(2,8),(2,10),(2,12),(4,2),(4,4),(4,6),
              (4,8),(4,10),(4,12),(4,14),(6,2),(6,4),(6,6),(6,8),(6,10),(8,6),(8,8),(8,10)}}
 out['low18']=covered(D,16,18,[{'nF8':2*k,'rF8':k*(18+2*k-4)} for k in (1,2,3)],residual)
 out['low18']['residual_cells']={str(k):sorted(cells) for k,cells in residual.items()}
 r64=[x for x in D if '_polar_r' in x['label']]
 out['low18_r64_residues']=covered(r64,16,18,
   [{'nF8':2*k,'rF8':k*(18+2*k-4),'r':64} for k in (1,2,3)],only_cells=residual)
 print(json.dumps(out,indent=2))

if __name__=='__main__':main()
