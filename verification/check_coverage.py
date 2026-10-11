import json,itertools
from .paths import ROOT as P
d=json.loads((P/'certificates'/'mathematical-certificate-data.json').read_text())
# Divide the nonnegative even axes at every printed boundary; this checks
# entire orthants, not only sample points or a bounded scan.
def check(leaves,fixed):
 L=[]
 for leaf in leaves:
  if any((not (fixed[k]>=b if s=='>=' else fixed[k]<=b if s=='<=' else fixed[k]==b)) for k,s,b in leaf['bounds'] if k in fixed):continue
  ok=True;cond=[]
  for k,s,b in leaf['bounds']:
   if k=='A':
    if not ((fixed.get('G')==0 or fixed.get('S')==0) and s=='=' and b==0):
     raise ValueError(('unjustified zero A',leaf['label']))
    continue
   if k in fixed:
    z=fixed[k]
    ok &= z>=b if s=='>=' else z<=b if s=='<=' else z==b
   elif k=='t' and s=='<=' and b==118:continue
   else:cond.append((k,s,b))
  if ok:L.append((leaf['label'],cond))
 axes=sorted({k for _,c in L for k,_,_ in c})
 def cells(k):
  cut={0}
  for _,c in L:
   for var,s,b in c:
    if var!=k:continue
    if b%2:raise ValueError(('odd printed boundary',k,b))
    cut.add(max(0,b));cut.add(max(0,b+2))
  C=sorted(cut)
  if k=='t': C=[z for z in C if z<=118]
  return C
 n=0;used=set()
 for vals in itertools.product(*(cells(k) for k in axes)):
  point=dict(zip(axes,vals));n+=1
  found=[]
  for label,c in L:
   if all(point[k]>=b if s=='>=' else point[k]<=b if s=='<=' else point[k]==b for k,s,b in c):found.append(label)
  if not found:raise ValueError(('uncovered',fixed,point))
  used.update(found)
 return n,used
report={}
for pre,GS in [('E1822',106),('E2020',106)]:
 L=[z for z in d['leaves'] if z['label'].startswith(pre+'_')]
 if pre=='E2020':L=[z for z in L if z['label'] not in ('E2020_A','E2020_B')]
 n=0;used=set()
 # All global slacks satisfy G+S <= vh-8(v+h)+26 = 106.
 # Include larger axis tails as well; high-cell leaves cover them.
 for g,s in itertools.product(range(0,GS+4,2),repeat=2):
  count,u=check(L,{'G':g,'S':s});n+=count;used.update(u)
 report[pre]={'axis_cells_checked':n,'leaves_used':len(used),'slack_bound':GS,'status':'passed'}
print(json.dumps(report,indent=2))
