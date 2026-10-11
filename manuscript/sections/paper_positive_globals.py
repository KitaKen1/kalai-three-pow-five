"""Printed rational identities fixing the positive two-pair face vector."""
import json
from verification.paths import ROOT

def add_positive_globals(p,eq,section,table,width):
    from .paper_endpoints import tuple_text
    from verification.certificate_checks import global_inequalities
    section(45,'The global counts in the positive two-pair cells')
    p('There are four full facets. Hence I≤4·8+14·7=130. '
      'The local stress sum is Σg(F)=2G+128−I. At G=2 '
      'each local stress is at most one, and Section 34 bounds '
      'the number of positive-stress facets by two. Thus I=130. '
      'At G=4 a facet with g=2 would, by the same two-facet '
      'bound with threshold two, allow at most two positive '
      'facets, each with g≤2. This contradicts '
      'Σg(F)≥6. Consequently g(F)≤1 in all eight positive cells.')
    p('We claim e=58,r=60,I=130. The following 27 rational '
      'identities prove the claim without assuming those counts. '
      'Their row domain is Section 22 with n≤8 on P and n≤9 '
      'on the polar, intersected with J≥4r. Both domains omit '
      'the impossible rows of Section 36 and the product T; '
      'the polar also omits Q and U by Sections 20,38,39,42. '
      'The local stress cap on P is one, that on the polar '
      'is S/2. The costs use the Section 41 weight with '
      'the B entry raised to five, valid by Lemma 44.1. '
      'The full count is N₈=4 and R₈≤36, and I≤130. '
      'For G=2 the threshold-zero count is at most two; '
      'for G=4 the threshold-two count is zero.')
    p('As before, Q₁,…,Q₂₃ are the base inequalities and '
      'U lists the additional quadrilateral, threshold, full-count '
      'and cell bounds in order. The coefficient vectors φ,ψ '
      'use the Section 34 order. Every multiplier in the '
      'identity is nonnegative, and its sum is the stated '
      'negative integer. These identities therefore exclude '
      'the stated branches for every admissible real polytope.')
    D=json.loads((ROOT/'certificates'/'positive-certificate-data.json').read_text())['leaves']
    proofs={x['label']:x for x in json.loads((ROOT/'evidence/positive-cost-checks.json').read_text())['certificates']}
    for i,x in enumerate(D,1):
        q=proofs[x['label']]
        p('<b>P'+str(i)+'.</b> '+x['label'].replace('_',' ')+'; '
          'cap F/S='+str(x['capF'])+'/'+str(x['capS'])+'.')
        for side,name in [('F','φ'),('S','ψ')]:
            p(name+'='+tuple_text(x['cost'+side])+'; threshold='+tuple_text(x['threshold'+side])+
              '; full='+tuple_text(x['full'+side])+'; µ='+str(x['quad'+side])+'.')
        extra=global_inequalities(x)[23:]
        p('U: '+'; '.join(str(j+1)+': '+s.replace('>=','≥').replace('<=','≤')
                          for j,(s,_) in enumerate(extra))+'.')
        terms=[]
        for key,w in sorted(q['multipliers'].items(),key=lambda z:int(z[0])):
            j=int(key);ref='Q'+str(j+1) if j<23 else 'U'+str(j-22)
            terms.append(('' if w==1 else str(w)+'·')+ref)
        p('Identity: '+' + '.join(terms)+' = −'+str(-q['constant'])+'.')
    p('Coverage is particularly short here. Since e is even, '
      'the alternatives are e≤56, e=58 and e≥60; the first '
      'and third are excluded in each cell. At e=58, '
      'even t≤118 is either at most 116 or equal to 118; '
      'the former is excluded. Thus r=60. For G=2, '
      'I=130 was already proved. For G=4, even I≤130 '
      'is either at most 128 or equal to 130; the former '
      'is excluded. Euler then gives p=86. We have proved')
    eq('(v,e,p,r,h)=(16,58,86,60,18), I=130,<br/>'
       'Σ<sub>F</sub>g(F)=2G−2, '
       'Σ<sub>F</sub>w(F)≤156−6S.','45.1')
    p('Here w=q−3b+2η is the actual geometric weight. '
      'The last inequality is Section 36 with these global '
      'counts substituted. The equality I=130 also forces '
      'all fourteen nonfull facets to have seven vertices.')
