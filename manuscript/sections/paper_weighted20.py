"""Exact cost closure of the one-to-three-full-pair (16,20) cases."""
import json
from verification.paths import ROOT

def add_weighted20(p,eq,section,table,width):
    from .paper_endpoints import tuple_text
    from verification.certificate_checks import global_inequalities
    section(37,'Completion of the (16,20) endpoint')
    p('<b>Proposition 37.1.</b> <i>Every centrally symmetric '
      'five-polytope with v=16 and h=20 has at least 243 '
      'nonempty faces.</i> Section 35 proves the no-full '
      'case. With at least four full pairs the full-normal '
      'rank is at least three: rank three is covered by '
      'Section 33, and rank at least four by Sections '
      '30–32. It remains to treat one, two or three '
      'full pairs. A full tetrahedron-prism gives the '
      'bound by Sections 16–17, so exclude that row '
      'on the facet side. The six impossible rows '
      'of Section 36 are excluded on both sides.')
    p('Extend the costs of Section 34 by μλ(R), where '
      'λ is the row weight of Section 36. The facet '
      'sum acquires μW. Every polar cost below has '
      'μ=0, so no quadrilateral budget for the '
      'twenty-vertex polar is assumed. On both '
      'sides use J≥4r in the local row domain. '
      'The full-ridge bound is N₈=2k and '
      'R₈≤18,40,66 for k=1,2,3. As in Section '
      '34, threshold counts are at most two '
      'when their printed cap covers a maximizing '
      'local g and the threshold satisfies '
      '2M≤τ or 2M≥G−τ.')
    p('Below Q₁,…,Q₂₃ retain their meaning, with '
      'threshold, full and μW terms included in '
      'the two costs. The U list first contains '
      'W≥0 and the budget of Section 36, then '
      'the threshold and full-count bounds, then '
      'the case conditions. Equalities are lower '
      'then upper. All integers multiplying Q or '
      'U are nonnegative. Each printed identity '
      'is a negative constant, proving its branch '
      'impossible under t≤118.')
    data=json.loads((ROOT/'certificates'/'weighted20-certificate-data.json').read_text())['leaves']
    proofs={a['label']:a for a in json.loads((ROOT/'evidence/weighted20-cost-checks.json').read_text())['certificates']}
    for num,leaf in enumerate(data,1):
        proof=proofs[leaf['label']]
        p('<b>J'+str(num)+'.</b> nmax F/S=8/10; cap F/S='
          +str(leaf['capF'])+'/'+str(leaf['capS'])+'.')
        for side,name in [('F','φ'),('S','ψ')]:
            p(name+'='+tuple_text(leaf['cost'+side])+'; threshold (a,τ)='
              +tuple_text(leaf['threshold'+side])+'; full (b,c)='
              +tuple_text(leaf['full'+side])+'; μ='+str(leaf['quad'+side])+'.')
        p('U: '+'; '.join(str(i+1)+': '+s.replace('>=','≥').replace('<=','≤')
              for i,(s,r) in enumerate(global_inequalities(leaf)[23:]))+'.')
        terms=[]
        for key,w in sorted(proof['multipliers'].items(),key=lambda z:int(z[0])):
            i=int(key);ref='Q'+str(i+1) if i<23 else 'U'+str(i-22)
            terms.append(('' if w==1 else str(w)+'·')+ref)
        p('Identity: '+' + '.join(terms)+' = −'+str(-proof['constant'])+'.')
    evidence=json.loads((ROOT/'evidence/extended-coverage.json').read_text())['weighted20']
    p('For completeness, coverage is checked by the following '
      'explicit integer partition. For each k=1,2,3 set '
      'N₈=2k and R₈=k(20+2k−4); every R₈ condition '
      'is an upper bound, so a smaller actual value '
      'satisfies the same leaves. Enumerate nonnegative '
      'even G,S with G+S≤58 and maxima '
      '0≤M<sub>F</sub>≤G/2,0≤M<sub>S</sub>≤S/2. '
      'Discard a leaf whose cap is below 2M, or '
      'whose nonzero threshold coefficient does not '
      'satisfy the preceding alternatives. When '
      'G=0 or S=0 use A=0; otherwise discard leaves '
      'requiring A=0. On every remaining even count '
      'axis, split at all printed boundaries b and '
      'b+2, retaining the unbounded last interval. '
      'Each condition is constant on each interval, '
      'so testing its least value is exact. This '
      'partition has '+format(evidence['cells_and_maxima'],',')+
      ' cells/maxima, all covered by the printed '
      'leaves. Together with their exact local '
      'nonnegativity and negative global identities '
      'this completes the few-full case and proves '
      'Proposition 37.1.')
