"""Further exact cost certificates, with explicit scope and coverage."""
import json
from verification.paths import ROOT

def add_extended_costs(p,eq,section,table,width):
    from .paper_endpoints import bound_text,tuple_text
    from verification.certificate_checks import global_inequalities
    section(34,'Further endpoint costs and the completed (16,16) case')
    p('We extend the affine cost of Section 22 by two terms: '
      'a·[2g&gt;τ] and [n=8](b+c r). Their sums are aK and '
      'bN₈+cR₈, where K counts facets above the stress threshold, '
      'N₈ counts eight-vertex facets and R₈ is their total ridge '
      'count. On any leaf where a≠0 we use 0≤K≤2. If M is '
      'the largest local g, this is justified whenever either '
      '2M≤τ, giving K=0, or 2M≥G−τ: all facet pairs '
      'other than a maximizing pair then have 2g≤G−2M≤τ '
      'by Section 25. The maximizing pair contains two facets. '
      'The same rule applies to the polar.')
    p('For a fixed n,e,r the extended local cost is affine in J '
      'on each of the two integer intervals split by '
      '2(J−3n−3r+10)≤τ. Check its endpoints, together with '
      'the elementary minimum recurrence of Section 22. The '
      'full-facet term is constant in J. Thus the local '
      'nonnegativity test is exact on the whole row domain; '
      'the discontinuous threshold is not minimized by assuming '
      'a single affine interval.')
    p('For full facets at v=16, Section 26 gives N₈=2k and '
      'R₈≤k(h+2k−4). The numbers for h=16,k=1,2,3 are '
      '14,32,54; those for h=20,k=7,8,9,10 are '
      '210,256,306,360. These are bounds for all realizations '
      'and do not require generic incidences.')
    p('<b>Proposition 34.1.</b> <i>A centrally symmetric five-polytope '
      'with v=h=16 has at least 243 nonempty faces.</i> If no '
      'facet is full, the one E case below applies. With one '
      'to three full pairs, a tetrahedron-prism facet on '
      'either side of polarity is excluded by Sections 16–17; '
      'otherwise the 25 G cases cover all slacks and local '
      'maxima. With at least four full pairs, full-normal '
      'rank is at least three by Section 28. Rank three '
      'is covered by Section 33; rank at least four by '
      'Sections 30–32, since h≤20. These alternatives '
      'exhaust every number of full pairs and every possible '
      'normal rank.')
    p('The same tables close (16,18) without full facets, '
      'and (16,20) with at least seven full pairs, after '
      'excluding the full tetrahedron-prism using '
      'Sections 16–17. For (18,20), the product row on '
      'P gives e≥72 and r≥50, hence t≥122. A product '
      'row only on the polar gives r≥66 by Section 21 '
      'and is included in C. Its remaining C cases '
      'require the tetrahedron-prism row to be absent '
      'on P or the indicated edge bound. D similarly '
      'handles the non-product, non-prism branches at '
      '(18,18), conditional on excluding row '
      '(9,19,17,7;38). Those two geometric exclusions '
      'are kept separate from the numerical computation.')
    table([
        ['<b>Group</b>','<b>Endpoint and geometric conditions</b>','<b>Cases</b>'],
        ['C','(18,20); product/prism rows as individually specified','25'],
        ['D','(18,18); product/prism/U rows as individually specified','216'],
        ['E','(16,16), no full facet','1'],
        ['F','(16,18), no full facet','14'],
        ['G','(16,16), k=1,2,3 full pairs, no prism on either side','25'],
        ['H','(16,20), k=7,8,9,10 full pairs, no prism on P','4']
    ],[35,width-80,45])
    p('Here is a finite coverage check written in terms of the actual '
      'integer quantities. First G,S≥0 are even and '
      'G+S≤vh−8(v+h)+26, namely 82,62,26,42,26,58 '
      'for C,D,E,F,G,H respectively. Enumerate each such '
      'pair and each integer M<sub>F</sub>∈[0,G/2], '
      'M<sub>S</sub>∈[0,S/2]. Retain the cases whose '
      'caps cover 2M and whose threshold satisfies the '
      'two alternatives proved above. If G=0 or S=0, '
      'include A=0 from Section 13. Split each remaining '
      'even nonnegative count axis at every printed '
      'boundary b and b+2; equality boundaries therefore '
      'stand in a separate cell. Each case condition is '
      'constant on a cell. The unbounded last cell is '
      'represented by its least value. This is an '
      'exhaustive interval partition, not a sampling argument.')
    p('For G and H fix N₈=2k. Every condition on R₈ is an '
      'upper bound, so it suffices to substitute the worst '
      'value k(h+2k−4); any smaller nonnegative value '
      'satisfies the same upper bounds. This partitions '
      '2,380 cells/maxima for E, 12,650 for F, 7,140 '
      'for G and 163,680 for H, and covers every one. '
      'The conditional non-product/non-prism branches '
      'of C and D cover 149,361 and 52,883 respectively. '
      'The tables below specify the full conditions, '
      'so the coverage calculation can be reconstructed '
      'using only integer intervals.')
    p('Each leaf retains Q₁,…,Q₂₃ from Section 22; Q₂₂,Q₂₃ '
      'now include the extra threshold and full-facet terms. '
      'The following U list first contains the threshold '
      'count bounds 0≤K≤2, then nonnegativity of N₈,R₈ '
      'when used, then the printed case conditions in '
      'order. An equality supplies its lower and upper '
      'form, lower first. As before z≥b means z−b, '
      'z≤b means b−z. The final identity for each leaf '
      'is a nonnegative integer combination equal to '
      'a negative constant. All local costs were '
      'checked on their complete finite row domains.')
    data=json.loads((ROOT/'certificates'/'extended-certificate-data.json').read_text())['leaves']
    raw=json.loads((ROOT/'evidence/extended-cost-checks.json').read_text())
    proofs={a['label']:a for a in raw['certificates']}
    numbers={}
    for leaf in data:
        pre=leaf['label'].split('_')[0]
        label={'E1820':'C','E1818':'D','E16f':'G','E20f':'H'}.get(pre)
        if pre=='E16k':label='E' if leaf['endpoint']==[16,16] else 'F'
        numbers[label]=numbers.get(label,0)+1;label+=str(numbers[label])
        proof=proofs[leaf['label']]
        p('<b>'+label+'.</b> nmax F/S='+str(leaf['nmaxF'])+'/'+str(leaf['nmaxS'])+
          '; cap F/S='+str(leaf['capF'])+'/'+str(leaf['capS'])+'. '
          'Exclude F: '+(', '.join(tuple_text(r) for r in leaf['excludedF']) or 'none')+
          '; S: '+(', '.join(tuple_text(r) for r in leaf['excludedS']) or 'none')+'.')
        for side,name in [('F','φ'),('S','ψ')]:
            text=name+'='+tuple_text(leaf['cost'+side])
            if 'threshold'+side in leaf:text+='; threshold (a,τ)='+tuple_text(leaf['threshold'+side])
            if 'full'+side in leaf:text+='; full (b,c)='+tuple_text(leaf['full'+side])
            p(text+'.')
        extra=global_inequalities(leaf)[23:]
        p('U: '+'; '.join(str(i+1)+': '+s.replace('>=','≥').replace('<=','≤') for i,(s,r) in enumerate(extra))+'.')
        terms=[]
        for key,w in sorted(proof['multipliers'].items(),key=lambda z:int(z[0])):
            i=int(key);ref='Q'+str(i+1) if i<23 else 'U'+str(i-22)
            terms.append(('' if w==1 else str(w)+'·')+ref)
        p('Identity: '+' + '.join(terms)+' = −'+str(-proof['constant'])+'.')
