"""Printed exact reduction to low-stress cells at the remaining endpoint."""
import json
from verification.paths import ROOT

def add_low18(p,eq,section,table,width):
    from .paper_endpoints import tuple_text
    from verification.certificate_checks import global_inequalities
    section(42,'Exact reduction of the few-full (16,18) branch')
    D=json.loads((ROOT/'certificates'/'low18-certificate-data.json').read_text())['leaves']
    proofdata=json.loads((ROOT/'evidence/low18-cost-checks.json').read_text())
    proofs={x['label']:x for x in proofdata['certificates']}
    coverage=json.loads((ROOT/'evidence/extended-coverage.json').read_text())['low18']
    p('Assume v=16,h=18,t≤118 and k=1,2,3 full '
      'facet pairs. A full tetrahedral prism has '
      'already been excluded. Both sides exclude '
      'the six impossible rows of Section 36. '
      'Every facet row also satisfies J≥4r, '
      'since every three-dimensional ridge has '
      'at least four vertices. The exact costs '
      'below use ρ or ρ′ from Section 41. '
      'No stronger weight is silently assumed.')
    p('For full facets N₈=2k and R₈≤k(18+2k−4), '
      'giving respectively 16,36,60. As in '
      'Section 34, every stress-threshold '
      'coefficient is summed using K≤2 '
      'only when 2M≤τ or 2M≥G−τ, '
      'where M is the largest local stress. '
      'The latter alternative is precisely '
      'the two-facet bound. Local nonnegativity '
      'is checked on the Section 22 row '
      'domain intersected with J≥4r.')
    p('Enumerate even G,S≥0 with G+S≤42 '
      'and both integer local maxima in '
      '[0,G/2] and [0,S/2]. Partition every '
      'remaining even count axis at b,b+2 '
      'as in Section 34. The following '
      '276 cases cover every cell except '
      'the explicitly listed residues. '
      'The coverage check visits '+str(coverage['cells_and_maxima'])+
      ' cells/maxima outside those residues, '
      'including all cases G≥16 or S≥16. '
      'Only '+str(coverage['leaves_used'])+
      ' of the printed leaves are needed '
      'by this enlarged interval coverage; '
      'extra valid leaves do not weaken '
      'the result.')
    table([['<b>k</b>','<b>Remaining (G,S) pairs</b>']]+
          [[k,', '.join(tuple_text(c) for c in cells)] for k,cells in coverage['residual_cells'].items()],
          [30,width-30])
    p('This is a necessary-cell reduction. Membership '
      'in the list does not assert that a polytope '
      'exists. At k=1 only (G,S)=(0,10) '
      'remains. At k=2 nine cells remain; '
      'at k=3 twenty-two. The r≥64 '
      'certificates below additionally show '
      'r≤62 for a counterexample. Hence '
      'Section 20 and Proposition 39.1 '
      'exclude both product rows Q and T '
      'on the polar. Section 38 excludes '
      'U on the polar as well. These '
      'exclusions are consequences, not '
      'hypotheses in the initial reduction.')
    p('Use Q₁,…,Q₂₃ from Section 22, with '
      'their two summed costs now including '
      'threshold, full and quadrilateral terms. '
      'The extra list U first gives '
      'QW≥0 and the quadrilateral budget '
      '4A+4f₀₃+4f₁₄−4I−6y−QW≥0; '
      'then the nonzero threshold-count '
      'bounds, nonnegativity of the full '
      'counts, and each printed bound '
      'in order. An equality supplies '
      'its lower then upper inequality. '
      'Every displayed integer combination '
      'has been recomputed using fractions '
      'and equals the printed negative '
      'constant exactly.')
    for i,x in enumerate(D,1):
        q=proofs[x['label']]
        p('<b>L'+str(i)+'.</b> '+('ρ′' if x['row_weight']=='q55refined' else 'ρ')+
          '; cap F/S='+str(x['capF'])+'/'+str(x['capS'])+'.')
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
