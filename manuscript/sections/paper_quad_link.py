"""The quadrilateral-link proof and the complete no-full (16,20) case."""
import json
from verification.paths import ROOT

def add_quad_link(p,eq,section,table,width):
    from .paper_endpoints import tuple_text
    from verification.certificate_checks import global_inequalities
    section(35,'Quadrilateral links and (16,20) without full facets')
    p('For a four-dimensional facet H put q₄(H)=# {quadrilateral faces of H} '
      'and η(H)=Σ<sub>Q⊂H,dim Q=2</sub>(#vert Q−3). Counting vertex–polygon '
      'incidences inside H gives η=J+n−e−3r. In particular q₄≤η. '
      'Call H good if its row is Y=(7,15,14,6;29) or E=(7,16,16,7;32). '
      'The small catalogue gives η(Y)=q₄(Y)=3 and η(E)=2. It also gives '
      'the following incidence property: every quadrilateral in a good H '
      'belongs to exactly one five-vertex three-face of H.')
    p('Here is an explicit way to check the last assertion, including its '
      'incidence content. For every admissible seven-point signed Gale code '
      'of Section 7 form the face masks by the positive-circuit criterion. '
      'Retain the codes with row Y or E. For each two-face mask Q with '
      'four bits, count the three-face masks T with five bits and Q⊂T; '
      'the count is one. This is an exhaustive combinatorial check of '
      'all realizable codes, rather than a test on chosen coordinates. '
      'The three-face profiles are, for Y, two tetrahedra, three square '
      'pyramids and one triangular prism; for E they are either four '
      'tetrahedra, two square pyramids and one three-face with '
      '(n,e,p)=(6,10,6), or five tetrahedra and two three-faces '
      'with (n,e,p)=(6,10,6). In the latter profile '
      'there is no quadrilateral. The mask check specifies which of '
      'these faces meet, so it proves the stated incidence count as well '
      'as their numbers.')
    p('Fix a quadrilateral Q of the five-polytope. Write ℓ for the '
      'number of facets through Q and a for the number of good ones. '
      'The link of Q is a polygon, so ℓ≥3. If all ℓ facets are good, '
      'the number of pairs (H,T), where Q⊂T⊂H and T has five vertices, '
      'is ℓ. Every T is in exactly two facets; thus ℓ is even and ℓ≥4. '
      'In this case a−2(ℓ−a)=ℓ≤4(ℓ−3). Otherwise a≤ℓ−1, giving '
      '3a−2ℓ≤ℓ−3≤4(ℓ−3). Consequently, in all cases')
    eq('a−2(ℓ−a) ≤ 4(ℓ−3).','35.1')
    p('Sum (35.1) over quadrilaterals. The left side becomes '
      'Σ<sub>H good</sub>q₄(H)−2Σ<sub>H not good</sub>q₄(H). '
      'The right side is at most 4A, because '
      'A=Σ<sub>Q</sub>(#vert Q−3)(ℓ(Q)−3), and the terms for '
      'other polygons are nonnegative. Add 2Ση(H). A Y facet now '
      'contributes 3+2·3=9; an E facet contributes q₄+4≥4; '
      'every other facet contributes −2q₄+2η≥0. Hence, with '
      'W=9#Y+4#E,')
    eq('0≤W≤4A+2(f₀₂₄−3y),<br/>f₀₂₄=2f₀₃+2f₁₄−2I.','35.2')
    p('The second equality follows by summing '
      'f₀₂(H)=J(H)+2e(H)−2n(H) over H: ΣJ=2f₀₃, '
      'Σe(H)=f₁₄ and Σn(H)=I. Thus (35.2) is entirely in '
      'the global variables of Section 22.')
    p('<b>Proposition 35.1.</b> <i>If v=16,h=20 and no facet is full, '
      'then s(P)≥243.</i> All facet rows have n≤7, and all polar '
      'facet rows have n≤10. Extend a facet cost φ of Section 22 '
      'by μ(9[Y]+4[E]). Its sum is the ordinary sum of φ plus μW. '
      'The polar cost is unchanged. The following seven exact '
      'certificates prove a contradiction under t≤118.')
    p('For each leaf use Q₁,…,Q₂₃ as before, with μW included in '
      'Q₂₂. Set U₁=W and U₂=4A+4f₀₃+4f₁₄−4I−6y−W. '
      'These are nonnegative by (35.2). The subsequent U entries '
      'are the case conditions below, written as their '
      'nonnegative differences; an equality is written lower '
      'then upper. Every identity is an exact integer identity '
      'in the displayed global variables.')
    data=json.loads((ROOT/'certificates'/'quad-certificate-data.json').read_text())['leaves']
    proofs={a['label']:a for a in json.loads((ROOT/'evidence/quad-cost-checks.json').read_text())['certificates']}
    for k,leaf in enumerate(data,1):
        proof=proofs[leaf['label']]
        p('<b>I'+str(k)+'.</b> Cap F/S='+str(leaf['capF'])+'/'+str(leaf['capS'])+
          '; φ='+tuple_text(leaf['costF'])+'; μ='+str(leaf.get('quadF',0))+
          '; ψ='+tuple_text(leaf['costS'])+'.')
        p('U: '+'; '.join(str(i+1)+': '+s.replace('>=','≥').replace('<=','≤')
              for i,(s,r) in enumerate(global_inequalities(leaf)[23:]))+'.')
        terms=[]
        for key,w in sorted(proof['multipliers'].items(),key=lambda z:int(z[0])):
            i=int(key);ref='Q'+str(i+1) if i<23 else 'U'+str(i-22)
            terms.append(('' if w==1 else str(w)+'·')+ref)
        p('Identity: '+' + '.join(terms)+' = −'+str(-proof['constant'])+'.')
    p('To see the coverage without any numerical assumption, G and S '
      'are nonnegative even integers. If G≥4 use I1. If G=0 use I2; '
      'Section 13 gives A=0. Otherwise G=2. The alternatives S=0 '
      'and S≥4 use I3 and I4, with A=0 in the former. In the '
      'remaining case G=S=2, even t is either at most 116 or is '
      '118. Use I5 in the first case. In the second, even e is '
      'either at most 56 or at least 58; use I6 or I7 respectively. '
      'The caps are valid since 2g(H)≤G and, on the polar, '
      '2g(H*)≤S. A cap of 1000 safely covers G+S≤58. '
      'All local costs are nonnegative on the complete row '
      'domain by the catalogue and the finite affine check of '
      'Section 22. This proves Proposition 35.1.')
