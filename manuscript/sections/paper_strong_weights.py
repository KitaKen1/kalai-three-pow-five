"""Catalogue-free strengthened Q55 weights used at the remaining endpoint."""
import json
from verification.paths import ROOT

def add_strong_weights(p,eq,section,table,width):
    from .paper_endpoints import tuple_text
    section(41,'Stronger quadrilateral weights from ridge counts')
    p('Use q for the number of quadrilaterals in a '
      'four-dimensional facet, b for those between '
      'two five-vertex ridges, and η for its polygon '
      'excess. Section 36 proved the global budget '
      'for w=q−3b+2η. We now prove stronger '
      'local lower bounds without classifying all '
      'eight-vertex four-polytopes. The twelve '
      'ridge types and their count variables '
      'c₁,…,c₁₂ are exactly those of Section 36.')
    p('<b>Reserved quadrilaterals.</b> A quadrilateral '
      'inside a ridge with other than five vertices '
      'does not contribute to b. A triangular '
      'prism therefore reserves three such '
      'quadrilaterals, so b+3≤q. Two distinct '
      'prisms share at most one two-face: their '
      'intersection is a single proper face '
      'of each, and any two-dimensional face '
      'in that intersection must equal it. '
      'Thus two prisms reserve at least five '
      'distinct quadrilaterals and b+5≤q.')
    p('An eight-vertex facet with a seven-vertex '
      'ridge is a pyramid: its remaining vertex '
      'is outside the ridge hyperplane and the '
      'facet is their convex hull. Every '
      'two-face outside the base is a triangle '
      'over a base edge. Hence every quadrilateral '
      'lies in the seven-vertex base. In '
      'particular b=0. Each square-pyramidal '
      'ridge has a different quadrilateral '
      'base shared with that seven-vertex '
      'ridge, giving q≥c₂.')
    p('<b>Excess and long polygons.</b> A quadrilateral '
      'contributes one to η, and a polygon '
      'with at least five vertices contributes '
      'at least two. Consequently η−q '
      'cannot equal one. If q=η all '
      'polygons are triangles or quadrilaterals. '
      'For a three-dimensional ridge of row '
      '(n,e,r), its polygon excess is '
      '2e−3r, by counting edge–polygon '
      'incidences. Thus in this last case '
      'it has exactly 2e−3r quadrilaterals. '
      'For every non-five-vertex ridge these '
      'are reserved, and b+(2e−3r)≤q.')
    p('The arithmetic is now completely specified. '
      'For each count vector in the recurrence '
      'of Section 36, retain the three local '
      'polygon restrictions P1–P3 and the '
      'two tetrahedron–pyramid parity exclusions '
      'proved there. Enumerate integers q,b '
      'with 0≤b≤q≤η, 2b≤c₂ and '
      '2q≥c₂+3c₄. Delete η−q=1; '
      'apply b=0,q≥c₂ if a seven-vertex '
      'ridge occurs, b+3≤q if c₄≥1, '
      'b+5≤q if c₄≥2, and the reserved '
      'excess inequalities when q=η. '
      'These are all necessary conditions '
      'proved above, so minimization over '
      'this enlarged integer set is a '
      'valid lower bound for every real facet.')
    D=json.loads((ROOT/'evidence/ridge-count-checks.json').read_text())['strong_weights']
    table([['<b>Facet row</b>','<b>η</b>','<b>Raw count vectors</b>',
            '<b>Minimum w</b>','<b>Used bound</b>']]+
          [[tuple_text(x['row']),str(x['row'][4]+x['row'][0]-x['row'][1]-3*x['row'][3]),
            str(len(x['raw_profiles'])),str(x['minimum']),str(x['claimed_bound'])] for x in D],
          [width*.43,width*.07,width*.19,width*.15,width*.16])
    p('For transparency, the complete raw count vectors '
      'are printed below in the twelve-type order. '
      'The count equations determine each finite '
      'list; no realization assumption is made '
      'about any vector. The supplied independent '
      'integer recurrence produces precisely '
      'these lists and checks the displayed minima.')
    for x in D:
        p('<b>'+tuple_text(x['row'])+'.</b> '+
          '; '.join(tuple_text(c) for c in x['raw_profiles'])+'.')
    p('A useful short explanation of the weight-three '
      'bounds is also available. For η=3, '
      'w&lt;3 forces q≥2 because b≤q. '
      'Since η−q≠1, necessarily q=3. '
      'Then w=9−3b&lt;3 forces b=3 '
      'and at least six square pyramids. '
      'For row (8,19,19,8;38), the '
      'count equations leave two tetrahedra '
      'and six square pyramids; for '
      '(8,20,20,8;39), one tetrahedron, '
      'one triangular bipyramid and six '
      'square pyramids. Both violate '
      'the vertex parity argument of '
      'Section 36. The reserved-quadrilateral '
      'inequality further raises the first '
      'row’s bound to four, as the full '
      'integer table records.')
    p('Let ρ be the Section 36 weight with '
      'the six entries above replaced by '
      '3,3,8,10,8,12 respectively in the '
      'displayed row order. Let ρ′ replace '
      'only its first entry by four. '
      'All earlier entries retain their '
      'proved bounds. Both satisfy, at '
      'sixteen vertices,')
    eq('Σ<sub>F</sub>ρ(F)≤4A+2(f₀₂₄−3y),<br/>'
       'Σ<sub>F</sub>ρ′(F)≤4A+2(f₀₂₄−3y).','41.1')
    p('The second inequality is stronger. The '
      'first is retained where a certificate '
      'uses only the smaller entry; this '
      'cannot invalidate its conclusion.')
