"""Full mathematical proof of the Q55 budget and the weak row-weight table."""
import json
from verification.paths import ROOT

def add_q55(p,eq,section,table,width):
    from .paper_endpoints import tuple_text
    section(36,'A quadrilateral budget at sixteen vertices')
    p('Let Q be a quadrilateral contained in a facet H. Exactly two '
      'three-faces R,S of H contain Q, and R∩S=Q. Each has at least '
      'five vertices, and |vert R|+|vert S|≤|vert H|+4≤12 when '
      'v(P)=16. If both have at least six vertices, equality forces '
      'H to be full and vert H=vert R∪vert S. We first show that '
      'this full-cover situation forces at least four facets through Q.')
    p('Suppose instead that there are exactly three, H,H<sub>R</sub>, '
      'H<sub>S</sub>, where H<sub>R</sub> and H<sub>S</sub> are the other '
      'facets through R and S. They are distinct: otherwise that '
      'facet contains vert R∪vert S=vert H and equals H. The polygon '
      'link of Q is a triangle. Its third three-face T belongs to '
      'H<sub>R</sub> and H<sub>S</sub> and is not in H. A vertex '
      'w of T outside H has −w in H, since H is full. The cover '
      'puts −w in R or S, hence in H<sub>R</sub> or H<sub>S</sub>. '
      'That proper facet already contains w, giving an antipodal '
      'pair, which is impossible. Thus every vertex of T lies '
      'in H, contradicting T⊄H. This proves the assertion.')
    p('Define b₅₅(H) to be the number of quadrilaterals of H whose '
      'two containing three-faces both have five vertices, and '
      'w(H)=q₄(H)−3b₅₅(H). For a Q in exactly three facets, '
      'each facet has at most one containing three-face with '
      'other than five vertices, by the preceding cover argument. '
      'The sum of these numbers is even, since every three-face '
      'through Q occurs twice. Of three numbers in {0,1}, '
      'at least one is zero. Thus at least one of the three '
      'facets contributes −2 to w at Q; the other two '
      'contribute at most 1, and their sum is at most zero. '
      'For ℓ≥4 the sum is at most ℓ≤4(ℓ−3). Summing gives')
    eq('Σ<sub>H</sub>w(H)≤4A,<br/>Σ<sub>H</sub>(w(H)+2η(H)) '
       '≤4A+2(f₀₂₄−3y).','36.1')
    p('The same nonnegative quantity w+2η admits useful lower '
      'bounds depending only on the row. In general b₅₅≤q₄≤η, '
      'so w+2η≥0. In a five-vertex three-polytope, a '
      'quadrilateral can occur only in the square pyramid '
      '(5,8,5), whose base is its unique quadrilateral. Hence, '
      'if a is the number of square-pyramidal three-faces '
      'and c the number of triangular-prismatic ones,')
    eq('2b₅₅≤a,     2q₄≥a+3c.','36.2')
    p('The first inequality counts two pyramids at each (5,5) '
      'quadrilateral. The second counts their bases and the '
      'three quadrilaterals of each triangular prism, with '
      'every quadrilateral counted at most twice.')
    p('We also need to exclude six purely numerical rows with '
      'eight vertices. Every proper three-face of such a facet '
      'has at most seven vertices. Euler and the degree bounds '
      '2e≥3n and 2e≥3p leave exactly the following possible '
      'three-face number triples. The ordering is fixed for '
      'the count vectors below.')
    triples=[(4,6,4),(5,8,5),(5,9,6),(6,9,5),(6,10,6),(6,11,7),
             (6,12,8),(7,11,6),(7,12,7),(7,13,8),(7,14,9),(7,15,10)]
    p('; '.join(str(i+1)+': '+tuple_text(t) for i,t in enumerate(triples))+'.')
    p('Write cᵢ for these twelve counts, and N for the number of '
      'three-faces having a nontriangular polygon. The exact '
      'equations are Σcᵢ=r, Σnᵢcᵢ=J and Σpᵢcᵢ=2p. '
      'Moreover N=c₂+c₄+c₅+c₆+c₈+c₉+c₁₀+c₁₁. '
      'Three elementary incidence restrictions suffice:')
    eq('c₄&gt;0 ⇒ N≥4;<br/>c₈&gt;0 ⇒ N≥3;<br/>'
       'c₄≥2 and c₂&gt;0 ⇒ N≥5.','36.3')
    p('For their proofs, every nontriangular polygon of a '
      'three-face T has a unique partner three-face of H. '
      'Different polygons of T have different partners, '
      'since two distinct three-faces meet in a single '
      'proper face. Thus N is at least one plus the number '
      'of nontriangular polygons of T. A triangular prism '
      'has three, proving the first restriction. A '
      '(7,11,6) three-polytope has polygon excess '
      '2·11−3·6=4. Each of its polygons has at most five '
      'sides, since its distinct edges require distinct '
      'other facets among the remaining five; it therefore '
      'has at least two nontriangular polygons. This proves '
      'the second restriction. Finally, if two prisms and '
      'a square pyramid belonged to at most four '
      'nonsimplicial three-faces, each prism would have '
      'all three other faces as partners. Each prism '
      'would share a quadrilateral with the pyramid. '
      'Those quadrilaterals are distinct, since each '
      'polygon lies in exactly two three-faces. This '
      'contradicts the pyramid’s unique quadrilateral '
      'and proves the third restriction.')
    raw=json.loads((ROOT/'evidence/ridge-count-checks.json').read_text())
    p('Solving the three count equations with cᵢ≥0 for each '
      'row below gives exactly the listed vectors. Every '
      'one violates (36.3), so none of the six rows is '
      'geometrically possible. The lists are short enough '
      'to check by substitution; a systematic enumeration '
      'chooses c₁ from 0 to r, subtracts its contributions, '
      'then c₂, and so on, rejecting a negative remainder. '
      'At the twelfth step all three remainders must be zero.')
    for row in raw['fake_rows']:
        p('<b>Excluded row '+tuple_text(row['row'])+'.</b> '
          +'; '.join(tuple_text(c) for c in row['raw_profiles'])+'.')
    p('One additional obstruction comes from vertex parity. '
      'At each vertex x of H, the degrees of x in its '
      'incident three-faces sum to twice the number of '
      'polygons of H through x: this is the face–edge '
      'count in the three-dimensional vertex figure. '
      'A tetrahedron contributes degree 3. A square '
      'pyramid contributes 4 minus the indicator that '
      'x belongs to its quadrilateral base. These '
      'base indicators sum to an even number because '
      'each quadrilateral belongs to two three-faces. '
      'If every three-face is a tetrahedron or square '
      'pyramid, the number of tetrahedra through each '
      'vertex is therefore even. Exactly two tetrahedra '
      'would have identical vertex sets, a contradiction. '
      'The same argument outside one exceptional '
      'three-face shows that a single tetrahedron and '
      'square pyramids cannot occur with just that '
      'exception: all tetrahedron vertices would lie '
      'in the distinct exceptional three-face.')
    p('Here is the row-weight table used below. Unlisted '
      'rows have weight zero. Each entry λ(R) satisfies '
      'λ(R)≤w(H)+2η(H) for a facet with row R.')
    table([['<b>Row R</b>','<b>λ(R)</b>'],
        [tuple_text((7,15,14,6,29)),'9'],[tuple_text((7,16,16,7,32)),'4'],
        [tuple_text((8,18,17,7,36)),'15'],[tuple_text((8,18,17,7,35)),'10'],
        [tuple_text((8,19,18,7,35)),'9'],[tuple_text((8,19,19,8,38)),'1'],
        [tuple_text((8,18,18,8,40)),'18'],[tuple_text((8,19,19,8,39)),'4'],
        [tuple_text((8,19,19,8,40)),'8']],[width-60,60])
    p('The Y and E entries follow from Section 35, because '
      'a good facet has b₅₅=0. The next three rows have '
      'at most seven polar vertices, so the Gale catalogue '
      'of Section 7 computes their whole face lattice. '
      'For each original face mask M, its polar mask '
      'has one bit for every facet mask containing M; '
      'its dimension is 3−dim M. Count the four-bit '
      'two-face masks and those with two five-bit '
      'three-face supersets. Direct substitution into '
      'q₄−3b₅₅+2η gives the bounds 15,10,9 for every '
      'admissible code with the stated row. This is '
      'the same exhaustive sign-code proof, now on '
      'the polar; no eight-point classification is used.')
    p('For the last four rows use the twelve count equations '
      'and (36.3), together with (36.2), 0≤b₅₅≤q₄≤η. '
      'At fixed c the least possible weight is the '
      'minimum of q−3b+2η over integers 0≤q≤η, '
      '0≤b≤min(q,⌊c₂/2⌋), 2q≥c₂+3c₄. '
      'For (8,18,18,8;40) the only count vector is '
      '(4,0,0,4,0,0,0,0,0,0,0,0), giving q≥6, '
      'b=0,η=6 and weight at least 18. For the other '
      'three rows the same finite minimum is 2,4,8 '
      'respectively, after excluding the two-tetrahedron '
      'profile by the parity argument. The weaker '
      'bound 1 for the first is sufficient here. The '
      'finite recurrence just described supplies all '
      'count vectors and all q,b values, so these '
      'minima do not presume realizability of any '
      'unclassified row.')
    p('Consequently, with W=Σ<sub>H</sub>λ(row H), '
      '(36.1) implies 0≤W≤4A+2(f₀₂₄−3y). '
      'We also use J≥4r in every local row, since each '
      'three-face has at least four vertices. These '
      'inequalities and the six exclusions are now '
      'proved mathematical inputs to the remaining '
      'sixteen-vertex cost calculation.')
