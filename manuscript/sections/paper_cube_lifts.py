"""Mathematical coverage and soundness of the cube-lift calculations."""
import gzip,json
from verification.paths import ROOT

def add_cube_lifts(p,eq,section,table,width):
    reports=json.loads((ROOT/'evidence/cube-lift-checks.json').read_text())
    section(30,'Four full normals: reduction covering every real lift')
    p('A full facet contains exactly one vertex from each antipodal pair. '
      'Its normalized normal u satisfies u(x)=±1 at every vertex. '
      'Choose four linearly independent full normals as the first four '
      'coordinates, and complete them to linear coordinates in dimension five. '
      'For m=7 or 8 antipodal pairs, write the vertices as')
    eq('±y<sub>i</sub>=(±q<sub>i</sub>,±h<sub>i</sub>), '
       'q<sub>i</sub>∈{−1,1}<super>4</super>, 0≤i&lt;m.', '30.1')
    p('Change a representative to its negative when necessary, so its first '
      'base coordinate is one. There are eight base classes '
      '(1,(−1)<super>b₀</super>,(−1)<super>b₁</super>,(−1)<super>b₂</super>), '
      'indexed by b₀+2b₁+4b₂. A class cannot occur three times: among three '
      'points on its vertical line, one lies between the other two and cannot '
      'be a vertex. Sorting the m class indices therefore gives exactly the '
      'nondecreasing sequences with no entry equal to the entry two places '
      'later. Direct enumeration gives 1,016 sequences for m=7 and 1,107 '
      'for m=8. This argument includes repeated bases and all coincidences '
      'among the remaining real heights.')
    p('For each sequence c the reduction uses one of two integer identities. '
      'Either a nonzero vector n satisfies n·q<sub>i</sub>=0 for every i, '
      'which contradicts full dimension, or an invertible rational map '
      'sends its signed, permuted base list onto a listed family. The latter '
      'identity has the form')
    eq('BA=eI₄, de≠0; &nbsp; '
       'A(ε<sub>i</sub>q<sub>τ(i)</sub>)=dQ<sub>i</sub>, '
       'ε<sub>i</sub>∈{−1,1}, τ a permutation.', '30.2')
    p('Equation (30.2) is an invertible linear change on the base coordinates. '
      'Next choose four independent base points Q<sub>b</sub>. The inverse '
      'of their matrix allows a shear h↦h−l(q) making their heights zero. '
      'The remaining m−4 heights are arbitrary real parameters a. Thus '
      'every realization becomes a listed family')
    eq('y<sub>i</sub>(a)=(Q<sub>i</sub>,ζ<sub>i</sub>·a), '
       'a∈ℝ<super>m−4</super>.', '30.3')
    p('The basis inverse is checked as an integer matrix identity MN=DI₄, '
      'D≠0. The four basis height forms are zero and the free height forms '
      'are the coordinate unit vectors. The zero parameter is excluded '
      'because all vertices would then lie in a four-dimensional subspace. '
      'Neither generic positions nor rational coordinates are assumed.')
    for m in (7,8):
        data=json.loads(gzip.decompress((ROOT/'certificates'/f'cube-{2*m}-certificates.json.gz').read_bytes()))
        report=reports[f'{2*m}_vertices'];uses=report['reduction']['uses']
        rows=[['<b>ID</b>','<b>Base class list</b>','<b>Sequences reduced</b>','<b>Forms / records</b>']]
        for k,(X,R) in enumerate(zip(data['families'],report['families'])):
            codes=[]
            for q in X['F']['qs']:
                s=q[0];codes.append(sum(1<<(j-1) for j in range(1,4) if q[j]!=s))
            rows.append([f'{2*m}.{k+1}',','.join(map(str,codes)),str(uses.get(str(k),0)),f"{R['planes']} / {R['records']}"])
        table(rows,[45,185,85,width-315])
        p(f'The {len(data["families"])} families cover '
          f'{report["reduction"]["sequences"]-report["reduction"]["nonspanning"]} '
          f'spanning sequences; {report["reduction"]["nonspanning"]} sequences '
          'are excluded by a displayed nonzero annihilator in the integer reduction data. '
          'The ordering of the bases in this table is retained when attaching free heights; '
          'equal class multisets alone are not used to identify families.')

    section(31,'Why the finite sign certificates prove a continuous statement')
    p('Here are the complete mathematical rules of the calculation. '
      'A plane form is l<sub>p</sub>(a)=L<sub>p</sub>·a with integer '
      'coefficients. Every branch separates l<sub>p</sub>&lt;0, '
      'l<sub>p</sub>=0 and l<sub>p</sub>&gt;0. All three children '
      'are checked. This is a partition of all real parameter space, '
      'including every wall and lower-dimensional intersection.')
    p('A supporting-function record is an affine function')
    eq('φ<sub>a</sub>(q,h)=∑<sub>j=1</sub><super>4</super>'
       '(C<sub>j</sub>·a)q<sub>j</sub>+c₄h+C₅·a.', '31.1')
    p('All its values φ<sub>a</sub>(y<sub>w</sub>) are first verified '
      'as exact integer vector identities: each is zero or a recorded '
      'integer multiple of one plane form. Thus the signs along a branch '
      'determine whether φ has the same weak sign at every vertex. '
      'If it does, its zero set is an exposed face and its zero vertices '
      'give its vertex mask. In the fourteen-vertex calculation this '
      'alone suffices; the supporting faces need not be facets.')
    p('In the sixteen-vertex calculation an upper facet is certified by '
      'five zero vertices T. Four of their base vectors are independent; '
      'an integer dependency ∑λ<sub>i</sub>Q<sub>Tᵢ</sub>=0, '
      'λ<sub>k</sub>≠0, has nonzero height '
      '∑λ<sub>i</sub>ζ<sub>Tᵢ</sub>·a on the branch. Hence the five '
      'vectors y<sub>Tᵢ</sub> span dimension five. Since they lie in '
      'a supporting hyperplane with nonzero constant, their affine '
      'span has dimension four. The sign of C₅·a orients (31.1); '
      'requiring the resulting last normal coordinate positive makes '
      'this an upper facet. Its antipode is a distinct lower facet.')
    p('Vertical facets use an integer inequality n·Q≤d, d&gt;0. '
      'The tight base mask is checked by direct dot products. If it is '
      'full, it contains one of each vertex pair and spans the facet '
      'hyperplane: their linear span is that of all the vertices. '
      'Otherwise the data identify two distinct tight points with '
      'equal base, and four independent tight base vectors. The '
      'height difference is nonzero because the vertices are distinct; '
      'together these again span dimension five, hence a facet.')
    p('For face-count terminals, let g₁,…,g<sub>s</sub> be certified '
      'supporting masks. For each proposed nonzero mask M, check')
    eq('M=⋂{g<sub>i</sub>: M⊆g<sub>i</sub>}.', '31.2')
    p('The intersection of nonempty exposed faces is exposed: normalize '
      'their support inequalities and add them; equality in the sum '
      'holds exactly when equality holds in each summand. Its vertices '
      'are exactly the intersection of the vertex masks. Distinct '
      'masks therefore give distinct faces. For fourteen vertices '
      'the list contains at least 243 masks, with the whole-polytope '
      'mask permitted. For sixteen vertices at least 242 distinct '
      'proper nonempty masks are supplied; adding the polytope gives 243.')
    p('There are four other terminal rules. A nonnegative linear '
      'combination of oriented strict inequalities, with at least '
      'one positive coefficient, cannot be the zero form. Such a '
      'record excludes its branch. A nonzero determinant of vanishing '
      'plane forms forces a=0 and excludes full dimension. If two '
      'equal bases have a height difference equal to a combination '
      'of vanishing forms, their vertices coincide and the branch '
      'is invalid. Finally, a full upper facet yields a fifth '
      'independent full normal, since its last coordinate is positive; '
      'the five-normal calculation below applies.')
    eq('∑ c<sub>i</sub>σ<sub>i</sub>L<sub>pᵢ</sub>=0, '
       'c<sub>i</sub>≥0 for σ<sub>i</sub>≠0, '
       'some c<sub>i</sub>&gt;0 with σ<sub>i</sub>≠0.', '31.3')
    p('For vanishing facts take σ=1 and allow signed coefficients. '
      'An implied sign uses the same combination equal to '
      'DσL<sub>p</sub>, D&gt;0, rather than zero. An implied '
      'equality uses only vanishing facts and D≠0. Shared subtrees '
      'must have exactly the same hypotheses and cannot refer back '
      'to themselves. These rules justify induction from every '
      'terminal to the root of every family.')
    p('Facet-count terminals at sixteen vertices certify V vertical '
      'facets and N distinct upper facets, with V+2N≥21. Their '
      'antipodes are lower facets, and neither is vertical. This '
      'contradicts h≤20. Thus every admissible real lift either has '
      'at least 21 facets, has at least 243 nonempty faces, or has '
      'a fifth independent full normal. At fourteen vertices every '
      'admissible real lift directly has at least 243 nonempty faces.')
    rows=[['<b>m</b>','<b>Three-way branches</b>','<b>Face/facet terminals</b>','<b>Other terminals</b>']]
    for m in (7,8):
        fams=reports[f'{2*m}_vertices']['families']
        s={k:sum(f['nodes'].get(k,0) for f in fams) for k in ('branch','leaf','count','rank5','invalid','zero','zeroRank3','refuted')}
        rows.append([str(m),str(s['branch']),f"{s['leaf']} / {s['count']}",
                     f"full: {s['rank5']}; coincident: {s['invalid']}; zero: {s['zero']+s['zeroRank3']}; refuted: {s['refuted']}"])
    table(rows,[40,80,105,width-225])
    p('These are counts of checks, not sampled real polytopes. The '
      'supplement contains only integer vectors, rational-map identities '
      'and finite sign trees. The independent Python calculation checks '
      'every identity above using ordinary rational arithmetic. '
      'The proof of continuous coverage is the normalization and '
      'three-way induction just given, rather than the output of an '
      'optimizer or checks of generic sample coordinates.')

    section(32,'Five full normals: a finite sign-vector calculation')
    p('With five independent full normals the vertices become cube '
      'sign vectors in {−1,1}<super>5</super>. For sixteen vertices '
      'there are eight distinct antipodal classes, chosen from the '
      'sixteen classes having first coordinate one. Thus there are '
      'C(16,8)=12,870 subsets. Coordinate permutations and coordinate '
      'sign changes act invertibly, preserving all faces. They '
      'reduce the list to the following 25 representatives.')
    data=json.loads(gzip.decompress((ROOT/'certificates'/'cube-5-sign-certificates.json.gz').read_bytes()))
    counts=reports['five_full_normals']['certified_face_counts']
    rows=[['<b>Representative</b>','<b>Eight classes</b>','<b>Certified nonempty faces</b>']]
    for k,(r,c) in enumerate(zip(data['reps'],counts)):
        rows.append([str(k+1),','.join(map(str,r)),'not spanning' if c==0 else str(c)])
    table(rows,[65,200,width-265])
    p('Coverage is checked on every eight-bit subset mask. Its listed '
      'signed permutation carries its classes onto its representative. '
      'The first representative has a nonzero annihilator and is '
      'excluded by full dimension. For each other representative, '
      'the integer witnesses (d,z,M) satisfy d&gt;0 and')
    eq('|z·q<sub>i</sub>|≤d; &nbsp; '
       'M={i:z·q<sub>i</sub>=d}∪{i+8:z·q<sub>i</sub>=−d}.', '32.1')
    p('Each nonzero M is the vertex set of the face exposed by z/d. '
      'The masks are strictly increasing and there are at least 242; '
      'none contains both members of a vertex pair, so all are proper. '
      'Adding the polytope proves s≥243. All inequalities are integer '
      'dot products. This supplies the last terminal rule in Section 31.')

    section(33,'Sixteen vertices and full-normal rank three')
    p('When there are at least four full pairs, their normal span has '
      'dimension at least three by q≤2<super>d</super> in Section 28. '
      'If its dimension is at least four, Sections 30–32 apply. '
      'For rank exactly three the same argument as Section 28 gives '
      'three base classes, transformed to ±e₁,±e₂,±e₃. The vertices '
      'have the form ±(e<sub>i</sub>,k), k∈K<sub>i</sub>⊂ℝ². '
      'Each K<sub>i</sub> is the vertex set of a convex polygon, '
      'segment or point. Their sizes sum to eight.')
    p('If one class is a point, shear it to zero and split off its '
      'segment as in Section 28. The remaining centrally symmetric '
      'four-polytope has at least 81 faces by Section 27; the free '
      'sum has at least 3·81=243. Otherwise the sizes, up to order, '
      'are (4,2,2) or (3,3,2). We prove both without a lifting enumeration.')
    p('Label each class O,+,− or B, according as neither sign, only '
      'the positive sign, only the negative sign, or both signs '
      'occur in an exposed proper face. Different labels give '
      'different vertex sets. For a nonempty label containing no B, '
      'put M equal to the Minkowski sum of the signed active K’s. '
      'Every face of M, including M, gives an exposed face of the '
      'large polytope: choose the base coefficient for each active '
      'class so its selected support equals a common large H, '
      'and the opposite and inactive supports are strictly smaller. '
      'The vertex pattern determines the individual summand faces, '
      'and hence their Minkowski face, so this construction is '
      'injective. A polygon with m edge normals contributes 2m+1 '
      'patterns; a segment contributes three.')
    p('Edge normal sets add by union under Minkowski addition. A '
      'triangle has three normals and contains no antipodal normal '
      'pair. A quadrilateral has four; a segment has its two '
      'opposite perpendicular normals. Write w<sub>i</sub>(b) '
      'for half the width of K<sub>i</sub> in direction b.')
    p('<b>Equatorial counting rule.</b> Suppose a segment K<sub>j</sub> '
      'has zero width at α and another class i is strictly widest '
      'there. For each choice of O,+,− on the remaining class, '
      'the label with B at i and a fixed sign at j has at least '
      'six patterns. Indeed take b=α and b=−α, tie the two signs '
      'of i by choosing its base coefficient to be minus the '
      'midpoint of its two support values, and use H=w<sub>i</sub>(b). '
      'The strict width gaps allow the other labels to be selected '
      'freely. At j its entire segment is exposed. Perturb b '
      'slightly on either side to expose each endpoint separately. '
      'The two choices of ±α remain distinct on class i because '
      'its width is positive. Thus there are 2·3 patterns. If '
      'both other classes are unused, the two directions still '
      'give two distinct B patterns. This proves the rule, '
      'including all width degeneracies not ruled out by a strict gap.')
    p('A further full normal exists whenever, in a nonzero direction '
      'b, every class is either zero-width or has one common positive '
      'width W and all its vertices lie on the two extreme support '
      'levels. Center each nonzero-width class by its base coefficient '
      'and scale by 1/W; at a zero-width class choose the base '
      'coefficient to give value one. The result is ±1 at every '
      'vertex and has a nonzero fibre component. This contradicts '
      'full-normal rank three. We will use precisely this explicit '
      'criterion to rule out two equality cases.')
    p('<b>Case (4,2,2).</b> Let Q be the quadrilateral and let '
      '±α,±γ be the two segment normal pairs. If the segments '
      'are parallel, Q cannot have both normals ±α; otherwise '
      'the preceding criterion supplies a fourth full normal. '
      'Every signed sum involving Q and a segment has at least '
      'five normals. The octahedral labels give at least '
      '8·11+4·11+4·11+2·9+6·3+2·3=218 faces. Q is strictly '
      'widest at α; the equatorial rule supplies 6·6+2·6+2=50 '
      'more, hence at least 269 including the polytope.')
    p('If the segments are nonparallel and Q contains neither '
      'complete normal pair, sums with one segment have at '
      'least five normals and those with both at least six. '
      'There are at least 8·13+4·11+4·11+2·9+4·9+4·3=258 '
      'octahedral faces, hence 259 including P. If Q contains '
      '±α, compare its width there with that of the other '
      'segment. They are unequal: equality gives a fourth '
      'full normal, since Q has two opposite extreme edges '
      'containing all its vertices and the other segment '
      'has only two vertices. The wider class is strictly '
      'widest, while the first segment has zero width. '
      'The crude octahedral count is 210, and the six labels '
      'with the widest class B and the first segment signed '
      'give 36 equatorial faces. Thus s≥247. The case '
      'where Q contains ±γ is identical with the segment '
      'indices interchanged.')
    p('<b>Case (3,3,2).</b> Let N₁,N₂ be the triangle normal '
      'sets and ±α the segment normal pair. Put '
      'x=|N₁∪N₂| and y=|N₁∪(−N₂)|. The intersections '
      'N₁∩N₂ and N₁∩(−N₂) are disjoint, so x+y≥9. '
      'Two signed triangles contribute 4(x+y)+4 patterns, '
      'and the same labels with the segment signed contribute '
      '8(x+y)+8. Triangle-segment labels contribute 8·9=72, '
      'single triangles 4·7=28, and a single segment 2·3=6. '
      'Including P gives the initial bound')
    eq('s≥12(x+y)+119≥227.', '33.1')
    p('If the triangle widths at α differ, the wider triangle '
      'is strictly widest, giving six equatorial labels with '
      'six patterns each. Therefore s≥263. If they are equal, '
      'at least one triangle contains neither α nor −α as an '
      'edge normal. Otherwise each triangle lies on its two '
      'extreme levels in that direction, giving a fourth full '
      'normal. A triangle has no antipodal normal pair, so '
      'each of the four signed triangle-normal unions lacks '
      'at least one of α,−α. Adding the segment gives one '
      'extra normal, hence two extra patterns at each of '
      'the eight three-signed labels. The gain of 16 in '
      '(33.1) proves s≥243. These alternatives exhaust the '
      'rank-three case.')
