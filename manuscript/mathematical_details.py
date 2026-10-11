"""Expanded mathematical arguments for the manuscript, without proof-system code."""


def add_details(p, eq, section, table, width):
    section(10, 'The rigidity input and its dimensional extension')
    p('For a finite set of points <i>X</i> in a Euclidean space and a set of bars '
      '<i>B</i>, an infinitesimal motion assigns a velocity <i>u</i><sub>x</sub> '
      'to each point and satisfies')
    eq('⟨<i>u</i><sub>x</sub> − <i>u</i><sub>y</sub>, <i>x</i> − <i>y</i>⟩ = 0 '
       '&nbsp; for every bar {<i>x</i>,<i>y</i>}.', '10.1')
    p('In the affine span of a full-dimensional framework, trivial motions have '
      'the form <i>u</i><sub>x</sub> = <i>Ax</i> + <i>b</i>, with '
      '<i>A</i> skew-symmetric. Infinitesimal rigidity means that all motions '
      'are trivial. Equivalently, the bars force (10.1) for every pair of vertices.')
    p('<b>Classical three-dimensional input.</b> A convex three-dimensional '
      'polytope becomes infinitesimally rigid when its polygonal faces are '
      'triangulated without new vertices. This is the convex three-dimensional '
      'rigidity theorem. Its proof is not reproduced here. The extension '
      'to dimensions four and five used below follows from the following '
      'slice and gluing argument.')
    p('First, the vertices of the 2-faces containing an edge span the affine '
      'space of the polytope. Indeed, modulo the edge direction, their '
      'directions contain the extreme rays of the tangent cone along the '
      'edge; those rays span the quotient. This also explains why a joint '
      'inserted on an edge can be braced by joining it to those vertices. '
      'After subtracting a trivial motion of the existing framework, the '
      'new velocity is orthogonal to spanning bar directions, and so is zero '
      'in the affine span. Adding finitely many such joints preserves bracing.')
    section(10, 'The slice and gluing extension, continued')
    p('Next, let <i>a</i> be a vertex of a convex polytope of dimension '
      '<i>k</i>+1. A sufficiently small hyperplane cuts its incident edges '
      'to give a <i>k</i>-dimensional vertex figure. Project every other '
      'vertex radially from <i>a</i> to this hyperplane:')
    eq('<i>z</i><sub>x</sub> = <i>a</i> + τ<sub>x</sub>(<i>x</i> − <i>a</i>), '
       '&nbsp; τ<sub>x</sub> &gt; 0;<br/>'
       '<i>w</i><sub>x</sub> = <i>u</i><sub>a</sub> + '
       'τ<sub>x</sub>(<i>u</i><sub>x</sub> − <i>u</i><sub>a</sub>).', '10.2')
    p('Vertices on a common 2-face through <i>a</i> project to joints on an '
      'edge of the vertex figure. Each 2-face of the vertex figure comes from '
      'a 3-face through <i>a</i>. The three-dimensional input braces that '
      '3-face, and the projected velocities preserve its slice bar lengths.')
    eq('⟨<i>w</i><sub>x</sub> − <i>w</i><sub>y</sub>, '
       '<i>z</i><sub>x</sub> − <i>z</i><sub>y</sub>⟩<br/>'
       '= τ<sub>x</sub>τ<sub>y</sub>'
       '⟨<i>u</i><sub>x</sub> − <i>u</i><sub>y</sub>, '
       '<i>x</i> − <i>y</i>⟩.', '10.3')
    p('The identity follows by expanding the inner products and using '
      '(10.1) for the pairs (<i>a</i>,<i>x</i>) and (<i>a</i>,<i>y</i>). '
      'Rigidity in dimension <i>k</i>, including the edge joints just '
      'described, therefore braces the entire vertex figure. Since the '
      'factors τ are positive, (10.3) braces the vertices of all 2-faces '
      'through <i>a</i>, together with <i>a</i>. Call this set the star of '
      '<i>a</i>. It spans the original affine space.')
    p('Stars of adjacent vertices overlap on the vertices of every 2-face '
      'through their edge. That overlap spans the space by the first '
      'paragraph. Their trivial motions consequently agree: an affine '
      'motion zero on an affinely spanning set is zero everywhere. '
      'The edge graph is connected; for example a generic linear '
      'functional gives an increasing edge from every vertex except its '
      'maximum. Gluing stars along such edges braces all vertices. This '
      'proves the induction from dimension three to four, then to five.')
    p('A fan triangulation of a polygon braces all pairs of its vertices: '
      'its triangles glue along edges in its plane. Thus replacing each '
      'polygon by its fan bars provides the bracing assumed in the '
      'argument. This works at the actual convex vertex positions; '
      'no generic perturbation or simplicial hypothesis is used.')

    section(11, 'Symmetry and the exact stress dimension')
    p('Triangulate each polygonal 2-face by a fan, making the choices '
      'antipodally. Different polygons share only vertices or original '
      'edges, so their added diagonals are distinct. If <i>M</i> is the '
      'total number of bars, then')
    eq('<i>M</i> = <i>e</i> + ∑<sub>Q</sub>(<i>f</i><sub>0</sub>(<i>Q</i>) − 3) '
       '= <i>e</i> + <i>x</i> − 3<i>p</i>.', '11.1')
    p('Every bar lies in a proper face, so no bar joins antipodal vertices '
      'and no bar is fixed by the antipodal operation. Choose one '
      'representative of each vertex pair and each bar pair. Restrict '
      'the rigidity map to even velocity fields, meaning '
      '<i>u</i><sub>−x</sub> = <i>u</i><sub>x</sub>, and keep one '
      'equation per bar pair. Its domain and codomain have dimensions '
      '5<i>v</i>/2 and <i>M</i>/2.')
    p('A vector in its kernel extends to a motion of the full framework, '
      'since the antipodal bar equation is the negative of the chosen '
      'one. By Section 10 it is <i>Ax</i>+<i>b</i>. Evenness forces '
      '<i>Ax</i>=0 at every vertex. The vertices span the ambient space, '
      'so <i>A</i>=0. Conversely, every translation is an even motion. '
      'The kernel is therefore exactly five-dimensional.')
    eq('rank <i>R</i><sub>even</sub> = 5<i>v</i>/2 − 5.', '11.2')
    p('A stress assigns a real coefficient to every bar so that the '
      'sum of the resulting bar forces is zero at each vertex. It is '
      'a vector in the kernel of the transpose rigidity map. An '
      'antisymmetric stress has opposite coefficients on antipodal '
      'bars. It is determined by one coefficient per pair, and its '
      'equilibrium equations are precisely the left kernel of '
      '<i>R</i><sub>even</sub>. Rank–nullity gives')
    eq('dim <i>S</i><sub>anti</sub> = <i>M</i>/2 − 5<i>v</i>/2 + 5 '
       '= <i>G</i>/2.', '11.3')
    p('Thus <i>G</i> is an even nonnegative integer. The same argument '
      'on the polar gives the corresponding facts for <i>G</i><super>*</super>. '
      'This provides the exact numerical meaning of the slacks in '
      'Section 3, rather than merely asserting their positivity.')

    section(12, 'Facet stress localization')
    p('Let <i>F</i> be a facet with row (<i>n</i>,<i>e</i><sub>F</sub>, '
      '<i>p</i><sub>F</sub>,<i>r</i><sub>F</sub>;<i>J</i>). The '
      'chosen polygon triangulations restrict to its complete 2-skeleton. '
      'Its framework is rigid in its four-dimensional affine span by '
      'Section 10.')
    p('Summing Euler’s relation in its three-dimensional vertex figures '
      'gives <i>f</i><sub>02</sub>(<i>F</i>) = '
      '<i>J</i>+2<i>e</i><sub>F</sub>−2<i>n</i>. '
      'Euler’s relation for <i>F</i> gives '
      '<i>p</i><sub>F</sub>=<i>e</i><sub>F</sub>−<i>n</i>+<i>r</i><sub>F</sub>. '
      'Consequently its bar count is <i>J</i>+<i>n</i>−3<i>r</i><sub>F</sub>. '
      'The trivial motions in four dimensions have dimension 10, so')
    eq('dim <i>S</i>(<i>F</i>) = (<i>J</i>+<i>n</i>−3<i>r</i><sub>F</sub>) '
       '− (4<i>n</i>−10)<br/>'
       '= <i>J</i>−3<i>n</i>−3<i>r</i><sub>F</sub>+10 = <i>g</i>(<i>F</i>).', '12.1')
    p('Extend a facet stress ω by zero to the other bars. It remains a '
      'global stress: all facet differences lie in its direction space, '
      'so its equilibrium equations are unchanged in the ambient '
      'space. Let τ copy stress coefficients to antipodal bars. Then')
    eq('ω ↦ ω − τω', '12.2')
    p('is an antisymmetric global stress. A proper face cannot contain '
      'antipodal vertices, so <i>F</i> and −<i>F</i> have disjoint '
      'vertex sets. Restricting (12.2) back to the bars of <i>F</i> '
      'recovers ω. The map is injective. Comparing (12.1) with '
      '(11.3) proves')
    eq('0 ≤ 2<i>g</i>(<i>F</i>) ≤ <i>G</i>.', '12.3')
    p('If <i>G</i>=0, every facet has <i>g</i>=0. Summing the '
      'definition of <i>g</i>, using (6.1) and the flag identities, gives')
    eq('∑<sub>F</sub><i>g</i>(<i>F</i>) = '
       '2<i>G</i> + 4<i>v</i> + 4<i>h</i> − <i>I</i> − 8.', '12.4')
    p('In particular <i>G</i>=0 forces '
      '<i>I</i>=4(<i>v</i>+<i>h</i>)−8. This is the exact '
      'incidence equation used at (14,20) and (16,22). '
      'The injection concerns a single facet. It does not justify '
      'adding stress lower bounds from arbitrary overlapping facets.')

    section(13, 'Polygon localization and the zero-slack case')
    p('Let <i>Q</i> be a polygonal 2-face with vertices '
      '<i>p</i><sub>1</sub>, …, <i>p</i><sub>k</sub>, contained in '
      'ℓ three-dimensional faces <i>T</i><sub>j</sub>. The '
      'two-dimensional face figure is a polygon, so it has ℓ '
      'vertices and ℓ edges; equivalently ℓ is also the number '
      'of facets containing <i>Q</i>. We prove')
    eq('<i>G</i> ≥ 2(<i>k</i>−3)(ℓ−3).', '13.1')
    p('Choose <i>p</i><sub>0</sub> in the affine span of '
      '<i>Q</i>, and let <i>U</i> be its two-dimensional direction '
      'space. The affine dependence space of the polygon vertices is')
    eq('<i>W</i> = {α : ∑<sub>i</sub>α<sub>i</sub>=0, '
       '∑<sub>i</sub>α<sub>i</sub><i>p</i><sub>i</sub>=0}, '
       '&nbsp; dim <i>W</i> = <i>k</i>−3.', '13.2')
    p('For each <i>T</i><sub>j</sub>, choose a vertex '
      '<i>q</i><sub>j</sub> outside <i>Q</i>. Its direction '
      '<i>b</i><sub>j</sub>=(<i>q</i><sub>j</sub>−<i>p</i><sub>0</sub>) '
      'modulo <i>U</i> is nonzero. These directions follow the extreme '
      'rays of the full-dimensional tangent cone along <i>Q</i>, '
      'and span the three-dimensional quotient. The matrix <i>B</i> '
      'with these columns has rank three, and its kernel has dimension '
      'ℓ−3.')
    p('Consider matrices <i>C</i> with each column in <i>W</i> and '
      'each row in ker <i>B</i>. Their vector space has dimension '
      '(<i>k</i>−3)(ℓ−3). For the <i>j</i>-th column form the '
      'virtual bar-row combination')
    eq('<i>s</i><sub>j</sub> = ∑<sub>i</sub>'
       '<i>C</i><sub>ij</sub> row(<i>p</i><sub>i</sub>, '
       '<i>q</i><sub>j</sub>).', '13.3')
    p('The force at <i>q</i><sub>j</sub> vanishes by the two '
      'affine dependence equations. At <i>p</i><sub>i</sub> it is '
      '<i>C</i><sub>ij</sub>(<i>p</i><sub>i</sub>−<i>q</i><sub>j</sub>). '
      'All the virtual bars lie in <i>T</i><sub>j</sub>. Its '
      'triangulated framework is rigid in its affine span, so the '
      'row space equals the row space of the complete graph on its '
      'vertices. This remains true in the ambient space, since bar '
      'rows have no normal components. Thus <i>s</i><sub>j</sub> '
      'has a representation <i>a</i><sub>j</sub> using actual bars '
      'of <i>T</i><sub>j</sub>. Choose the representations linearly.')
    p('Summing (13.3), the row-kernel equations make every remaining '
      'force lie in <i>U</i>, supported on the polygon vertices. '
      'It has zero total force and torque, since it is a sum of bar '
      'rows. The polygon fan is rigid in its plane, and its row space '
      'is exactly the planar loads orthogonal to translations and '
      'rotation. Hence the sum has a representation <i>a</i><sub>Q</sub> '
      'using polygon bars. The coefficients')
    eq('ω(<i>C</i>) = ∑<sub>j</sub><i>a</i><sub>j</sub> − '
       '<i>a</i><sub>Q</sub>', '13.4')
    p('form an actual stress supported in the union of the '
      '<i>T</i><sub>j</sub> frameworks. Distinct three-faces '
      'containing <i>Q</i> meet exactly in <i>Q</i>. A bar from '
      '<i>p</i><sub>i</sub> to a vertex of '
      '<i>T</i><sub>j</sub> outside <i>Q</i> therefore belongs '
      'to no other <i>T</i><sub>j′</sub>. If ω(<i>C</i>) '
      'vanishes on every bar incident to <i>Q</i>, the normal '
      'component of the force of <i>a</i><sub>j</sub> at '
      '<i>p</i><sub>i</sub> must vanish. That component is '
      '−<i>C</i><sub>ij</sub><i>b</i><sub>j</sub>, and '
      '<i>b</i><sub>j</sub> is nonzero. Thus <i>C</i>=0.')
    p('No three-face containing <i>Q</i> contains an antipode of '
      'a polygon vertex. Consequently τω(<i>C</i>) vanishes '
      'on bars incident to <i>Q</i>. The map '
      '<i>C</i> ↦ ω(<i>C</i>)−τω(<i>C</i>) is injective '
      'into the global antisymmetric stress space. Its dimension '
      'is <i>G</i>/2, which proves (13.1).')
    p('The excess <i>A</i> is the sum over polygons of '
      '(<i>k</i>−3)(ℓ−3). If <i>G</i>=0, (13.1) '
      'makes each summand zero, and hence <i>A</i>=0. '
      'For positive <i>G</i>, this argument bounds each polygon '
      'separately; it does not give an additive bound on <i>A</i>.')

    section(14, 'Constructing the small-facet catalogue')
    p('Let <i>a</i><sub>1</sub>, …, <i>a</i><sub>n</sub> '
      'be the vertices of a four-dimensional polytope with '
      '5 ≤ <i>n</i> ≤ 7. Form the augmented matrix with columns '
      '(<i>a</i><sub>i</sub>,1). Its rank is five. A basis of '
      'its kernel gives Gale vectors <i>g</i><sub>i</sub> of '
      'rank <i>n</i>−5, embedded in a plane if necessary.')
    p('For a vertex subset <i>F</i>, put <i>S</i> equal to its '
      'complement. The face criterion is that the vectors '
      '<i>g</i><sub>i</sub>, <i>i</i> in <i>S</i>, admit '
      'a dependence with every coefficient strictly positive. '
      'To see this, an exposing affine functional has zero slack '
      'on <i>F</i> and positive slack on <i>S</i>. Its slack '
      'vector lies in the row space of the augmented matrix, '
      'which is the orthogonal complement of the Gale matrix '
      'columns. This is exactly the displayed dependence condition. '
      'The empty complement corresponds to the whole polytope.')
    eq('dim <i>F</i> = 4 − |<i>S</i>| + '
       'rank{<i>g</i><sub>i</sub> : <i>i</i> in <i>S</i>}.', '14.1')
    p('Indeed the affine dependencies supported on <i>F</i> '
      'have dimension (<i>n</i>−5) minus the rank on '
      '<i>S</i>. Subtract this from |<i>F</i>|−1 '
      'to obtain (14.1).')
    p('Choose a coordinate direction avoiding the finitely many '
      'nonzero Gale lines. Rescale each nonzero vector by a '
      'positive factor to the form ±(1,<i>t</i>), and order '
      'the distinct slopes. Code the zero vector by 0, and '
      'the positive and negative vectors on line <i>j</i> '
      'by 2<i>j</i>+1 and 2<i>j</i>+2. Sorting all '
      'codes only relabels the vertices. Occupied lines '
      'are numbered consecutively, so a recursive enumeration '
      'may use an existing line or introduce the next line.')
    p('The minimal nonnegative dependencies are precisely: '
      'a zero singleton; opposite vectors on the same line; '
      'or three distinct ordered lines with equal signs on '
      'the outside lines and the opposite sign on the '
      'middle line. This follows by solving the two equations '
      'for (1,<i>t</i>): the middle slope is a strict convex '
      'combination of the outside slopes. Rank at most two '
      'ensures that no larger minimal support is needed.')
    p('A subset admits a dependence positive on every member '
      'exactly when it is a union of such minimal supports '
      'contained in it. One direction follows by summing '
      'their positive dependences. For the other, decompose '
      'a nonnegative dependence into minimal ones by '
      'subtracting a scaled minimal dependence until a '
      'coefficient vanishes, and iterate.')
    p('As an independent consistency check, functional sign '
      'partitions are enumerated both on an occupied line '
      'and between adjacent lines. A subset without a '
      'positive dependence must have a functional nonnegative '
      'on all its vectors and positive on at least one. '
      'Every subset is checked to satisfy exactly one of '
      'these alternatives. Every singleton vertex must '
      'also pass the face criterion; codes that fail are discarded.')
    p('The accompanying standard-library Python program '
      '<font name="MathUpright">verify_mathematics.py</font> '
      'implements these steps with integer masks. It checks '
      '6,364 sorted codes, of which 4,608 have the required '
      'rank. Exactly 832 pass all singleton tests. Counting '
      'their faces by (14.1) gives exactly the 24 rows '
      'in Section 15. These are counts of codes, not '
      'counts of distinct combinatorial types.')
    section(14, 'Catalogue profiles and recognition, continued')
    p('For the row (7,15,14,6;29), the same face enumeration '
      'gives exactly one six-vertex 3-face. For the row '
      '(7,18,19,8;35), it gives exactly two vertices '
      'lying in six facets. By polarity, the row '
      '(8,19,18,7;35) therefore has exactly two '
      'six-vertex 3-faces. These profile facts are checked '
      'for every valid code producing the indicated row.')
    p('The prism row can also be recognized without an affine '
      'product assumption. Its dual is (6,14,16,8;32), '
      'with a rank-one Gale diagram. Let the numbers of '
      'positive, negative and zero Gale vectors be '
      '<i>a</i>, <i>b</i>, <i>z</i>. The singleton face '
      'tests require <i>a</i>,<i>b</i>≥2. A facet '
      'complement is either one zero vector or one '
      'positive and one negative vector, so the '
      'facet count is <i>z</i>+<i>ab</i>. Together '
      'with <i>a</i>+<i>b</i>+<i>z</i>=6 and '
      '<i>z</i>+<i>ab</i>=8, this forces '
      '<i>z</i>=0 and {<i>a</i>,<i>b</i>}={2,4}. '
      'The eight dual vertices are therefore '
      'labelled by a pair in a two-element set '
      'times a four-element set. Its six facets '
      'are the two tetrahedra and four sides '
      'omitting corresponding vertex pairs. '
      'The full face criterion gives exactly '
      'the tetrahedron-prism face lattice. '
      'The program checks these facet witnesses '
      'for every code of the dual row.')

    section(15, 'The twenty-four rows and local costs')
    p('The columns show (<i>n</i>,<i>e</i>,<i>p</i>,<i>r</i>;<i>J</i>) '
      'and the four weights of Section 6. The catalogue is generated '
      'by the procedure of Section 14, not obtained by assuming '
      'the desired five-dimensional inequality.')
    from verification.verify_mathematics import catalogue, weights
    rows, _ = catalogue()
    cells = [['<b>'+c+'</b>' for c in ('n','e','p','r','J','g','L₁','L₂','L₃')]]
    cells += [[str(c) for c in tuple(r) + (weights(r)[3],) + weights(r)[:3]] for r in rows]
    table(cells, [width/9]*9, compact=True)
    p('All weights are nonnegative. The adjusted cost '
      '<i>L</i><sub>2</sub>−5[<i>n</i>=7] is negative '
      'only on (7,15,14,6;29), where it is −4. '
      'The unadjusted cost <i>L</i><sub>1</sub> '
      'takes values 0 or 5 below 10. With <i>g</i>=0, '
      'its zero rows are precisely the simplex '
      '(5,10,10,5;20) and (7,15,14,6;29).')

    section(16, 'Segment fibres and the parallel full prism')
    p('<b>Lemma 16.1 (Three faces over every base face).</b> '
      '<i>Suppose a linear projection of a full-dimensional '
      'polytope onto a polytope Q has a one-dimensional '
      'kernel, and the fibre above every vertex of Q '
      'is a nondegenerate segment. Then s(P) ≥ 3s(Q).</i>')
    p('<i>Proof.</i> Fix a nonempty face <i>K</i> of '
      '<i>Q</i>. Its inverse-image face <i>P</i><sub>K</sub> '
      'is obtained by pulling back an exposing functional; '
      'for <i>K</i>=<i>Q</i> it is <i>P</i> itself. '
      'If dim <i>K</i>=<i>k</i>, this face has dimension '
      '<i>k</i>+1, since its vertex fibres are nondegenerate. '
      'In fact every fibre is nondegenerate: express a base '
      'point as a convex combination of base vertices '
      'and combine the two endpoints of their segments.')
    p('Over <i>K</i>, the upper endpoint of the fibres is '
      'a concave piecewise affine function; the lower '
      'endpoint is a convex piecewise affine function. '
      'Each has a cell of full dimension <i>k</i> '
      'whose relative interior meets that of <i>K</i>. '
      'Their graphs are upper and lower faces of '
      '<i>P</i><sub>K</sub>, hence faces of <i>P</i>. '
      'They have dimension <i>k</i>, so neither is '
      '<i>P</i><sub>K</sub>. They cannot be the same '
      'face, since fibres above the relative interior '
      'of <i>K</i> have positive length.')
    p('These three faces for different <i>K</i> are '
      'distinct. A chosen upper or lower face projects '
      'into <i>K</i> and has a full-dimensional cell '
      'there; the smallest face of <i>Q</i> containing '
      'its projection is therefore <i>K</i>. It is '
      'also never an inverse-image face, because the '
      'latter contains entire nondegenerate fibres. '
      'Choosing these three faces for every nonempty '
      '<i>K</i> proves the injection and the bound. □')
    p('Now let a full facet of a sixteen-vertex '
      'centrally symmetric five-polytope have the '
      'face lattice of a tetrahedron prism. Label its '
      'four corresponding edge pairs by <i>E</i><sub>i</sub>. '
      'Each pair of their affine lines is coplanar, '
      'because the edges are opposite sides of a '
      'quadrilateral 2-face. The four lines cannot '
      'all lie in one plane, since the facet has '
      'dimension four.')
    p('Distinct pairwise coplanar lines not contained '
      'in one plane are either all parallel or all '
      'concurrent. To prove this, take two intersecting '
      'lines through <i>p</i> in a plane <i>H</i>. '
      'A line coplanar with both that avoids <i>p</i> '
      'lies in <i>H</i>. Any further line outside '
      '<i>H</i> must pass through <i>p</i>, and '
      'cannot then be coplanar with that third line. '
      'Thus either all lines pass through <i>p</i>, '
      'or all would lie in <i>H</i>, a contradiction.')
    p('In the parallel case, project along their common '
      'direction. The four edge centres, modulo that '
      'direction, are linearly independent: otherwise '
      'the vertices of <i>P</i> would span at most '
      'four dimensions. The image is the '
      'four-dimensional crosspolytope, and each '
      'vertex fibre is exactly its corresponding '
      'edge or antipodal edge. A crosspolytope has '
      '81 nonempty faces by polarity with the '
      'four-cube. Lemma 16.1 gives 3·81=243. '
      'Equal edge lengths are not required.')

    section(17, 'Thirty-two polar vertices in the concurrent case')
    p('In the concurrent case let <i>p</i> be the common '
      'point of the four prism-edge lines. It lies '
      'outside every closed edge segment: in the '
      'convex quadrilateral made by any two opposite '
      'edges, the line of one edge leaves the entire '
      'other edge strictly on one side. Consequently '
      'write the endpoints as '
      '<i>p</i>+<i>s</i><sub>i</sub><i>u</i><sub>i</sub> '
      'and <i>p</i>+<i>t</i><sub>i</sub><i>u</i><sub>i</sub>, '
      'with 0&lt;<i>s</i><sub>i</sub>&lt;<i>t</i><sub>i</sub>.')
    p('The four directions are independent, since '
      'the facet spans four dimensions. Normalize '
      'its supporting form to equal 1. It takes '
      'value 1 at <i>p</i> and zero on the four '
      'directions, so <i>p</i> and those directions '
      'are a basis in dimension five. A linear '
      'change of coordinates gives')
    eq('<i>P</i> = conv{±(1,<i>s</i><sub>i</sub><i>e</i><sub>i</sub>), '
       '±(1,<i>t</i><sub>i</sub><i>e</i><sub>i</sub>) : 1≤<i>i</i>≤4}.', '17.1')
    p('Its polar is cut out by '
      '|<i>x</i><sub>0</sub>+<i>s</i><sub>i</sub><i>x</i><sub>i</sub>|≤1 '
      'and |<i>x</i><sub>0</sub>+<i>t</i><sub>i</sub><i>x</i><sub>i</sub>|≤1. '
      'For every nonempty subset <i>S</i> of {1,2,3,4}, take')
    eq('<i>x</i><sub>0</sub>=1; &nbsp; '
       '<i>x</i><sub>i</sub>=0 if <i>i</i> is in <i>S</i>, '
       'and −2/<i>t</i><sub>i</sub> otherwise.', '17.2')
    p('These points are feasible. Inside <i>S</i> '
      'both expressions are 1; outside it the '
      '<i>t</i> expression is −1 and the '
      '<i>s</i> expression is 1−2<i>s</i>/<i>t</i>, '
      'strictly between −1 and 1. Choose an index '
      'in <i>S</i>. Its two active equations determine '
      '<i>x</i><sub>0</sub> and its coordinate; '
      'one active equation for each remaining '
      'index determines all others. Their rank is '
      'five, so this is a vertex. The fifteen '
      'subsets and their negatives give thirty '
      'distinct vertices.')
    eq('<i>a</i>=min<sub>i</sub>'
       '(<i>t</i><sub>i</sub>+<i>s</i><sub>i</sub>)/'
       '(<i>t</i><sub>i</sub>−<i>s</i><sub>i</sub>) &gt; 1;<br/>'
       '<i>x</i><sub>0</sub>=<i>a</i>, &nbsp; '
       '<i>x</i><sub>i</sub>=−(1+<i>a</i>)/<i>t</i><sub>i</sub>.', '17.3')
    p('All four <i>t</i> expressions are −1. '
      'Each <i>s</i> expression is greater than '
      '−1 and at most 1; the latter inequality '
      'is equivalent to <i>a</i>≤(<i>t</i>+<i>s</i>)/'
      '(<i>t</i>−<i>s</i>). At a minimizing index '
      'the expression is 1. Its equation and '
      'the four <i>t</i> equations have rank '
      'five. Thus (17.3) and its negative are '
      'two further vertices, distinct from (17.2).')
    p('The polar therefore has at least 32 vertices. '
      'A five-dimensional polytope has minimum '
      'vertex degree five, so <i>e</i>≥5·16/2=40 '
      'and, by polarity, <i>r</i>≥5·32/2=80. '
      'Hence <i>t</i>≥120 and <i>s</i>(<i>P</i>)≥243. '
      'Together with Section 16, this proves the '
      'full tetrahedron-prism statement for every '
      'real realization of its face lattice.')

    section(18, 'A full pyramid and divisibility by four')
    p('Suppose a full facet is a pyramid with apex '
      '<i>a</i> and a three-dimensional base '
      '<i>K</i>. Normalize its supporting form '
      'to equal 1. The direction space of '
      '<i>K</i> has dimension three; its linear '
      'span has dimension four, since the '
      'supporting form is zero on directions '
      'but equals 1 on the base. The apex is '
      'outside that linear span: its intersection '
      'with the facet hyperplane is the affine '
      'span of the base, and an exposed base '
      'contains every point of the pyramid '
      'in that affine span.')
    p('Since the facet is full, all vertices of '
      '<i>P</i> are its vertices and their '
      'antipodes. Therefore')
    eq('<i>P</i> = conv({±<i>a</i>} ∪ <i>R</i>), '
       '&nbsp; <i>R</i> = conv(<i>K</i> ∪ −<i>K</i>).', '18.1')
    p('Here <i>R</i> is a centrally symmetric '
      'four-polytope in the complementary '
      'four-dimensional subspace. A linear '
      'change of coordinates turns (18.1) '
      'into a bipyramid over <i>R</i>. Its '
      'facets are the pyramids from either '
      'apex over a facet of <i>R</i>. Hence')
    eq('<i>f</i><sub>4</sub>(<i>P</i>) = '
       '2<i>f</i><sub>3</sub>(<i>R</i>) ≡ 0 (mod 4).', '18.2')
    p('The congruence follows because the facets '
      'of <i>R</i> occur in antipodal pairs. '
      'This alone excludes a full pyramid '
      'at (14,22); no five-dimensional '
      'face bound is assumed.')
    p('The exceptional seven-vertex row '
      '(7,15,14,6;29) is a pyramid over a '
      'triangular prism. Its recognition '
      'is a face-lattice statement, rather '
      'than an affine product assertion. '
      'It can be checked on each corresponding '
      'Gale code: the six-vertex base facet '
      'excludes one apex, and all other '
      'vertices lie in that base. A face '
      'is the convex hull of its vertices, '
      'so this proves the pyramid description.')

    section(19, 'The numerical closure at (16,22)')
    p('Assume <i>v</i>=16, <i>h</i>=22 and '
      '<i>t</i>≤118. Every facet has at most '
      'eight vertices. The tetrahedron-prism '
      'row <i>T</i>=(8,16,14,6;32) is excluded '
      'by Sections 16–17 after its face-lattice '
      'recognition. Put')
    eq('<i>L</i>(<i>F</i>) = <i>L</i><sub>1</sub>(<i>F</i>) '
       '+ 9[<i>n</i>=8].', '19.1')
    p('On nonfull facets the table gives '
      '<i>L</i>≥0, with the only values below '
      '10 being 0 and 5. For a full '
      'eight-vertex facet other than <i>T</i>, '
      '<i>L</i>≥13. If its <i>g</i> is zero, '
      '<i>L</i>≥14 and the only value below '
      '20 besides 14 is 18, attained uniquely '
      'by <i>Z</i>=(8,19,18,7;35).')
    p('Here is the coverage argument for these '
      'eight-vertex facts. If the facet has '
      'at most seven facets, its dual is '
      'in the table. The possibilities with '
      'eight vertices are <i>T</i>, '
      '(8,18,17,7;35), (8,18,17,7;36), '
      'and <i>Z</i>, whose costs are '
      '0,14,13,18. Otherwise let its facet '
      'count be <i>r</i>≥8. Euler and '
      '<i>J</i>+32≤4<i>e</i> give')
    eq('<i>L</i> = 4<i>e</i>+9<i>r</i>−86−<i>J</i> '
       '≥ 9<i>r</i>−54 ≥ 18.', '19.2')
    p('If <i>g</i>=0, then <i>J</i>=14+3<i>r</i> '
      'and 4<i>e</i>≥46+3<i>r</i>. '
      'For <i>r</i>=8, integer <i>e</i>≥18 '
      'gives <i>L</i>=4<i>e</i>−52≥20; '
      'for <i>r</i>≥9 the bound is still '
      'larger. This proves the stated gaps '
      'without a complete eight-vertex catalogue.')
    p('Let <i>m</i> count full antipodal facet '
      'pairs, and let <i>c</i> be the sum '
      'of <i>L</i> over one representative '
      'of every facet pair. Dividing (6.3) '
      'by two gives the exact identity')
    eq('6<i>t</i> = 699 − 9<i>m</i> + '
       '3<i>G</i> + 2<i>A</i> + <i>c</i>.', '19.3')
    p('Both <i>A</i> and <i>G</i> are even '
      'and nonnegative. The first fact for '
      '<i>A</i> follows either from its flag '
      'formula or by pairing antipodal polygons. '
      'Since <i>c</i>≥13<i>m</i> and '
      '6<i>t</i>≤708, (19.3) yields')
    eq('2<i>A</i> + 4<i>m</i> + 3<i>G</i> ≤ 9.', '19.4')
    section(19, 'The slack cases and ridge contradiction, continued')
    p('If <i>G</i>&gt;0, evenness forces '
      '<i>G</i>=2, <i>m</i>=0 and '
      '<i>A</i>=0. Equation (19.3) gives '
      '<i>c</i>≤3, so <i>c</i>=0 because '
      'a positive pair cost is at least five. '
      'It would then give 6<i>t</i>=705, '
      'impossible for integer <i>t</i>.')
    p('If <i>G</i>=0, Sections 12–13 give '
      '<i>g</i>(<i>F</i>)=0 for every facet '
      'and <i>A</i>=0. Thus '
      '<i>c</i>≥14<i>m</i> and '
      '<i>c</i>≤9+9<i>m</i>, so '
      '<i>m</i> is 0 or 1. At '
      '<i>m</i>=0, the only even '
      '<i>t</i>≤118 compatible with '
      '(19.3) is 118 and <i>c</i>=9. '
      'A sum of costs 0 or 5 cannot equal '
      '9. At <i>m</i>=1, the full '
      'pair cost is at least 14; the only '
      'possibility is <i>t</i>=118, '
      '<i>c</i>=18. A full cost of '
      '14 would leave four, impossible '
      'for the other nonnegative costs. '
      'The full pair must therefore be '
      '<i>Z</i>, and every other pair '
      'has cost zero.')
    p('The zero-cost, zero-<i>g</i> rows '
      'are the simplex <i>S</i> and '
      'the triangular-prism pyramid '
      '<i>Y</i>. Equation (12.4) gives '
      '<i>I</i>=144. The facet count '
      'and incidence count now imply')
    eq('<i>N</i><sub>S</sub>+<i>N</i><sub>Y</sub>+2=22,<br/>'
       '5<i>N</i><sub>S</sub>+7<i>N</i><sub>Y</sub>+16=144,<br/>'
       '<i>N</i><sub>S</sub>=6, &nbsp; <i>N</i><sub>Y</sub>=14, '
       '&nbsp; <i>N</i><sub>Z</sub>=2.', '19.5')
    p('A simplex has no six-vertex ridges, '
      '<i>Y</i> has one, and <i>Z</i> '
      'has two, by the profile counts '
      'of Section 14. Thus the number '
      'of incidences of six-vertex '
      'ridges with facets would be '
      '6·0+14·1+2·2=18. Every ridge '
      'belongs to exactly two facets; '
      'these ridges also occur in '
      'antipodal pairs. Their incidence '
      'count must therefore be divisible '
      'by four, contradicting 18. '
      'This closes the numerical argument '
      'at (16,22) from the stated '
      'geometric recognition and rigidity inputs.')

    from .sections.paper_endpoints import add_endpoints
    add_endpoints(p,eq,section,table,width)
    from .sections.paper_geometry import add_geometry
    add_geometry(p,eq,section,table,width)
    from .sections.paper_cube_lifts import add_cube_lifts
    add_cube_lifts(p,eq,section,table,width)
    from .sections.paper_extended_costs import add_extended_costs
    add_extended_costs(p,eq,section,table,width)
    from .sections.paper_quad_link import add_quad_link
    add_quad_link(p,eq,section,table,width)
    from .sections.paper_q55 import add_q55
    add_q55(p,eq,section,table,width)
    from .sections.paper_weighted20 import add_weighted20
    add_weighted20(p,eq,section,table,width)
    from .sections.paper_u import add_u
    add_u(p,eq,section,table,width)
    from .sections.paper_prism18 import add_prism18
    add_prism18(p,eq,section,table,width)
    from .sections.paper_endpoint_assembly import add_endpoint_assembly
    add_endpoint_assembly(p,eq,section,table,width)
    from .sections.paper_strong_weights import add_strong_weights
    add_strong_weights(p,eq,section,table,width)
    from .sections.paper_low18 import add_low18
    add_low18(p,eq,section,table,width)
    from .sections.paper_one_pair import add_one_pair
    add_one_pair(p,eq,section,table,width)
    from .sections.paper_two_pair_zero import add_two_pair_zero
    add_two_pair_zero(p,eq,section,table,width)
    from .sections.paper_positive_globals import add_positive_globals
    add_positive_globals(p,eq,section,table,width)
    from .sections.paper_positive_profiles import add_positive_profiles
    add_positive_profiles(p,eq,section,table,width)
    from .sections.paper_positive_closures import add_positive_closures
    add_positive_closures(p,eq,section,table,width)
    from .sections.paper_positive_geometry import add_positive_geometry
    add_positive_geometry(p,eq,section,table,width)
    from .sections.paper_signed_carriers import add_signed_carriers
    add_signed_carriers(p,eq,section,table,width)
    from .sections.paper_cube_three_singleton import add_cube_three_singleton
    add_cube_three_singleton(p,eq,section,table,width)

    from .sections.paper_balanced_sections import add_balanced_sections
    add_balanced_sections(p,eq,section,table,width)

    section(55, 'Completion of the endpoint ledger')
    p('Every possibility in the fifteen-pair reduction of Section 5 '
      'has now been excluded under t≤118. For clarity, the following '
      'ledger specifies where each complete exclusion is assembled. '
      'The references are to mathematical arguments and exact tables '
      'printed in this manuscript.')
    table([
      ['<b>(v,h)</b>', '<b>Complete exclusion</b>'],
      ['(14,16), (14,18), (14,20), (14,22), (14,24), (14,26)',
       '§40.1: incidence bounds and row sums after the all-real full-normal analysis of §§28–32'],
      ['(16,16)', '§34: full-normal geometry, no-full certificates and complete even-cell coverage'],
      ['(16,18)', 'No full pairs: §34; four or more: §§29–33; one: §43; two: §§44–49; three: §§50–54'],
      ['(16,20)', '§§35–37: quadrilateral localization, row weights, full-normal geometry and exact coverage'],
      ['(16,22)', '§19: forced ridge profile and antipodal incidence divisibility'],
      ['(16,24)', '§8: L₁ row sum, with the full prism excluded by §§16–17'],
      ['(18,18)', '§40.2: product and prism bounds of §§20,38–39, and the complete D certificates of §34'],
      ['(18,20)', '§40.3: product and prism alternatives, extra-pair geometry of §21, and complete C certificates of §34'],
      ['(18,22)', '§23: product bound and four exact slack alternatives'],
      ['(20,20)', '§24: product bound on either side of polarity and two remaining exact certificates']
    ],[145,width-145])
    p('For (16,18), the few-full reduction of Section 42 '
      'covers every possible slack cell and local maximum. '
      'Its three-full-pair residues no longer need an '
      'additional numerical certificate: Section 50 '
      'puts their three independent full normals into '
      'the cube-fibre form. Its five-point fibre is '
      'excluded there, and all four other distributions '
      'are excluded in Sections 52–54. Each has '
      'at least twenty facets unless a nonzero-kernel '
      'full support occurs; that alternative has rank '
      'at least four and is excluded by Sections '
      '30–32. This closes the final branch of '
      'the ledger.')
    p('The finite arithmetic has a direct meaning on paper: '
      'row domains, integer recurrences, parameter cells '
      'and exact negative linear combinations are '
      'displayed. Their accompanying fraction-arithmetic '
      'programs independently check the tables. '
      'They do not establish the geometric lemmas; '
      'those are proved in the preceding sections. '
      'As usual, the classical three-dimensional '
      'convex rigidity theorem stated in Section 10 '
      'is used as a standard mathematical theorem; '
      'the dimensional extension and every stress '
      'localization used here are supplied explicitly.')

    section(56, 'Conclusion')
    p('Suppose a centrally symmetric five-dimensional '
      'convex polytope had fewer than 243 nonempty '
      'faces. Euler’s relation and antipodal parity '
      'would give s(P)=3+2t with even t≤118. '
      'The cube-section argument and polarity '
      'exclude vertex or facet counts at most '
      'twelve. Orienting polarity so v≤h, '
      'the flag and rigidity inequalities place '
      '(v,h) in the fifteen-pair ledger of '
      'Section 5. Section 55 excludes every '
      'entry. Therefore no such polytope '
      'exists, and')
    eq('f₁(P)+f₃(P)≥120,<br/>'
       's(P)=3+2(f₁(P)+f₃(P))≥243=3<super>5</super>.','56.1')
    p('The five-cube has face counts '
      '(32,80,80,40,10). Including the cube '
      'itself gives exactly 243 nonempty '
      'faces. Thus the five-dimensional '
      'bound is sharp. □')
