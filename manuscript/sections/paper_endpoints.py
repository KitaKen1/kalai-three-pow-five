"""Written geometry and fully printed rational certificates for two endpoints."""
import json

from verification.paths import ROOT


def add_endpoints(p, eq, section, table, width):
    section(20, 'A product facet: the supporting functionals')
    p('We now supply the product-facet geometry and the complete arithmetic '
      'closure at (18,22) and (20,20). All quantities in the certificates '
      'below are face counts or integer coefficients. The argument does not '
      'require a proof assistant or access to its source.')
    p('<b>Lemma 20.1.</b> <i>A four-polytope with row (9,18,15,6;36) '
      'has the face lattice of the product of two triangles.</i> Its polar '
      'has six vertices and nine facets. In the rank-one Gale description '
      'of Section 14, let a,b,z be the positive, negative and zero '
      'multiplicities. One has a,b≥2, a+b+z=6, and ab+z=9. '
      'The only possibility is a=b=3 and z=0. Facet complements in '
      'the polar consist of one member of each triple. Thus the original '
      'nine vertices are x<sub>ij</sub>, 0≤i,j≤2. Its six facets are '
      'R<sub>i</sub> and C<sub>j</sub>, with x<sub>ab</sub> in '
      'R<sub>i</sub> exactly when a≠i and in C<sub>j</sub> exactly '
      'when b≠j. This establishes the recognition without assuming an '
      'affine product realization. □')
    p('Let F be such a facet of the five-polytope, exposed at level one '
      'by c. Each R<sub>i</sub> is a ridge of the five-polytope and '
      'belongs to another facet exposed by c<sub>i</sub>, also at '
      'level one. Put h<sub>i</sub>=c−c<sub>i</sub>. Likewise '
      'put k<sub>j</sub>=c−d<sub>j</sub> for the other facet at '
      'C<sub>j</sub>. On the vertices of F we have')
    eq('h<sub>i</sub>(x<sub>ab</sub>)=0 (i≠a), '
       'h<sub>a</sub>(x<sub>ab</sub>)&gt;0;<br/>'
       'k<sub>j</sub>(x<sub>ab</sub>)=0 (j≠b), '
       'k<sub>b</sub>(x<sub>ab</sub>)&gt;0.', '20.1')
    p('<b>Lemma 20.2 (Positive representation).</b> <i>There are positive '
      'numbers γ<sub>i</sub>,δ<sub>j</sub> such that '
      'c=∑γ<sub>i</sub>h<sub>i</sub>+∑δ<sub>j</sub>k<sub>j</sub>.</i> '
      'Define Ψ(γ,δ) to be this sum. Evaluation at x<sub>ab</sub> '
      'sees only γ<sub>a</sub> and δ<sub>b</sub>. A kernel vector '
      'with γ<sub>0</sub>=0 consequently has every δ<sub>b</sub>=0 '
      'and then every γ<sub>a</sub>=0. Thus dim ker Ψ≤1. The '
      'domain has dimension six and the codomain five, so Ψ is onto '
      'and its kernel has dimension one.')
    p('Normalize a nonzero kernel vector (u,w) by u<sub>0</sub>&gt;0. '
      'Equation (20.1) forces all u<sub>a</sub>&gt;0 and all '
      'w<sub>b</sub>&lt;0. Take any representation (γ°,δ°) of c. '
      'Evaluating it and the kernel vector at x<sub>ab</sub> gives')
    eq('γ°<sub>a</sub>h<sub>a</sub>(x<sub>ab</sub>) '
       '+ δ°<sub>b</sub>k<sub>b</sub>(x<sub>ab</sub>)=1,<br/>'
       'u<sub>a</sub>h<sub>a</sub>(x<sub>ab</sub>) '
       '+ w<sub>b</sub>k<sub>b</sub>(x<sub>ab</sub>)=0.', '20.2')
    p('These equations imply −γ°<sub>a</sub>/u<sub>a</sub> '
      '&lt; δ°<sub>b</sub>/(−w<sub>b</sub>) for every a,b. '
      'Choose η strictly between the maximum of the three left '
      'endpoints and the minimum of the three right endpoints. '
      'Then γ=γ°+ηu and δ=δ°+ηw are positive and still represent '
      'c. This proves the lemma. □')
    p('Set U<sub>ab</sub>=γ<sub>a</sub>h<sub>a</sub>(x<sub>ab</sub>) '
      'and V<sub>ab</sub>=δ<sub>b</sub>k<sub>b</sub>(x<sub>ab</sub>). '
      'Both are positive and U<sub>ab</sub>+V<sub>ab</sub>=1. '
      'For potentials u<sub>i</sub>,w<sub>j</sub>, the functional '
      'L=∑u<sub>i</sub>γ<sub>i</sub>h<sub>i</sub>+'
      '∑w<sub>j</sub>δ<sub>j</sub>k<sub>j</sub> satisfies')
    eq('L(x<sub>ab</sub>)=u<sub>a</sub>U<sub>ab</sub>+'
       'w<sub>b</sub>V<sub>ab</sub>.', '20.3')

    section(20, 'A product facet: thirty-six side edges, continued')
    p('<b>Lemma 20.3.</b> <i>If v=18 and F has row (9,18,15,6;36), '
      'then e≥72.</i> The vertices of P are exactly the nine '
      'x<sub>ab</sub> and their antipodes, since a facet cannot contain '
      'antipodal vertices. Choose i≠i′ and j≠j′. Give u the values '
      '1,−1,0 at i,i′ and the remaining index, and give w the '
      'values 1,−1,0 at j,j′ and its remaining index. By (20.3), '
      'L has maximum one only at x<sub>ij</sub> in F and minimum '
      'minus one only at x<sub>i′j′</sub>. On −F its maximum '
      'is therefore only at −x<sub>i′j′</sub>. The exposed '
      'face is the segment joining these two vertices.')
    p('There are (3·2)²=36 different such edges: their positive and '
      'negative endpoints identify the ordered pairs. None is an '
      'edge contained in F or −F. Those two facets contain 18 edges '
      'each. The three disjoint sets give 36+18+18=72. □')
    p('<b>Corollary 20.4.</b> <i>A counterexample at (18,22) has no '
      'facet of this row.</i> Every four-dimensional facet has at '
      'least five ridges. Each ridge belongs to two facets, so '
      '2r≥5h=110. Lemma 20.3 gives t=e+r≥72+55=127, '
      'contrary to t≤118. □')

    section(21, 'A product facet with an extra antipodal pair')
    p('<b>Lemma 21.1.</b> <i>If v=20 and F has row '
      '(9,18,15,6;36), then e≥66.</i> In addition to ±x<sub>ij</sub>, '
      'there is one pair ±z. Write Z<sub>i</sub>=γ<sub>i</sub>h<sub>i</sub>(z) '
      'and W<sub>j</sub>=δ<sub>j</sub>k<sub>j</sub>(z). '
      'Their sum is c(z), which lies strictly between −1 and 1: '
      'z and −z are vertices outside F.')
    p('For a candidate c₀=((i,i′),(j,j′)) among the same 36 ordered '
      'pairs, use potentials 1,−1,α on the three row indices and '
      '1,−1,β on the column indices, where −1&lt;α,β&lt;1. '
      'The two intended endpoints remain the unique maxima on '
      'F and −F. If k,l are the unused indices, put')
    eq('D=Z<sub>i</sub>−Z<sub>i′</sub>+W<sub>j</sub>−W<sub>j′</sub>, '
       'a=Z<sub>k</sub>, b=W<sub>l</sub>;<br/>'
       'L(z)=D+αa+βb.', '21.1')
    p('If the open interval (D−|a|−|b|,D+|a|+|b|) meets '
      '(−1,1), choose α,β so that |L(z)|&lt;1, and the '
      'candidate edge survives. A candidate is blocked above '
      'if D−|a|−|b|≥1, and below if −D−|a|−|b|≥1. '
      'The degenerate cases a=b=0,D=±1 are counted as surviving: '
      'L exposes a triangle with the two intended endpoints and '
      '±z. Three different vertices of a polytope cannot be '
      'collinear, and each side of this triangle is a face of P. '
      'These alternatives cover every candidate.')
    p('Let B be the set blocked above, after deleting those degenerate '
      'cases. Reversing both ordered pairs maps B bijectively to the '
      'set blocked below. The two sets are disjoint. Thus at least '
      '36−2|B| candidate edges survive. For c₀∈B, one has D&gt;1. '
      'Let L₀ use α=β=0 and put ζ=c(z). The functional')
    eq('L₀ + ((D−1)/(1−ζ))c', '21.2')
    p('exposes the edge joining z to x<sub>ij</sub>: on F its '
      'unique maximum is 1+(D−1)/(1−ζ), and z has exactly '
      'that value; on −F the maximum is smaller. The functional '
      'L₀−((D−1)/(1+ζ))c similarly exposes the edge joining '
      'z to −x<sub>i′j′</sub>. Their negatives supply the '
      'corresponding edges at −z.')
    p('Let f be the number of distinct first cells (i,j) of B and '
      's the number of distinct second cells (i′,j′). These are '
      'distinct neighbours of z, so deg(z)≥f+s. Also deg(z)≥5 '
      'because its tangent cone spans five-dimensional space. '
      'The resulting edge sets are disjoint, giving')
    eq('e ≥ 36+(36−2|B|)+2 max(5,f+s).', '21.3')

    section(21, 'The extra-pair combinatorics, continued')
    p('We prove |B|≤max(5,f+s)+3. Give an ordered pair (i,i′) '
      'orientation + if i′=i+1 modulo three and − otherwise. '
      'For two different pairs of the same orientation, the sum '
      'of Z<sub>i</sub>−Z<sub>i′</sub>−|Z<sub>k</sub>| '
      'is at most zero. For example the pairs (0,1),(1,2) '
      'give Z<sub>0</sub>−Z<sub>2</sub>−|Z<sub>2</sub>|−|Z<sub>0</sub>|≤0; '
      'the other choices are cyclic permutations or reversals. '
      'The same holds for W. Hence two members of B cannot have '
      'different row pairs of the same orientation and different '
      'column pairs of the same orientation: adding their defining '
      'inequalities would give 2≤0.')
    p('Within each of the four orientation blocks, the triple '
      '(row orientation, column orientation, j−i mod 3) '
      'determines a member of B. Indeed equal diagonals and '
      'different members force both ordered pairs to differ, '
      'which is the forbidden situation just proved. Each block '
      'therefore has at most three members; |B|≤12. Also '
      '|B|≤fs, since a first cell and a second cell uniquely '
      'specify the two ordered pairs.')
    p('Let m,n be the sizes of the ++ and −− blocks. The two '
      'mixed blocks contain at most six members in total, so '
      '|B|≤m+n+6, where m,n≤3. In each unmixed block, the '
      'second cell is the first cell shifted by (1,1) or '
      '(−1,−1). These shifts preserve the diagonal. Members '
      'on different diagonals cannot share either cell. On '
      'a common diagonal, a ++ member and a −− member may '
      'share their first cells or their second cells, but '
      'cannot share both: the two shifts differ. Consequently '
      'the total number of first- or second-cell coincidences '
      'is at most min(m,n), and')
    eq('f+s ≥ 2(m+n)−min(m,n).', '21.4')
    p('If |B|≥11, then m+n≥5. For m+n=5 the right side of '
      '(21.4) is at least eight; for m+n=6 it is nine. '
      'Together with |B|≤m+n+6 this gives |B|≤f+s+3. '
      'If |B|≤10 and f+s≥7 the same claim is immediate. '
      'If f+s=6, then |B|≤fs≤9; if f+s≤5, then '
      '|B|≤fs≤6≤8. These cases prove the claimed inequality. '
      'Substitution in (21.3) gives e≥72−6=66, completing '
      'the proof of Lemma 21.1. □')

    section(22, 'Exact row inequalities and their summation')
    p('Here is the arithmetic certificate method, including its whole '
      'finite row domain. Write S=G<super>*</super> and use '
      'v,h,t,e,I as global variables. The identities already proved give')
    eq('r=t−e, p=t+2−v−h,<br/>'
       'x=G−e+3t+2v−3h−4,<br/>'
       'y=S+e+2t−3v+2h−4,<br/>'
       'A=2I−G−S+26−8(v+h),<br/>'
       'B=−I−G+2S+9e−3t−8v+7h−4,<br/>'
       'C=−I+2G−S−9e+6t+7v−8h−4.', '22.1')
    p('A cost is specified by ten integers '
      '(c₀,cₙ,cₑ,cₚ,cᵣ,cⱼ,a₅,a₆,b₅,b₆). For a facet '
      'row R=(n,e₀,p₀,r₀;J), its value is')
    eq('φ(R)=c₀+cₙn+cₑe₀+cₚp₀+cᵣr₀+cⱼJ<br/>'
       '+a₅[n=5]+a₆[n=6]+b₅[r₀=5]+b₆[r₀=6].', '22.2')
    p('Square brackets are zero-one indicators. Let N₅,N₆ count '
      'facets with five or six vertices and R₅,R₆ count facets '
      'with five or six ridges. Give these counts subscripts F '
      'and S on the two sides of polarity. Each is even. The '
      'sum of (22.2) over facets is the linear form')
    eq('Φ=c₀h+cₙI+cₑ(I+y−2r)+cₚy+2cᵣr<br/>'
       '+2cⱼ(I+x−2e)+a₅N<sub>F5</sub>+a₆N<sub>F6</sub>'
       '+b₅R<sub>F5</sub>+b₆R<sub>F6</sub>.', '22.3')
    p('For a second cost ψ, its polar sum Ψ is obtained by '
      'v↔h, e↔r, x↔y, G↔S and F↔S. If the two costs '
      'are nonnegative on their respective row domains, Φ,Ψ≥0.')
    p('For completeness, those domains contain every possible facet '
      'row. If n≤7 or r₀≤7, use the 24 rows in Section 15 '
      'and their duals, subject to n≤nmax, 0≤2g≤cap, and '
      'the stated exclusions. Otherwise n,r₀≥8 and all rows '
      'are in the following integer box:')
    eq('8≤n≤nmax, &nbsp; 0≤e₀≤n(n−1)/2,<br/>'
       '8≤r₀≤⌊(4e₀−7n+10)/3⌋, &nbsp; p₀=e₀+r₀−n,<br/>'
       '3n+3r₀−10≤J≤min(4e₀−4n, '
       '4p₀−4r₀, 3n+3r₀−10+⌊cap/2⌋).', '22.4')
    p('The upper bound on edges counts vertex pairs. In a '
      'four-polytope, summing minimum degree three in every '
      'three-face gives J+4n≤4e₀; polarity gives J+4r₀≤4p₀. '
      'These facts, Euler and g≥0 prove (22.4). Thus the '
      'box is an outer approximation; it need not be realizable '
      'to make a cost valid for every actual facet.')

    section(22, 'Checking a cost on the complete row domain, continued')
    p('The finite calculation for the large box has a particularly '
      'short exact recurrence. After substituting p₀=e₀+r₀−n, '
      'put dₙ=cₙ−cₚ, dₑ=cₑ+cₚ, dᵣ=cᵣ+cₚ. For each '
      'n,e₀,r₀ in (22.4), set L=3n+3r₀−10 and let U be '
      'the displayed upper bound. Discard the triple if L&gt;U. '
      'The minimum over J is attained at L when cⱼ≥0 and '
      'at U when cⱼ&lt;0. Hence the minimum cost on the '
      'whole large box is exactly')
    eq('min {c₀+dₙn+dₑe₀+dᵣr₀+cⱼ '
       '(L if cⱼ≥0, U otherwise)}.', '22.5')
    p('There are no indicator terms here, since n,r₀≥8. '
      'For the small rows substitute the printed row entries in '
      '(22.2). Section 24 prints both minima for every cost. '
      'The symbol “—” denotes an empty large box. The integers '
      'are obtained by the finite ranges (22.4) and the endpoint '
      'substitution (22.5), so neither rounding nor a numerical '
      'optimization assumption enters this step.')
    p('For each case below, label the following nonnegative linear '
      'forms Q₁,…,Q₂₃, in the printed order:')
    table([
        ['<b>Labels</b>', '<b>Nonnegative forms</b>'],
        ['Q₁–Q₁₁', 'e, p, r, I, x, y, G, S, A, B, C'],
        ['Q₁₂–Q₁₉', 'N<sub>F5</sub>, N<sub>F6</sub>, R<sub>F5</sub>, '
         'R<sub>F6</sub>, N<sub>S5</sub>, N<sub>S6</sub>, '
         'R<sub>S5</sub>, R<sub>S6</sub>'],
        ['Q₂₀, Q₂₁', 'vh−2I, 118−t'],
        ['Q₂₂, Q₂₃', 'Φ, Ψ from the two case costs']
    ], [100,width-100])
    p('List the additional conditions of a case in order. A condition '
      'z≥b supplies H=z−b; z≤b supplies H=b−z; an equality '
      'supplies both forms, with z−b first. Number these '
      'H₁,H₂,… in that order. The final line of each case '
      'prints nonnegative integer multipliers and a positive '
      'integer κ. After the substitutions (22.1), the indicated '
      'sum is identically −κ. Since every summand is '
      'nonnegative, that identity is a contradiction. A reader '
      'can check it by collecting coefficients of t,e,I,G,S '
      'and the eight row counts.')

    section(23, 'Complete closure at (18,22) and (20,20)')
    p('<b>Proposition 23.1.</b> <i>Neither (18,22) nor (20,20) '
      'is the vertex/facet pair of a counterexample.</i> At '
      '(18,22), Corollary 20.4 excludes the product row on '
      'the facet side. The vertex limits for facets of P '
      'and its polar are nine and eleven. Use the 69 cases '
      'labelled A1–A69 in Section 24, excluding '
      '(9,18,15,6;36) only on the facet side.')
    p('Here is their coverage. First separate G≥22, '
      '12≤G≤20, and G≤10. In the last range separate '
      'S≥32, 20≤S≤30, and S≤18. This leaves just '
      'the sixty even pairs G∈{0,2,4,6,8,10}, '
      'S∈{0,2,…,18}. Nine rectangles cover all but '
      'the following nine individual pairs:')
    eq('(0,10), (2,4), (2,6), (2,8), (2,10), '
       '(2,12), (4,10), (4,12), (4,14).', '23.1')
    p('The conditions printed for these pairs split only on '
      'the even quantities t,e,I,N<sub>F5</sub>,N<sub>F6</sub>, '
      'R<sub>S5</sub>,R<sub>S6</sub>. Every split is '
      'z≤b or z≥b+2, which exhausts the even integers. '
      'For example, (0,10) first splits t≤116 or t=118; '
      'in the latter part it splits e≤54 or e≥56; '
      'if e≤54, it splits R<sub>S5</sub>≤2 or ≥4; '
      'in the last part it splits R<sub>S6</sub>≤10 '
      'or ≥12. All five resulting cases are printed. '
      'The other pairs are resolved by the full condition '
      'lists in the same way. Whenever G=0 or S=0, '
      'Section 13 supplies A=0. There is therefore '
      'no omitted slack value or omitted boundary equality.')
    p('At (20,20), a product facet gives e≥66≥62 by '
      'Lemma 21.1, and the case B1 applies. A product '
      'facet of the polar gives r≥66≥62 and B2 applies. '
      'If neither side has that row, use B3–B7. Their '
      'five conditions exhaust G,S≥0 even: G≥12; '
      'G≤10,S≥20; G≤10,6≤S≤18; G≤10,2≤S≤4; '
      'G≤10,S=0. In the last case A=0. The respective '
      'vertex limits are ten on both sides.')
    p('The cap 1000 in a case denotes the uniform generous bound. '
      'Indeed (3.6) and 2I≤vh give '
      'G+S≤vh−8(v+h)+26, namely 102 or 106 for '
      'these two endpoints. By (12.3), every local '
      '2g is at most its global slack. Smaller caps '
      'in the tables are the upper bounds of the '
      'corresponding slack cells. Thus all local '
      'cost hypotheses are established. Every case '
      'has nonnegative costs and a strictly negative '
      'constant sum in Section 24, which proves the '
      'proposition. □')
    p('The companion arithmetic check also partitions each even '
      'axis at every printed boundary, rather than testing '
      'random configurations. It checks 32,196 complete '
      'axis cells for the first endpoint and 3,025 for '
      'the non-product branch of the second, using all '
      '69 and all five applicable cases, respectively. '
      'This is an optional independent check of the '
      'printed coverage, not a hypothesis of the argument.')

    section(24, 'The printed integer certificates')
    p('A cases use (v,h)=(18,22), nmax=(9,11), excluding '
      '(9,18,15,6;36) on F only. B1 and B2 use '
      '(20,20), nmax=(10,10), without exclusions. '
      'B3–B7 exclude that row on both sides. Every '
      'case assumes t≤118, already Q₂₁; an additional '
      'printed t≤118 is harmless. F and S after '
      '“cap” specify the two local stress caps. '
      'The cost tuples have exactly the coefficient '
      'order in (22.2). Minima are reported as '
      '(small rows, large box). All multipliers '
      'refer to Q and H as defined in Section 22.')
    from verification.certificate_checks import universe,local_cost
    data=json.loads((ROOT/'certificates'/'mathematical-certificate-data.json').read_text())
    certs={z['label']:z for z in json.loads(
        (ROOT/'evidence/printed-cost-certificates.json').read_text())['certificates']}
    count={'A':0,'B':0}
    for leaf in data['leaves']:
        prefix='A' if leaf['endpoint']==[18,22] else 'B'
        count[prefix]+=1
        label=prefix+str(count[prefix])
        proof=certs[leaf['label']]
        p('<b>'+label+'.</b> cap F='+str(leaf['capF'])+', S='+str(leaf['capS'])+'. '
          'Conditions: '+', '.join(bound_text(z) for z in leaf['bounds'])+'.')
        for side in ('F','S'):
            rows=universe(leaf['nmax'+side],leaf['cap'+side],
                          tuple(tuple(r) for r in leaf['excluded'+side]))
            small=[r for r in rows if r[0]<=7 or r[3]<=7]
            large=[r for r in rows if r[0]>=8 and r[3]>=8]
            minima=[str(min(local_cost(leaf['cost'+side],r) for r in group))
                    if group else '—' for group in (small,large)]
            if any(int(x)<0 for x in minima if x!='—'):
                raise ValueError('A printed cost is negative')
            p(('φ' if side=='F' else 'ψ')+'='+tuple_text(leaf['cost'+side])+
              '; minima ('+', '.join(minima)+').')
        terms=[]
        for key,w in sorted(proof['multipliers'].items(),key=lambda z:int(z[0])):
            i=int(key)
            ref='Q'+str(i+1) if i<23 else 'H'+str(i-22)
            terms.append(('' if w==1 else str(w)+'·')+ref)
        p('Identity: '+' + '.join(terms)+' = −'+str(-proof['constant'])+'.')


def tuple_text(xs):
    return '('+', '.join(str(x).replace('-','−') for x in xs)+')'


def bound_text(bound):
    k,s,b=bound
    names={'nF5':'N<sub>F5</sub>','nF6':'N<sub>F6</sub>',
           'rF5':'R<sub>F5</sub>','rF6':'R<sub>F6</sub>',
           'nS5':'N<sub>S5</sub>','nS6':'N<sub>S6</sub>',
           'rS5':'R<sub>S5</sub>','rS6':'R<sub>S6</sub>'}
    return names.get(k,k)+{'<=':'≤','>=':'≥','=':'='}[s]+str(b)
