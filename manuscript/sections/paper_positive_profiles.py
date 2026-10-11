"""Complete integer multiset lists at the positive two-pair endpoint."""
import json
from verification.paths import ROOT

def add_positive_profiles(p,eq,section,table,width):
    from .paper_endpoints import tuple_text
    from verification.certificate_checks import extended_local_cost
    section(46,'Nine-pair enumeration without an eight-vertex catalogue')
    D=json.loads((ROOT/'evidence/positive-profile-checks.json').read_text())
    rows=[tuple(R) for R in D['catalogue']]
    leaf={'costF':[0]*10,'quadF':1,'row_weight':'q55bsix'}
    weight=lambda R:extended_local_cost(leaf,'F',R)
    p('Central symmetry lets us choose one facet from each '
      'of the nine antipodal pairs. Seven choices have seven '
      'vertices; two choices are full. Number the possible '
      'rows by the following table. Rows 1–15 come from '
      'the planar Gale enumeration. Rows 16–47 are an '
      'arithmetic superset: Euler, 0≤g≤1, η≥0, J≥4r, '
      'J+4n≤4e and the excluded rows give precisely '
      'the listed possibilities. A full row with seven '
      'ridges is the dual of a classified seven-vertex '
      'row; the other full rows need no realization catalogue. '
      'The last column is a proved lower bound for w, '
      'including Lemma 44.1.')
    table([['<b>ID</b>','<b>Row (n,e,p,r;J)</b>','<b>g</b>','<b>r−n+1</b>','<b>Weight</b>']]+
          [[str(i),tuple_text(R),str(R[4]-3*R[0]-3*R[3]+10),
            str(R[3]-R[0]+1),str(weight(R))] for i,R in enumerate(rows,1)],
          [30,width-160,30,60,40])
    p('If mᵢ counts pair choices of row i, the entire search '
      'is the following system of nonnegative integer equations '
      'and one inequality:')
    eq('Σ<sub>i≤15</sub>mᵢ=7, Σ<sub>i≥16</sub>mᵢ=2, '
       'Σmᵢ(rᵢ−nᵢ+1)=4,<br/>'
       '2Σmᵢeᵢ=288+S, Σmᵢgᵢ=G−1, '
       'Σmᵢρᵢ≤78−3S.','46.1')
    p('The ridge-excess equality follows from Σnᵢ=65 '
      'and Σrᵢ=60. For a direct enumeration, choose '
      'two full row IDs with repetition. Subtract their '
      'ridge excesses from four. Visit the seven-vertex '
      'IDs in increasing order and choose a multiplicity '
      'between zero and the remaining pair count, stopping '
      'when its nonnegative ridge excess exceeds the '
      'remaining budget. Keep precisely the length-seven '
      'lists and test (46.1). This recurrence produces '
      '1914 lists before the cell equations and the '
      'following 151 lists after them. Every nine-ID '
      'list records pair choices; double it to recover '
      'the actual eighteen facets. The table is a '
      'complete output, not a sample.')
    table([['<b>(G,S)</b>','<b>Lists</b>']]+
          [[tuple_text((x['G'],x['S'])),str(len(x['profiles']))] for x in D['cells']],
          [width*.65,width*.35])
    for x in D['cells']:
        p('<b>(G,S)='+tuple_text((x['G'],x['S']))+'.</b> '+
          '; '.join(tuple_text(l) for l in x['profiles'])+'.')
