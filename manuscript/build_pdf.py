#!/usr/bin/env python3
"""Build the manuscript with ReportLab; no network access is required.

Run from the repository root: python3 -m manuscript.
Requires reportlab and DejaVu Serif fonts. Set KALAI_PDF_FONT_DIR to the
directory containing those font files if they are not in a standard location.
KALAI_PDF_OUTPUT can select a different output file.
"""
from pathlib import Path
import os
from reportlab.lib import colors
from reportlab.lib.enums import TA_CENTER, TA_JUSTIFY, TA_LEFT
from reportlab.lib.pagesizes import A4
from reportlab.lib.styles import ParagraphStyle
from reportlab.pdfbase import pdfmetrics
from reportlab.pdfbase.ttfonts import TTFont
from reportlab.platypus import (
    SimpleDocTemplate, Paragraph, Spacer, PageBreak, Table, TableStyle,
)

ROOT = Path(__file__).resolve().parents[1]
FONT_FILES = ('DejaVuSerif.ttf', 'DejaVuSerif-Bold.ttf',
              'DejaVuSerif-Italic.ttf', 'DejaVuSerif-BoldItalic.ttf')
font_setting = os.environ.get('KALAI_PDF_FONT_DIR')
font_candidates = ([Path(font_setting).expanduser()] if font_setting else
                   [Path('/usr/share/fonts/truetype/dejavu'),
                    Path('/usr/local/share/fonts/dejavu')])
FONT_DIR = next((p for p in font_candidates
                 if all((p / f).is_file() for f in FONT_FILES)), None)
if FONT_DIR is None:
    raise RuntimeError('Set KALAI_PDF_FONT_DIR to a directory containing '
                       'the four DejaVu Serif font files.')
for name, file in [('Serif','DejaVuSerif.ttf'), ('SerifB','DejaVuSerif-Bold.ttf'),
                   ('SerifI','DejaVuSerif-Italic.ttf'), ('SerifBI','DejaVuSerif-BoldItalic.ttf'),
                   ('MathUpright','DejaVuSerif.ttf')]:
    pdfmetrics.registerFont(TTFont(name, str(FONT_DIR / file)))
pdfmetrics.registerFontFamily('Serif', normal='Serif', bold='SerifB', italic='SerifI', boldItalic='SerifBI')
pdfmetrics.registerFontFamily('MathUpright', normal='MathUpright', bold='MathUpright',
                              italic='MathUpright', boldItalic='MathUpright')

W, H = A4
WIDTH = W - 144
S = {
    'body': ParagraphStyle('body', fontName='Serif', fontSize=10.4, leading=13.8,
        alignment=TA_JUSTIFY, spaceAfter=8.0),
    'heading': ParagraphStyle('heading', fontName='SerifB', fontSize=13.0, leading=17,
        spaceAfter=13),
    'title': ParagraphStyle('title', fontName='SerifB', fontSize=18.2, leading=24,
        alignment=TA_CENTER, spaceAfter=0),
    'date': ParagraphStyle('date', fontName='Serif', fontSize=10.0, leading=14,
        alignment=TA_CENTER, spaceAfter=0),
    'equation': ParagraphStyle('equation', fontName='Serif', fontSize=10.8, leading=17,
        alignment=TA_CENTER),
    'number': ParagraphStyle('number', fontName='Serif', fontSize=9, leading=17,
        alignment=TA_CENTER),
    'cell': ParagraphStyle('cell', fontName='Serif', fontSize=9.8, leading=13,
        alignment=TA_LEFT),
}

story = []
def printable(text):
    # Use glyphs present in the embedded fonts. Backslash denotes set difference.
    return (text.replace('ℓ', '<i>l</i>').replace('∖', '\\')
            .replace('⋂', '∩').replace('⋃', '∪'))
def p(text):
    # DejaVu Serif Italic lacks the double-struck real-number symbol.
    text = text.replace('ℝ', '<font name="MathUpright">ℝ</font>')
    text = printable(text)
    story.append(Paragraph(text, S['body']))
def eq(text, number):
    text = printable(text)
    t = Table([[Paragraph(text, S['equation']), Paragraph('('+number+')', S['number'])]],
              colWidths=[WIDTH-43, 43])
    t.setStyle(TableStyle([('VALIGN',(0,0),(-1,-1),'MIDDLE'),
        ('LEFTPADDING',(0,0),(-1,-1),0), ('RIGHTPADDING',(0,0),(-1,-1),0),
        ('TOPPADDING',(0,0),(-1,-1),4), ('BOTTOMPADDING',(0,0),(-1,-1),8)]))
    story.append(t)
def section(n, title):
    if n > 1: story.append(PageBreak())
    story.append(Paragraph(str(n)+'&nbsp;&nbsp; '+title, S['heading']))
def table(rows, widths, compact=False):
    data = [[Paragraph(printable(c), S['cell']) for c in r] for r in rows]
    t = Table(data, colWidths=widths, repeatRows=1, hAlign='CENTER')
    t.setStyle(TableStyle([('LINEABOVE',(0,0),(-1,0),0.6,colors.black),
        ('LINEBELOW',(0,0),(-1,0),0.4,colors.black),
        ('LINEBELOW',(0,-1),(-1,-1),0.6,colors.black),
        ('VALIGN',(0,0),(-1,-1),'TOP'), ('TOPPADDING',(0,0),(-1,-1),3 if compact else 6),
        ('BOTTOMPADDING',(0,0),(-1,-1),3 if compact else 6), ('LEFTPADDING',(0,0),(-1,-1),8),
        ('RIGHTPADDING',(0,0),(-1,-1),8)]))
    story.extend([t, Spacer(1,12)])

story.append(Spacer(1,54))
story.append(Paragraph("Kalai's 3<super size=\"11\">d</super> conjecture<br/>in dimension five", S['title']))
story.append(Spacer(1,26))
story.append(Paragraph('11 October 2026 &nbsp; • &nbsp; Mathematical draft 4', S['date']))
story.append(Spacer(1,37))

section(1, 'Problem and notation')
p('Let <i>P</i> be a full-dimensional convex polytope in ℝ<super>5</super>, centrally symmetric '
  'about the origin. A polytope is the convex hull of a finite set. For 0 ≤ <i>i</i> ≤ 4, '
  'write <i>f</i><sub>i</sub>(<i>P</i>) for its number of <i>i</i>-dimensional faces, and set')
eq('<i>s</i>(<i>P</i>) = 1 + <i>f</i><sub>0</sub> + <i>f</i><sub>1</sub> + '
   '<i>f</i><sub>2</sub> + <i>f</i><sub>3</sub> + <i>f</i><sub>4</sub>.', '1.1')
p('The empty face is excluded, and the whole polytope is included. An exposed face is the '
  'set of maximizers of a linear functional on <i>P</i>. Every face of a polytope is exposed; '
  'the zero functional exposes <i>P</i> itself.')
p('<b>Target 1.1 (Kalai’s bound in dimension five).</b> <i>Every full-dimensional, '
  'origin-symmetric convex polytope in ℝ<super>5</super> satisfies</i>')
eq('<i>s</i>(<i>P</i>) ≥ 3<super>5</super> = 243.', '1.2')
p('The bound is sharp: each face of [−1,1]<super>5</super> chooses, in each coordinate, '
  'the negative endpoint, the positive endpoint, or the whole interval. These 3<super>5</super> '
  'choices include the whole cube.')
p('This manuscript gives a mathematical proof through a fifteen-pair '
  'reduction, geometric endpoint arguments and exact finite tables. '
  'All real parameter cases, including the parallel and boundary '
  'cases in the three-full-pair branch, are included. The standard '
  'three-dimensional convex rigidity theorem is stated in Section 10; '
  'its dimensional extension and the stress-space constructions '
  'are proved there and in the following sections.')
p('The argument reduces the face-count inequality to fifteen possible '
  'vertex/facet-count pairs. Euler and flag identities give the arithmetic '
  'reduction, a central cube-section argument handles small vertex counts, '
  'and facet geometry supplies the endpoint estimates. Sections 2–8 describe '
  'these reductions and selected endpoint arguments. Section 9 states '
  'the assembly principle. Sections 10–19 develop auxiliary arguments. '
  'Sections 20–29 supply product-facet proofs, exact endpoint certificates, '
  'two-facet stress localization, ridge capacities and the rank-three reduction. '
  'Sections 30–37 supply continuous cube-lift certificates, quadrilateral '
  'budgets and further complete cost tables. Sections 38–50 supply the remaining '
  'product-facet geometry, stronger weights, exact few-full reduction and '
  'one- and two-full-pair closures, and the five-point fibre exclusion. '
  'Sections 51–54 give exact balanced-section tables and complete '
  'the three-full-pair cases. Section 55 assembles every endpoint, '
  'and Section 56 gives the conclusion.')
p('The target concerns Conjecture A in dimension five. It makes no simplicity, simpliciality, '
  'or vertex-count assumption. The all-dimensions conjecture and its unrestricted '
  'dimension-at-least-six variant are outside this target.')

section(2, 'Euler, parity, and the incidence bound')
p('Write <i>v</i> = <i>f</i><sub>0</sub>, <i>e</i> = <i>f</i><sub>1</sub>, '
  '<i>p</i> = <i>f</i><sub>2</sub>, <i>r</i> = <i>f</i><sub>3</sub>, and '
  '<i>h</i> = <i>f</i><sub>4</sub>. Put <i>t</i> = <i>e</i> + <i>r</i> and '
  '<i>u</i> = <i>v</i> + <i>h</i>. Euler’s relation on the boundary is')
eq('<i>v</i> − <i>e</i> + <i>p</i> − <i>r</i> + <i>h</i> = 2.', '2.1')
p('<b>Lemma 2.1 (The counting target).</b> <i>The number of nonempty faces is '
  '3 + 2t. Hence the desired inequality is equivalent to t ≥ 120.</i>')
p('<i>Proof.</i> Equation (2.1) gives <i>p</i> = 2 + <i>t</i> − <i>u</i>. '
  'Substitution into 1 + <i>u</i> + <i>t</i> + <i>p</i> gives 3 + 2<i>t</i>. □')
p('Central symmetry and full dimension imply that the origin lies in the interior. '
  'A proper exposed face has a strictly positive support value for its nonzero exposing '
  'functional. It cannot contain both a point and its antipode. Consequently <i>F</i> ↦ −<i>F</i> '
  'is a fixed-point-free involution on proper faces of each dimension.')
eq('<i>v</i>, <i>e</i>, <i>p</i>, <i>r</i>, <i>h</i> are even; '
   '<i>t</i> is even.', '2.2')
p('A flag is a chain of incident proper faces. Applying the same involution to every '
  'member of a flag also gives even flag counts. Let <i>I</i> = <i>f</i><sub>04</sub> '
  'count vertex–facet incidences. In particular, <i>I</i> is even.')
p('<b>Lemma 2.2 (Antipodal incidence bound).</b> <i>One has 2I ≤ vh.</i>')
p('<i>Proof.</i> Each facet contains at most one vertex from each of the '
  '<i>v</i>/2 antipodal vertex pairs. Summing its vertex count over the <i>h</i> facets '
  'gives <i>I</i> ≤ <i>vh</i>/2. □')
p('If a counterexample exists, Lemma 2.1 and parity give <i>t</i> ≤ 118. This two-unit '
  'gap will convert rational lower bounds just above 118 into the exact target 120.')

section(3, 'Flag identities and nonnegative slacks')
p('Let <i>f</i><sub>ij</sub> count pairs <i>F</i> ⊂ <i>G</i> of dimensions '
  '<i>i</i> and <i>j</i>, and define triple flags similarly. Set '
  '<i>x</i> = <i>f</i><sub>02</sub> and <i>y</i> = <i>f</i><sub>24</sub>. '
  'Euler’s relation in face figures and intervals gives')
eq('<i>f</i><sub>03</sub> = <i>I</i> + <i>x</i> − 2<i>e</i>, &nbsp; '
   '<i>f</i><sub>14</sub> = <i>I</i> + <i>y</i> − 2<i>r</i>,', '3.1')
eq('<i>f</i><sub>13</sub> = <i>I</i> + <i>x</i> + <i>y</i> − 2<i>t</i>,<br/>'
   '<i>f</i><sub>024</sub> = 2<i>I</i> + 2<i>x</i> + 2<i>y</i> − 4<i>t</i>.', '3.2')
p('Define the following integer quantities:')
eq('<i>A</i> = <i>f</i><sub>024</sub> − 3<i>x</i> − 3<i>y</i> + 9<i>p</i>,<br/>'
   '<i>B</i> = 2<i>f</i><sub>13</sub> − 3<i>f</i><sub>03</sub>, &nbsp; '
   '<i>C</i> = 2<i>f</i><sub>13</sub> − 3<i>f</i><sub>14</sub>,', '3.3')
eq('<i>G</i> = <i>e</i> + <i>x</i> − 3<i>p</i> − 5<i>v</i> + 10,<br/>'
   '<i>G</i><super>*</super> = <i>r</i> + <i>y</i> − 3<i>p</i> − 5<i>h</i> + 10.', '3.4')
p('All five are nonnegative. The quantity <i>A</i> is the sum, over polygonal '
  '2-faces <i>Q</i>, of the product of the vertex excess of <i>Q</i> and that of its '
  'polygonal face figure. The quantities <i>B</i> and <i>C</i> express minimum degree '
  'three in 3-faces and in the polar. The bounds <i>G</i>, <i>G</i><super>*</super> ≥ 0 '
  'come from the centrally symmetric rigidity bound.')
p('<b>Lemma 3.1 (The two global identities).</b> <i>The preceding quantities satisfy</i>')
eq('<i>A</i> + <i>B</i> + <i>C</i> = 9<i>p</i> − 6<i>t</i>,', '3.5')
eq('<i>G</i> + <i>G</i><super>*</super> + <i>A</i> = 2<i>I</i> − 8<i>u</i> + 26.', '3.6')
p('<i>Proof.</i> Substitute (3.1)–(3.4), cancel terms, and use (2.1). '
  'Nonnegativity in (3.5), together with <i>p</i> = 2 + <i>t</i> − <i>u</i>, yields '
  '3<i>u</i> ≤ <i>t</i> + 6. □')
p('The rigidity bound can be expressed by triangulating the 2-faces without '
  'adding vertices. The resulting symmetric rigid framework has '
  '<i>e</i> + <i>x</i> − 3<i>p</i> bars, and its rigidity implies '
  '5<i>v</i> ≤ <i>e</i> + <i>x</i> − 3<i>p</i> + 10. This is precisely '
  '<i>G</i> ≥ 0. Applying the same bound to the polar gives '
  '<i>G</i><super>*</super> ≥ 0.')

section(4, 'Small vertex counts and a cyclic orbit argument')
p('Suppose <i>v</i> ≤ 12. Choose six vectors <i>v</i><sub>1</sub>, …, '
  '<i>v</i><sub>6</sub> covering the vertices up to sign, padding unused positions '
  'with zero. The polar is defined by the six inequalities '
  '|⟨<i>y</i>, <i>v</i><sub>i</sub>⟩| ≤ 1. The coordinate map '
  '<i>y</i> ↦ (⟨<i>y</i>, <i>v</i><sub>i</sub>⟩)<sub>i</sub> is injective '
  'and has a five-dimensional hyperplane as image in ℝ<super>6</super>. '
  'Changing signs of coordinates makes its normal nonnegative. Thus its image is')
eq('<i>K</i> = [−1,1]<super>6</super> ∩ {<i>z</i> : '
   '∑<sub>i</sub> <i>a</i><sub>i</sub><i>z</i><sub>i</sub> = 0}, '
   '&nbsp; <i>a</i><sub>i</sub> ≥ 0.', '4.1')
p('Polarity and injective linear maps preserve the total face count. It remains '
  'to bound the number of cube faces whose relative interior meets the hyperplane. '
  'Such faces correspond bijectively to the faces of the section.')
p('<b>Lemma 4.1 (Central cube sections).</b> <i>For n ≥ 1 and nonnegative weights, '
  'at least 3<super>n−1</super> of the cube’s 3<super>n</super> face patterns '
  'meet the central hyperplane in their relative interior.</i>')
p('<i>Proof.</i> A pattern assigns to each coordinate one of +, −, or free. Let '
  '<i>W</i> be the total weight, and <i>P</i>, <i>N</i>, <i>F</i> the weights in '
  'the three states, so <i>P</i> + <i>N</i> + <i>F</i> = <i>W</i>. The minimum '
  'and maximum of the defining linear form on that face are')
eq('2<i>P</i> − <i>W</i>, &nbsp; <i>W</i> − 2<i>N</i>.', '4.2')
p('A pattern lies weakly on the positive side without lying in the hyperplane '
  'exactly when 2<i>P</i> ≥ <i>W</i> and 2<i>N</i> &lt; <i>W</i>. Cycle all '
  'coordinate states simultaneously by + ↦ − ↦ free ↦ +. Each orbit has three '
  'elements. At most one element is on this positive side: two state weights '
  'at least <i>W</i>/2 would force equality and the third weight zero, and the '
  'strict inequality then excludes a second qualifying element. If <i>W</i> = 0, '
  'all patterns lie in the hyperplane.')
p('Hence at most 3<super>n−1</super> patterns are on the positive side. '
  'Antipodal symmetry gives the same bound on the negative side. All other '
  'patterns meet the hyperplane in their relative interior, so their number is '
  'at least 3<super>n</super> − 2·3<super>n−1</super> = 3<super>n−1</super>. □')
p('Taking <i>n</i> = 6 gives 243. Applying the same argument to the polar also '
  'handles <i>h</i> ≤ 12. Parity therefore forces <i>v</i>, <i>h</i> ≥ 14 '
  'in every counterexample.')

section(5, 'The exact fifteen-pair reduction')
p('Assume <i>s</i>(<i>P</i>) &lt; 243. By Section 4, <i>v</i>, <i>h</i> ≥ 14. '
  'Replace <i>P</i> by its polar if needed, so <i>v</i> ≤ <i>h</i>. '
  'The total face count is preserved, and vertices and facets are exchanged.')
p('<b>Proposition 5.1 (Finite ledger).</b> <i>The pair (v,h) belongs to the following '
  'fifteen-element list.</i>')
table([['<b>Vertices v</b>', '<b>Possible facets h</b>'],
       ['14','16, 18, 20, 22, 24, 26'], ['16','16, 18, 20, 22, 24'],
       ['18','18, 20, 22'], ['20','20']], [130, WIDTH-130])
p('<i>Proof.</i> Parity and (2.1) give <i>t</i> ≤ 118. From Section 3, '
  '3<i>u</i> ≤ <i>t</i> + 6 ≤ 124. Since <i>u</i> is even,')
eq('<i>v</i> + <i>h</i> = <i>u</i> ≤ 40.', '5.1')
p('Nonnegativity in (3.6) gives 2<i>I</i> ≥ 8<i>u</i> − 26. '
  'Since <i>I</i> is even, 2<i>I</i> is divisible by four, whereas '
  '8<i>u</i> − 26 is congruent to two modulo four. Therefore')
eq('2<i>I</i> ≥ 8<i>u</i> − 24.', '5.2')
p('Combining this sharper integer bound with 2<i>I</i> ≤ <i>vh</i> yields')
eq('(<i>v</i> − 8)(<i>h</i> − 8) ≥ 40.', '5.3')
p('Because <i>v</i> ≤ <i>h</i> and their sum is at most 40, '
  '<i>v</i> can only be 14, 16, 18, or 20. Listing even <i>h</i> between '
  '<i>v</i> and 40 − <i>v</i> gives the table; (5.3) removes (14,14), '
  'for which the product is 36. Every other listed pair satisfies (5.3). □')
p('This arithmetic reduction avoids searching through polytopes with arbitrary real '
  'coordinates. The geometric work is confined to fifteen vertex/facet-count pairs. '
  'It does not assert that the inequalities classify all realizable polytopes in those '
  'pairs, or that every row of the table is realizable.')

section(6, 'Facet rows and their global sums')
p('For a four-dimensional facet <i>F</i>, write its row as '
  '<i>R</i> = (<i>n</i>, <i>e</i><sub>F</sub>, <i>p</i><sub>F</sub>, '
  '<i>r</i><sub>F</sub>; <i>J</i>), where <i>J</i> is its vertex–3-face '
  'incidence count. Summing rows over all facets gives')
eq('∑<sub>F</sub> <i>n</i> = <i>I</i>, &nbsp; '
   '∑<sub>F</sub> <i>e</i><sub>F</sub> = <i>f</i><sub>14</sub>, &nbsp; '
   '∑<sub>F</sub> <i>p</i><sub>F</sub> = <i>y</i>,<br/>'
   '∑<sub>F</sub> <i>r</i><sub>F</sub> = 2<i>r</i>, &nbsp; '
   '∑<sub>F</sub> <i>J</i> = 2<i>f</i><sub>03</sub>.', '6.1')
p('Set <i>q</i> = #{<i>F</i> : <i>n</i> = 7}. The following weights are used in '
  'the fourteen-vertex endpoints; the facet subscripts are suppressed inside a row.')
eq('<i>L</i><sub>1</sub> = 9<i>p</i> − 5<i>e</i> − <i>n</i> − <i>J</i> − 15,<br/>'
   '<i>L</i><sub>2</sub> = 12<i>n</i> − 10<i>e</i> + 12<i>p</i> − 3<i>J</i> − 20 '
   '+ 5[<i>n</i> = 7],<br/>'
   '<i>L</i><sub>3</sub> = 16<i>n</i> + 2<i>p</i> + 31<i>r</i> − 10<i>J</i> − 48 '
   '+ 12[<i>n</i> = 7].', '6.2')
p('The bracket denotes an indicator. The Gale classification of 4-polytopes '
  'with at most seven vertices gives 24 possible rows, on each of which '
  '<i>L</i><sub>1</sub>, <i>L</i><sub>2</sub>, <i>L</i><sub>3</sub>, and '
  '<i>g</i>(<i>R</i>) = <i>J</i> − 3<i>n</i> − 3<i>r</i> + 10 are nonnegative. '
  'At <i>v</i> = 14 every facet has at most seven vertices, so this classification applies.')
p('<b>Lemma 6.1 (Local-to-global identities).</b> <i>With global symbols v,h,t,A,G '
  'and the facet weights above,</i>')
eq('12<i>t</i> = 48<i>v</i> + 33<i>h</i> − 96 + 4<i>A</i> + 6<i>G</i> '
   '+ ∑<sub>F</sub> <i>L</i><sub>1</sub>,', '6.3')
eq('6<i>t</i> = 34<i>v</i> + 14<i>h</i> − 68 − 5<i>q</i><br/>'
   '+ 2<i>A</i> + 8<i>G</i> + ∑<sub>F</sub> <i>L</i><sub>2</sub>,', '6.4')
eq('∑<sub>F</sub> <i>L</i><sub>3</sub> + 2<i>A</i> + 22<i>G</i> '
   '= 6<i>t</i> − 62<i>v</i> + 124 + 12<i>q</i>.', '6.5')
p('<i>Proof.</i> Sum the linear expressions (6.2), use (6.1), and substitute the '
  'Euler and flag identities from Sections 2–3. □')
p('Stress localization supplies 2<i>g</i>(<i>R</i>) ≤ <i>G</i> for every facet. '
  'Another useful sum is ∑<sub>F</sub> <i>g</i>(<i>R</i>) '
  '= 2<i>G</i> + 4<i>v</i> + 4<i>h</i> − <i>I</i> − 8.')

section(7, 'Four endpoint exclusions')
p('At fourteen vertices a seven-vertex facet is full: it contains one vertex from '
  'every antipodal pair. The full-facet input needed here says that at least eight such '
  'facets, with <i>h</i> ≥ 18, force the target face bound. Therefore a counterexample '
  'with these counts has <i>q</i> ≤ 6: the facet count <i>q</i> is even. '
  'Sections 28–32 prove the full-normal rank alternatives and their geometric '
  'bounds; Proposition 40.1 combines them to establish this full-facet input.')
p('<b>Proposition 7.1.</b> <i>The pair (14,26) is excluded by the row sum. '
  'The pair (14,22) is excluded using the full-pyramid argument. The pairs '
  '(14,24) and (14,20) are excluded using the full-facet input proved in '
  'Sections 28–32 and Proposition 40.1.</i>')
p('<i>Proof. The pair (14,26).</i> Every facet has <i>L</i><sub>1</sub> ≥ 0. '
  'Equation (6.3) immediately gives')
eq('12<i>t</i> ≥ 48·14 + 33·26 − 96 = 1434.', '7.1')
p('Thus <i>t</i> ≥ 120, contradicting <i>t</i> ≤ 118.')
p('<i>The pair (14,24).</i> If <i>q</i> ≥ 8, use the geometric lemma. Otherwise '
  '<i>q</i> ≤ 6, and (6.4), nonnegativity, and parity give')
eq('6<i>t</i> ≥ 34·14 + 14·24 − 68 − 5·6 = 714.', '7.2')
p('So <i>t</i> ≥ 119, and its evenness forces <i>t</i> ≥ 120.')
p('<i>The pair (14,22).</i> Put <i>M</i><sub>22</sub> = <i>L</i><sub>2</sub> '
  '− 5[<i>n</i> = 7]. It is nonnegative on every catalogue row except '
  '(7,15,14,6;29). That exceptional row is a full pyramid. Its geometric '
  'consequence, proved in Section 18, makes <i>h</i> divisible by four, '
  'which excludes it when <i>h</i> = 22. '
  'Removing the indicator from (6.4) therefore gives')
eq('6<i>t</i> ≥ 34·14 + 14·22 − 68 = 716.', '7.3')
p('Again <i>t</i> ≥ 120. This estimate uses the pyramid parity lemma and avoids '
  'a stress-localization case split at this endpoint.')
p('<i>The pair (14,20).</i> Here <i>G</i> is even. If <i>G</i> ≥ 2, (6.5) '
  'and <i>q</i> ≤ 6 imply 6<i>t</i> ≥ 716. If <i>G</i> = 0, stress '
  'localization and <i>g</i> ≥ 0 make every facet’s <i>g</i> zero. Its summed '
  'identity then gives <i>I</i> = 128. But each facet has at most six vertices '
  'unless counted in <i>q</i>, so <i>I</i> ≤ 6·20 + 6 = 126, a contradiction. □')

section(8, 'Full facets and the remaining endpoints')
p('Two more fourteen-vertex pairs require full-facet geometry. Equation '
  '(3.6) and parity imply <i>I</i> ≥ 108 at (14,16), and <i>I</i> ≥ 116 at '
  '(14,18). Since each facet has at most seven vertices,')
eq('<i>I</i> ≤ 6<i>h</i> + <i>q</i>.', '8.1')
p('Thus <i>q</i> ≥ 12 at (14,16) and <i>q</i> ≥ 8 at (14,18). '
  'The full-normal arguments in Sections 28–32 exclude both '
  'configurations; Section 40.1 gives the complete assembly.')
p('At sixteen vertices a full facet has eight vertices. The endpoint arguments '
  'organize these configurations by the rank of their full normals and by the '
  'number of full antipodal pairs. They use geometric injections, local incidence '
  'estimates, and finite case distinctions. Rank-four configurations are '
  'treated by their supporting hyperplanes and exposed-face counts; '
  'the other ranks admit their own geometric reductions.')
p('For (16,24), the local <i>L</i><sub>1</sub> inequality extends to facets with '
  'at most eight vertices except the full tetrahedron-prism row (8,16,14,6;32). '
  'The full-prism argument is developed in Sections 16–17. When it is absent, (6.3) gives '
  '12<i>t</i> ≥ 48·16 + 33·24 − 96 = 1464, which suffices.')
p('The following table organizes the endpoint arguments. Section 19 '
  'supplies the numerical closure at (16,22). The geometric reductions '
  'and exact certificates for the other entries are developed in '
  'Sections 20–54; Section 55 records their complete coverage.')
table([['<b>Pair</b>', '<b>Geometric distinctions</b>'],
       ['(16,16), (16,18)', 'Full facets, rank of full normals, and ridge counts'],
       ['(16,20)', 'Number of full pairs, rank-four configurations, and face counts'],
       ['(16,22)', 'Facet-row costs, stress localization, and ridge parity'],
       ['(18,18)', 'Product facets on either side of polarity and stress bounds'],
       ['(18,20)', 'Product facets, edge lower bounds, and facet-row inequalities'],
       ['(18,22)', 'Product facets and the possible toric slacks'],
       ['(20,20)', 'Product facets on either side of polarity and row exclusions']],
      [118, WIDTH-118])

section(9, 'Assembly principle for the endpoint arguments')
p('The endpoint arguments combine with the reductions to give the '
  'desired face-count bound. The small '
  'vertex case and its polar counterpart are handled by Section 4. The '
  'remaining vertex/facet pairs are listed in Proposition 5.1, and the '
  'endpoint estimates excluding each of them are assembled in Section 55.')
p('<b>Proposition 9.1.</b> <i>If the bound holds at each of the fifteen pairs '
  'in Proposition 5.1, it holds for every centrally symmetric five-dimensional '
  'polytope.</i>')
p('<i>Proof.</i> Suppose '
  '<i>s</i>(<i>P</i>) &lt; 243. If <i>v</i> ≤ 12, Section 4 gives a contradiction. '
  'Apply the same argument to the polar to exclude <i>h</i> ≤ 12. Parity gives '
  '<i>v</i>, <i>h</i> ≥ 14. Choose <i>P</i> or its polar so that <i>v</i> ≤ <i>h</i>. '
  'The chosen polytope still has fewer than 243 faces.')
p('Its face and flag data satisfy the identities and inequalities of Section 3. '
  'Proposition 5.1 places its vertex/facet pair in the fifteen-element ledger. '
  'The endpoint estimates each give at least '
  '243 faces for the corresponding pair by the hypothesis of this proposition. '
  'Every possible pair is therefore '
  'contradictory. This proves the bound. □')
p('Section 55 supplies the endpoint hypothesis of this assembly '
  'principle by pointing to every complete exclusion in the subsequent '
  'geometric arguments and exact tables.')

from .mathematical_details import add_details
add_details(p, eq, section, table, WIDTH)

def decorate(canvas, doc):
    canvas.saveState()
    page = doc.page
    if page > 1:
        canvas.setFont('Serif', 8.0)
        head = "Kalai's 3"
        canvas.drawString(72, H-43, head)
        x = 72 + pdfmetrics.stringWidth(head, 'Serif', 8.0)
        canvas.setFont('Serif', 5.8)
        canvas.drawString(x, H-40.5, 'd')
        x += pdfmetrics.stringWidth('d', 'Serif', 5.8)
        canvas.setFont('Serif', 8.0)
        canvas.drawString(x, H-43, ' conjecture in dimension five')
        canvas.drawRightString(W-72, H-43, 'Mathematical draft 4')
        canvas.setLineWidth(0.4)
        canvas.line(72, H-47, W-72, H-47)
    canvas.setFont('Serif', 8.7)
    canvas.drawCentredString(W/2, 32, str(page))
    canvas.restoreState()

output_setting = os.environ.get('KALAI_PDF_OUTPUT')
out = (Path(output_setting).expanduser() if output_setting else
       ROOT / 'PDF' / 'kalai-three-pow-five.pdf')
out.parent.mkdir(exist_ok=True)
doc = SimpleDocTemplate(str(out), pagesize=A4, leftMargin=72, rightMargin=72,
    topMargin=62, bottomMargin=52, title="Kalai's 3^d conjecture in dimension five",
    author='Kenta Kitamura', subject='The five-dimensional face-count bound and its mathematical reduction',
    creator='ReportLab; mathematical draft 4, 11 October 2026')
doc.build(story, onFirstPage=decorate, onLaterPages=decorate)
print(out)
