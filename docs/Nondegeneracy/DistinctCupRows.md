# Finite rows of the distinct cup word

`SKM/RouquierDistinctCupRows` formalizes the strict positive finite-row
calculation in Brundan–Ellis Lemma 7.1, `Lemma71Cup.pcu_b`. Its edges are

    a --i--> b --j--> d,
    a --j--> c --i--> d.

The lower local datum uses the incoming edge `a --i--> b` and its
prescribed outgoing `i` edge. The cup is its original inverse-defined
`cupL`; the row test is its original `capD n`.
`distinctCupRowLinear` closes an endomorphism of `E_i(a,b) E_j(b,d)`
with these maps, the left unitors, the associators and left whiskering
by `F_i(b,a)`.

Write `H=h_i(b)` and `D=d_ij`. The strict range `H>D` gives shifted
height `h_i(d)=H-D>0`. The lemma `distinctCupRow_leftDot` turns `p`
left `i` dots into `capD(p+n)`. The local inverse relation evaluates
this row to the Kronecker coefficient `H-1=p+n`.

A right `j`-dot monomial passes the given dotted cap with the factor

    (-1)^((n parity(i))(q parity(j))).

`distinctCupRow_monomial_zero` retains that interchange factor and
then vanishes when `p+n<H-1`.

The double crossing is ordered `cross(j,i); cross(i,j)`, so its
quadratic expansion is the actual `quadNe j i`. Its surviving second
leading term has `p=D` and coefficient `t_ij`. For `n<H-D`, the other
leading term and every interior term have `p<D` and vanish. Therefore
`distinctCupQuadraticRow_of_gt` evaluates the literal quadratic cup
row to

    t_ij · (if n=(h_i(d)-1).toNat then id(E_j) else 0).

Disconnected colours use `quadZero j i` and the prescribed equality
`t_ji=t_ij`. The calculation assumes no cup comparison or row test.
Its statement covers the strict branch `h_i(b)>d_ij`.

The paired consumer uses constructed rational two-odd probe families.
For connected Cartan entries `(-4,-4)`, the lower height is six and
the shifted height is two; both finite rows are tested in both colour
orders. The leading parameter is two and `s_ij^(2,2)=1`. The consumer
also tests odd right-dot interchange and the disconnected six-row
window with leading parameter two. Nonzero probe append vectors are
retained, and all owned declarations are audited against the standard
axiom allowlist.
