# Finite columns of the distinct cap word

`SKM/RouquierDistinctCapColumns` evaluates the upper dotted-cup,
double-crossing and inverse-defined cap word in Brundan–Ellis
Lemma 7.1, `pfL_b`. The edges are

    a --i--> b --j--> d,
    a --j--> c --i--> d.

The local upper cap is the prescribed `capL` at `c`, with its original
predecessor edge. The map `distinctCapColumnLinear` closes an
endomorphism of `E_j(a,c) E_i(c,d)` using the actual upper dotted cup,
associators, upper cap and right unitors. It is linear without changing
any of these maps.

For negative lower height write `N = -h_i(a)` and `D = d_ij`.
The upper height is `h_i(c) = h_i(a)-D`, so the upper inverse cap has
width `N+D`. Right dots of exponent `p` turn the given cup exponent
`n` into `n+p`. Thus `distinctCapColumn_rightDot` evaluates the raw
upper cup-cap to the Kronecker coefficient at `N+D-1`.

`distinctCapColumn_monomial_zero` also retains the middle strand's
endomorphism. Moving its `q` dots through the given dotted cup uses the
homogeneous interchange factor

    (-1)^((q parity(j))(n parity(i))).

The remaining right-dot cap coefficient vanishes when
`n+p < N+D-1`; the sign is retained until this zero is established.

`distinctCapQuadraticColumn_of_neg` applies the actual `quadNe`
relation to the upward double crossing. For `n<N`, every interior
term has `p<D` and vanishes. The other leading term has `p=0` and
also vanishes when the colours are connected. The leading `i`-dot
term has `p=D` and contributes exactly

    t_ij · (if n=N-1 then id(E_j) else 0).

For disconnected colours the same formula follows directly from
`quadZero`; the upper and lower cap widths coincide. No scalar,
cap comparison, or column equality is assumed.

The paired consumer uses constructed rational two-odd probe families
for connected Cartan entries `(-4,-4)` and disconnected entries `(0,0)`.
Both have leading parameter `2`. The connected family has the nonzero
interior coefficient `s_ij^(2,2)=1`. It checks every column of the
negative-height window, right-dot addition, even and odd middle-dot
vanishing, and nonzero probe append vectors in both colours. All
owned declarations are audited against the standard axiom allowlist.
