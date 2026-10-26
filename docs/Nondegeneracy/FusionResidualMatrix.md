# Signed-height residual matrix for separated fusion

## Status and conventions

This is a proposed written reduction, not a Lean theorem or a proof of fused
inversion. It gives an exact categorical residual matrix, a symbolic
partial-fraction matrix with an all-height inversion proof, and the precise
comparison still missing between them. In particular the latter matrix is
**not** asserted to be the residual of the proposed action.

Composition is right to left. Fix a colour of parity `p`, put `q=(-1)^p`,
and let `h_A+h_B=N≥0`. Use

```
P = {(a,s) : a∈{A,B}, 0≤s<h_a},
M = {(a,m) : a∈{A,B}, 0≤m<−h_a},
F = {0,…,N−1}.
```

Thus `|P|=N+|M|`, including when N is zero. These are the source-row and
target-column indices of the even reference's `schurPos`. Below ordinary
block displays instead have target rows and source columns. No transpose
of a matrix over a noncommutative ring is used as an algebra operation.

The source conventions are `SuperRouquierLoc` in `RouquierData.lean`,
`capD`, `cupD`, `cupN`, `capN` in `RouquierLeftCupCap.lean`, and the inverse
identities in `RouquierInverseRelations.lean`. In those files the source
of `sig` is `F₁E₁` and its target is `E₂F₂`; denote these objects by X and Y
rather than changing their names according to diagram-reading convention.
The mate and its principal inverse have parity p, not necessarily zero.

## 1. Shifted objects and finite windows

Write `c_a(s)=capD s`, `u_a(m)=cupD m`, `a_a(s)=cupN s`,
`b_a(m)=capN m`, and `r_a=−sigL`. These are the inverse components of the
literal mate. Normalize the mate by `−q` only if its inverse and cup/cap
coordinate identifications are transported at the same time.

For an integer degree/parity pair `(d,e)`, use the convention

```
Hom⁰(Z[d,e],W[d',e']) = Hom^(d−d',e−e')(Z,W).
```

Let `(δ_a,ε_a)` record the shift of the sector X_a inside the fused source.
With `d_i=d`, the factor augmented map is even of degree zero on the objects

```
X_a[δ_a,ε_a],                 Y_a[δ_a,ε_a+p],
P_(a,s) = 1[δ_a−d(1−h_a+2s), ε_a+sp],
M_(a,m) = 1[δ_a+d(1+h_a+2m), ε_a+(m+1)p].
```

Indeed the underlying degrees of cap and cup are `d(1−h_a+2s)` and
`d(1+h_a+2m)`, their parities are sp and mp, and sig has degree zero and
parity p. These degrees are `gsum_epsL`, `gsum_etaL`, `gsum_sigmaL` in
`Grading.lean`; the parities are `capD_mem`, `cupD_mem` and the defining
`SuperRouquierLoc` fields. The inverse components carry the opposite degrees
and the required parities. At total height N the fused cap summand is
`F_t=1[−d(1−N+2t),tp]` after fixing the fused source normalization.

The numbers `(δ_a,ε_a)` must come from the actual tensor/Hom action and its
lowering-functor shifts. They are not freely adjustable parameters of a
proof. In particular substituting the factor cap for a fused cap component
without its shift transport is not a homogeneous equality in general.
The probe with invertible odd dots need not retain an integer grading;
then retain the parity shifts and interpret the degree table as the
required grading of a homogeneous precursor, not as an extra property of
the specialized probe.

On these shifted objects put X=⊕X_a, Y=⊕Y_a. Let v:X→P collect precisely
the positive low caps, u:M→Y precisely the negative low cups, a:P→X the
positive inverse cups, b:Y→M the negative inverse caps, and r:Y→X the
principal inverse. Factor inversion gives

```
Φ = [ σ  u ] : X⊕M → Y⊕P,     Φ⁻¹ = [ r  a ].
    [ v  0 ]                         [ b  0 ]
```

In particular `σr+ub=1`, `σa=0`, `vr=0`, `va=1`, `bu=1`, `bσ=0`,
and `rσ+av=1`.
All these are statements in the shifted even category. They do not say
that σ or r is invertible.

## 2. Exact elimination, before a scalar comparison

Suppose the off-sector summands have been eliminated by their specified
isomorphisms, and let the resulting central fused map be

```
R = [σ+K; w] : X → Y⊕F.
```

Here K is the ordered cross-sector mate contribution and w is the actual
fused cap window, including both sector components and their transports.
This supposition is the still-required cross-support comparison of
`NondegeneracyProof.md` §5.4, not a consequence of the following algebra.
Stabilizing with M and precomposing by Φ⁻¹ gives exactly

```
[ σ+K  u ] [ r  a ]   [ 1+Kr  Ka ]
[  w   0 ] [ b  0 ] = [  wr   wa ].
[  0   1 ]           [   b    0  ]
```

Set `A₀=1+Kr : Y→Y`. If A₀ is invertible, ordinary Gaussian elimination
in this even additive category leaves the **exact residual**

```
S = [ wa − wr A₀⁻¹ Ka ] : P → F⊕M.                 (R)
    [     −b A₀⁻¹ Ka ]
```

This proves that R is invertible if and only if S is invertible, under the
stated A₀ hypothesis: stabilization adds an identity on M, Φ is an
isomorphism, and the two elimination matrices are triangular with identity
diagonal. It uses no determinant or ordinary commutativity of super scalars.
It also fixes the minus sign in the negative-window columns.

The source-row entries are explicitly

```
S_(a,s),t     = w_t a_a(s) − w_t r A₀⁻¹ K a_a(s),
S_(a,s),(e,m) = −b_e(m) A₀⁻¹ K a_a(s).
```

This is a typed all-finite-height formula with either factor height sign.
Its entries are composites between the shifts in §1, not unspecified
entries of an ordinary scalar matrix. Joint nilpotence of reservoir
closures is relevant to A₀ and to the correction terms but has not yet
identified all the terms in (R) with a nilpotent ideal.

For clarity, the ordered normalized mate expansions of
`NondegeneracyProof.md` §5.2 would give

```
K_AB = Σ_(r≥0) q^r u_A(r)c_B(−r−1),
K_BA = −Σ_(r≥0) q^(r+1) u_B(−r−1)c_A(r).
```

Negative powers refer only to the invertible probe dot. Once all factor
maps have been transported to this normalization, the zeroth term of
`−b(1+Kr)⁻¹Ka` is therefore

```
A positive, B negative:
  Σ_r q^(r+1) b_B(m)u_B(−r−1)c_A(r)a_A(s),
B positive, A negative:
 −Σ_r q^r b_A(m)u_A(r)c_B(−r−1)a_B(s).              (L)
```

The low reservoir windows give Kronecker coefficients exactly. Outside
the window, `c_A(r)a_A(s)` has degree `2d(r−s)` and
`b_A(m)u_A(r)` has degree `2d(r−m)`. Thus, modulo a justified ideal of
positive-degree reservoir identity maps, (L) has respective leading terms

```
q^(s+1) b_B(m)u_B(−s−1),
−q^m c_B(−m−1)a_B(s).                              (L₀)
```

This computation does not discard the remaining terms of (R), prove that
that ideal controls them, or normalize the probe inverse-window entries.
The fused-window leading entries remain the specified composites `w_t a_a(s)`.
These are exactly where an assertion that the answer is an identity matrix
would omit substantive mathematics.

## 3. A symbolically invertible parity-block comparison matrix

Ordinary partial fractions in the **squared** variable suffice for a
candidate comparison, provided the two parity blocks are retained. This
section proves that algebraic assertion, not its identification with (R).
Work over a field k with c≠0. For an odd colour restrict the probe height to
`h_B=2b` with b integral. This is the permitted even-cutoff probe slice:
odd-colour Cartan pairings with roots are even, so an even highest cutoff
keeps the probe height even at every content, including negative heights.
An arbitrary odd probe height is not supplied by these factors.

Use one polynomial variable z, with parity one, and T=z². This is the
ordinary associative polynomial module with its parity grading, **not** a
supercommutative polynomial algebra on an odd generator. Define positive
jet spaces, retaining only factors of positive height,

```
J_A = k[z]/(z^(h_A))                     if h_A>0,
J_B = k[z]/((z²−c)^b)                    if b>0.
```

Their bases are `z^s`, and `z^ε(T−c)^j` with ε∈{0,1} respectively.
Take domain the direct sum of polynomials of degree <N and, at factors of
negative height, the proper fractions

```
z^(−m−1)                         (0≤m<−h_A),
z^ε/(T−c)^(j+1)                  (ε∈{0,1}, 0≤j<−b).
```

Reduce each rational function in each positive jet space; its denominators
are units there. This defines a matrix H with source rows the positive jets
and target columns the polynomial/fraction coordinates, as in `crtMatrix`.
Here are **all** its entries (absent sign configurations give absent blocks):

* A row s, polynomial column t: `δ_(s,t)`.
* B row (ε,j), polynomial column t: zero unless `t≡ε (mod 2)`;
  otherwise `binom((t−ε)/2,j)c^((t−ε)/2−j)`, interpreted as zero when
  j exceeds the nonnegative upper index.
* A row s, B fraction column (ε,l): zero unless `s≥ε` and `s≡ε (mod 2)`;
  with `v=(s−ε)/2`, the entry is
  `(-1)^(l+1) binom(l+v,v)c^(−l−1−v)`.
* B row (ε,j), A fraction column m: choose the unique ε∈{0,1} and integer
  k with `−m−1=2k+ε`. The entry in that parity block is
  `binom(k,j)c^(k−j)` and in the other block is zero. For negative k this
  means the integral coefficient
  `binom(k,j)=(-1)^j binom(j−k−1,j)`, mapped into the field.

These formulas follow by expanding powers of `c+(T−c)` or of `−c+T`.
They use integral binomial coefficients and remain valid in positive
characteristic; division by factorials is not assumed. In particular no
choice of a square root of c and no separation of +√c from −√c is needed.
The negative A column has parity `(m+1)p`, precisely the extra p in M in
§1, rather than mp. Probe fraction columns have parity ε. The polynomial
columns have parity tp. Thus H is parity-preserving before any further
sector parity transport. There is no parity-rank mismatch at odd h_A.

### Symbolic inversion proof

Let P₊ be the product of the positive factors `z^(h_A⁺)` and
`(z²−c)^(b⁺)`, and P₋ the product of the corresponding negative factors.
They are coprime since c≠0 and the same factor cannot have both signs.
Their degrees satisfy `deg P₊=N+deg P₋`.

If a rational function f in the displayed domain maps to zero, then
`g=P₋f` is a polynomial of degree strictly less than deg P₊. Vanishing in
each positive jet space implies P₊ divides g, since P₋ is a unit there.
Hence g=0, so f=0. Polynomial division and the coprime-factor partial
fraction decomposition show that the displayed polynomial and fraction
coordinates of f are all zero. This proves injectivity. The two spaces
have equal finite dimensions, hence H is invertible. Alternatively, for
prescribed jets solve `g ≡ P₋·jet (mod P₊)` uniquely with degree below
`deg P₊`, then divide `g/P₋` into its polynomial and proper-fraction parts.
This is an explicit symbolic inverse algorithm for every finite height,
including N=0 and either sign of h_A or b. No matrices were numerically
inverted or enumerated.

For an even colour replace `z²−c` by `z−c` and omit ε. The same proof
recovers the two-point signed-height partial-fraction argument of
`CoproductCRT.lean`. For odd colours an invertible probe dot with completely
unspecified spectrum does not imply this single-c model: passage to its
spectral primary blocks, or an appropriate polynomial version, must be
proved for the chosen factor. The suggested probe `(z²−1)^M` supplies the
intended primary coordinate, not the categorical comparison below.

## 4. The remaining identity, not a new assumption solving fusion

To use §3 one must prove, for the intended factor actions, the following
specific comparison. Choose the sector shift transports of §1, an explicitly
nilpotent ideal J of the finite shifted identity-endomorphism matrix algebra,
and explicit even invertible coordinate changes L and Q obtained from the
factor inverse windows and the probe dot. Then prove

```
S mod J = L · H_res · Q,                             (C)
```

Here H_res sends a positive-jet basis vector to the linear combination of
polynomial/fraction basis vectors with the coefficients in its row of §3.
Its ordinary target-row matrix is the transpose of the rational-to-jet
matrix H; this transpose is taken only over the purely even commutative
field k, so invertibility follows from §3. It is not a transpose operation
on the categorical super coefficient algebra. S is literally (R), and the
leading negative-window entries must be literally (L₀). Equation (C) uses
ordinary target-row matrices; in source-row notation ordered factors reverse. Neither arbitrary choices of L,Q nor
assuming their existence constitutes a solution: their entries must be
computed from the given cups, caps, dot powers, and inverse components.

The unresolved checks are concrete:

1. Derive the sector restrictions w_t, including `(δ_a,ε_a)`, of the
   **fused** right adjunction; match their composites with a_a(s) to the
   polynomial columns of H.
2. Identify the dot-conjugated probe inverse-window composites in (L₀)
   with the fraction columns of H, including the factors `q^(s+1)` and
   `−q^m` and any reindexing of paired probe coordinates.
3. Prove that all remaining terms in (R), and the principal-block
   elimination, are controlled by the same nilpotent reservoir ideal.
   Positive degrees of isolated reservoir closures do not establish this
   for an uncomputed Schur expression.

These are stronger than the already checked low-window Kronecker
relations. No theorem currently cited computes the fused cap restriction
or the necessary high and inverse probe windows. Thus the precise
obstruction is (C), with these source-derived coordinate changes and ideal,
not symbolic inversion of the parity-block partial-fraction matrix.
A proof of (C) would permit a finite geometric-series lift in the even
shifted endomorphism algebra. Until then A2-b remains open. Negative total
height requires its own super-opposite comparison and is not inferred by
mirroring the signs above.
