# Distinct-colour precomposition mate

**Status: proposed factor calculation with a checked conditional bicategorical
contraction (§6); the canonical factor pitchfork is still open.** This evaluates
only the pre/pre entry (A8)–(A9) of `SwappedActionAssembly.md`, conditional
on its specified full factor action. It supplies no new fused-action
hypothesis and changes none of the assigned generators. In particular it
uses the inherited reversed-label upward crossing, not its inverse.

The source inputs are Brundan–Ellis, *Super Kac–Moody 2-categories*,
arXiv:1701.04133v2, Definition 1.5 (1.11)–(1.12), Definition 2.2,
Proposition 6.2 (6.6), and Proposition 7.2 (7.5). The relevant library
calculation is `Cyclicity.rot_tau_left`, not the full crossing cyclicity
formula (1.28). The latter has a separate sign issue and is not needed.

## 1. Edge labels and endpoints

All scalar exponents below are in Z/2. Put i≠j, p=p_i, r=p_i p_j,
d=d_ij=-<h_i,alpha_j>, and k=<h_i,nu>. Set

    omega=nu-alpha_i+alpha_j,
    sigma=p(k+1),
    e(h)=1 if h<0, and (-1)^p if h>=0,
    c(h)=(-1)^(p(h+1)) e(h).

The four factor raising edges underlying (A8) are

| Edge | Colour | Factor bottom | Factor top |
|---|---|---|---|
| a | i | omega | nu+alpha_j |
| b | j | nu-alpha_i | omega |
| c | j | nu | nu+alpha_j |
| d | i | nu-alpha_i | nu |

Here edge letters a,b,c,d are labels, whereas the integer d in formulas
is d_ij. Write L_x=pre(E_x), K_x=pre(F_x). The bottom i-heights at the
two bent edges are k-2-d and k-2, respectively. The datum relation
p_i d_ij=0 in Z/2 gives

    sigma_a=p(k-1-d)=sigma_d=p(k-1)=sigma.               (1)

This uses the Cartan parity condition, not a restriction to even colours
or to disconnected pairs. The integral heights must still be kept distinct:
normalization signs can change when they cross zero.

Fix H:T_omega→W, with the reservoir component held fixed. Functor application
in this note is functional order; diagram boundary lists retain the
library's left-to-right order. The source and target of the Hom mate are

    Q=L_c R_a H,                 Q'=R_d L_b H,
    R_a=S_sigma K_a,             R_d=S_sigma K_d.

These are the execution words R_a L_c and L_b R_d of (A8), respectively.
The upward entry has functional type

    T:L_d L_c -> L_b L_a.

Its factor crossing has boundary [up j,up i]→[up i,up j]; this is the
reversed-label inherited crossing prescribed in (A9). In particular no
factor Q polynomial is inverted here.

Put Q0=L_c K_a H and Q0'=K_d L_b H, and use the homogeneous coordinates

    C=L_c(z_sigma(K_a H)):Q→Q0,
    D=z_sigma(K_d L_b H):Q'→Q0'.                         (2)

Each has degree sigma. Neither is being called even.

## 2. Substitution into the specified Hom adjunction

Let U_d be `leftCup` at the top nu of edge d; let V_a be `leftCap`
at the bottom omega of edge a. These are the raw inverse-defined maps
of `RouquierLeftCupCap.lean`, without the source's bubble scalars.
Let u_d be insertion of U_d and v_a insertion of c(k-2-d)^(-1)V_a.
The assigned even adjunction components are exactly

    eta_d(Z)=u_d(Z);z_sigma(K_d L_d Z)^(-1),
    eps_a(H)=(-1)^sigma L_a(z_sigma(K_a H));v_a(H).      (3)

Thus the functional-order expansion of (A8) is

    M_H=eta_d(Q);
        S_sigma K_d(T_(R_a H));
        S_sigma K_d L_b(eps_a(H)).                      (4)

The intermediate target after the crossing is
S_sigma K_d L_b L_a R_a H, so the last component is typed without
identifying the two different j-edges or the two i-edges.

Use S_sigma(f);z=(-1)^(sigma |f|)z;f. Removing the outer S in (4)
contributes sigma r, since eps_a is even. Moving C^(-1) past u_d
contributes sigma^2=sigma. Moving the remaining input z^(-1) past T
contributes sigma r; it then cancels the z in eps_a. The explicit
coefficient of eps_a contributes sigma. Consequently

    sigma r + sigma^2 + sigma r + sigma = 0,
    C^(-1);M_H;D = pre(Wbar)_H.                         (5)

Here Wbar is the following factor word, with the displayed boundary
lists and rightmost region nu:

    [dn i,up j]
      -- U_d on the right --> [dn i,up j,up i,dn i]
      -- crossing j,i -->    [dn i,up i,up j,dn i]
      -- c(k-2-d)^(-1)V_a on the left --> [up j,dn i].  (6)

Precomposition preserves chronological vertical composition. The reversal
is horizontal, and has already been accounted for in the j,i crossing.
There is no same-colour coefficient -(-1)^p in (6).

## 3. Comparison with the source's normalized left maps

The source maps eta'_i and eps'_i are not U and V. This distinction
accounts for a parameter and a height-window sign in the answer.
Define the involutive unit

    g(h)=1 if h>0, and (-1)^(p(h+1)) if h<=0,
    f(h)=1 if h<0, and (-1)^(p h) if h>=0.              (7)

For a region rho of height h write B_rho for the source bubble scalar
c_{rho;i}; B is unrelated to the postcomposition sector label. Direct
comparison of `MoreGenerators.etaP`, `MoreGenerators.epsP` with
`SuperRouquierLoc.cupL`, `capL` gives

    eta'_i(rho)=g(h) B_rho U_rho,
    eps'_i(rho)=f(h) B_rho^(-1) V_rho.                 (8)

These formulas include the minus in the nonnegative definition of capL.
For an i-edge of bottom height h, the elementary identity

    c(h) f(h) g(h+2)=1                                (9)

holds separately for h<=-2, h=-1, and h>=0. Thus its normalized raw cap
has the particularly useful expression

    c(h)^(-1)V_rho=g(h+2) B_rho eps'_i(rho).           (10)

No existence assumption on bubble scalars on the original weight group
is needed. For this calculation pull the already given factor action back
to the formal-content cover: use labels (rho,n) with n in the free abelian
group on the finite colour set, roots (alpha_l,e_l), and heights read from
rho. For each colour a set B^a_(rho,n)=product_l t_al^(n_l), and write B=B^i
in this calculation. Use nu~=(nu,n) and
omega~=(omega,n-e_i+e_j). The B^a are units and satisfy the
source scalar shift rule, since t_aa=1. This is a relabeling of the same
factor maps for the proof, not a quotient of X, a new action premise, or
a change to (3). Absent content components remain zero. The resulting
identity is independent of B and hence is an identity on the original
content-indexed factor maps. In particular

    B_omega/B_nu=t_ij.                                (11)

Let W' be the word (6) with eta'_i(nu) and eps'_i(omega) instead of
U_d and the normalized raw cap. Equations (8)–(11) imply

    Wbar=t_ij g(k-d) g(k)^(-1) W'.                     (12)

This keeps the cup height k and cap height k-2-d, rather than assigning
the same central height to both. The auxiliary B values cancel completely.

## 4. Derived mixed relation and the inverse

Let ell_ij(nu) be the factor `lcrossL i j`, with boundary
[dn i,up j]→[up j,dn i], and let s_ij(nu) be `sigmaL i j` in the
opposite direction. The all-weight cap pitchfork and the F triangle give

    W'=(-1)^(r sigma) ell_ij(nu).                      (13)

Precisely, apply `Cyclicity.rot_tau_left` with its arguments (j,i,nu).
Its proof first applies `PitchforkCap.eq_7_5_a` at nu-alpha_i to the
crossing–cap subword. Next exchange the remaining left crossing past the
cup of degree sigma, contributing (-1)^(r sigma), and finish with
`cup_cap_F_left`, whose F snake is one. This derives (13) from the factor
relations, rather than assuming that arbitrary partial mates preserve
isomorphisms. The parity invariance used there is
`PitchforkCap.ipar_wt_upj`, exactly (1).

Combining (5), (12), (13), define the even scalar unit

    delta_ij(k)=t_ij (-1)^(p_i p_j sigma) g(k-d_ij)/g(k).

The promised coordinate formula and inverse are

    C^(-1);M_H;D = delta_ij(k) pre(ell_ij(nu))_H,
    M_H = delta_ij(k) C;pre(ell_ij(nu))_H;D^(-1),
    N_H = delta_ij(k)^(-1) D;pre(s_ij(nu))_H;C^(-1).   (14)

The source relations `Presentation.invNe₁` and `invNe₂` in the **factor**
give s;ell=1 and ell;s=1, with no same-colour minus. Adjacent coordinate
cancellation in (14) therefore gives both

    M_H;N_H=1_Q,          N_H;M_H=1_Q'.                (15)

There is no exchange of two odd maps in these products. The scalar
inverse is t_ij^(-1) times the same sign, not delta itself unless the
parameter happens to square to one. Each map in (14) has parity r,
because the two endpoint coordinates contribute 2 sigma.

For clarity the height-window part of the coefficient is

    g(k-d)/g(k) = (-1)^sigma if 0<k<=d, and 1 otherwise. (16)

Indeed d>=0 and p d=0; if both arguments are nonpositive their signs
agree. Formula (16) includes d=0 and both boundaries k=0,d without an
unstated continuation from a positive or negative range. If i is even,
delta=t_ij. If i is odd and j is even, the only sign is the window sign.
If both are odd, multiply that window sign by (-1)^(k+1).

## 5. Scope

This is a written evaluation and two-sided inverse of the single prescribed
pre/pre partial mate (A9), for both parities and every permitted height,
using the existing full factor-action input. The new calculation is not
kernel-checked in its entirety. The cited presented-calculus pitchfork,
rotation, and factor inverse relations have library declarations. The
bicategorical contraction in §6 is checked with its pitchfork hypothesis
explicit.

The pre/post and post/pre entries of (A8), full swapped presentation action,
normalized vacuum bubbles, and bounded detecting consumer are not proved
here. No whole-matrix, post/post, or nondegeneracy conclusion is asserted.

## 6. Bicategorical contraction and the remaining canonical pitchfork

`OddMath.SKM.leftCrossMate_eq_of_cap_pitchfork` is the bicategorical
form of the last contraction in §4, in
`OddMath/SKM/RouquierDistinctLeftRotation.lean`. Write `A_d`, `A_a` for
the prescribed shifted left adjunctions, `U_d=A_d.unit`, and
`V_d=A_d.counit`, `V_a=A_a.counit` for their normalized caps. For any
degree-r map `ell:E_c F_a→F_d E_b`, the explicit hypothesis is

    a(E_d,E_c,F_a)^(-1);(T▷F_a);a(E_b,E_a,F_a);
      (E_b◁V_a);rho(E_b)
      = q (E_d◁ell);a(E_d,F_d,E_b)^(-1);
          (V_d▷E_b);lambda(E_b).                     (17)

The theorem gives

    leftCrossMate(A_d,A_a,T)=q (-1)^(sigma_d r) ell.   (18)

Its proof uses `ShiftedSuperAdjunction.unit_slide` and
`left_triangle_whiskerRight`. Thus the Koszul factor and the entire
cup–crossing–cap word are retained. The companion
`leftCrossMate_inv_products_of_cap_pitchfork` proves both inverse
products with `q^(-1) (-1)^(sigma_d r) s` when `q` is a unit and `s`
is a two-sided inverse of `ell`.
`leftCrossMate_isIso_of_cap_pitchfork` packages these products.

To obtain `LeftMateInvertible T T.leftAdjoints` for the probe family,
(17) must still be derived for the following exact choices:

* `T` in the mate is the inherited reversed-label upward crossing
  `family.cross j i h₁ h₂ h₃ h₄`;
* `A_d=family.leftAdjoints.adjL i h₁` and
  `A_a=family.leftAdjoints.adjL i h₄`;
* `s=crossMate (family.adj i h₁) (family.adj i h₄)
  (family.cross i j h₃ h₄ h₁ h₂)` and `ell=inv s`;
* `q=t_ij g(k-d_ij)/g(k)`, with the two separate top heights
  `k=h_i(b)` and `k-d_ij=h_i(d)` of these edges.

The existing multicolour `invNe` field supplies the inverse relations for
these exact `s` and `ell`; it does not supply (17). In particular the
checked `Cyclicity.rot_tau_left` has codomain `pres D Sc`, whereas the
probe family has codomain `PiSCat k`. No interpretation from an arbitrary
`RouquierFamily` and `RouquierMulticolour` into the presented calculus has
yet been constructed. Therefore applying that source theorem to the
probe is not a completed Lean argument.

The direct cited route to (17) ports Lemma 7.1's cap pitchfork tests:
`ext_FEE` for the nonpositive range, the mixed-braid correction identity
used by `pf_a`, and the dotted quadratic calculation used by `pf_b`.
The intermediate positive window uses `eq_7_3`; the complementary range
is obtained by the cup relation and the two triangles as in
`PitchforkCap.eq_7_5_a`. These inputs must retain the inverse-defined
maps and the height-dependent normalization of §3. They are the
remaining canonical factor obligation, not new hypotheses of the
intended probe conclusion.

The two-mate expansion needed for the correction identity is checked as
`crossMate_comp_crossMate` in `RouquierRectangularComposition.lean`.
For adjunctions `E₁⊣F₁`, `E₂⊣F₂`, `E₃⊣F₃` at six independent objects
and crossings `t₁₂:G₁₂ E₂→E₁ H₁₂`,
`t₂₃:G₂₃ E₃→E₂ H₂₃` of degrees `p,q`, it identifies the composite
of their two prescribed right mates with `(-1)^(pq)` times the
rectangular outer mate of `(G₁₂◁t₂₃);(t₁₂▷H₂₃)`, retaining all
associators. `rectangularMateLinearMap` transports the correction sums
linearly. This removes the same-colour restriction of
`rouquierMate_comp_mate`; it does not evaluate the resulting terms
against the canonical left caps.
