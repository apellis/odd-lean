# The content-shifted probe matrix

**Status: principal equality (B), natural-power dotted identities (9), and
whole augmented inverses (10)–(13) proved in Lean, including supernatural
transformation packaging in SCat. Negative powers and a full Hom Rouquier
family remain separate.** `RouquierHomPostSuperInverse.lean` lifts all five
products in each height regime, proves zero-height agreement and retains
literal parity shifts in the even natural components. `RouquierHomPostInverse.lean`
supplies both height regimes, all five products, the literal parity-shifted
summands and zero-height overlap. `homContentPostCup_coordinates` and
`homContentPostCap_coordinates` in `RouquierHomPostPowers.lean` supply every
natural-power dotted entry, without requiring the factor dot to be invertible. The principal theorem is
`homContentPostCrossing_principal` in `RouquierHomPostPrincipal.lean`. This computes the
probe-sector input (B) of `HomCentralFeedback.md`, independently of its
central-feedback argument. The conclusion is conditional on the probe factor's
specified local augmented inverse, not on an inverse for the shifted sector.
No bare mixed crossing is assumed invertible at nonzero height.

## 1. The prescribed crossing and dots

Use execution order `f;g`, functional order for functors, and suppress only
even reassociations. Fix reservoir content beta throughout the BB word, put
`p=p(i)`, `kappa=p contentParity(beta)`, `S=S_kappa`, and write

```
M=homPost(E_B), N=homPost(F_B), L=S M, R=N S,
u:Id -> NM, v:MN -> Id, d:M -> M, t:MM -> MM.
```

Here u,v are the even postcomposition adjunction maps, while d,t have
parity p. Adjacent edges of M,N carry their own probe weights; they are not
endomorphisms of one weight sector. The notation below suppresses these
edge subscripts, never their order. S has the same kappa on all of them.

The same-sector prescription in `NondegeneracyProof.md` §5.3 is the factor
crossing transported by the Koszul tensor comparison. In the pinned
Pi-supercategory convention its word-removal comparison is

```
Theta_H = S(beta_M(MH)^-1);xi_kappa(MMH)
        = S M(z_kappa(MH));z_kappa(MMH) : LLH -> MMH,
T_H = Theta_H;t_H;Theta_H^-1,             delta_H=S(d_H).       (1)
```

Indeed `beta_M(X)^-1=M(z_kappa X);z_kappa(MX)^-1` and
`xi_kappa(Y)=S(z_kappa Y);z_kappa Y`; the middle inverse pair cancels.
Thus (1) is the expansion of that prescribed coherent transport, not a
choice of crossing made to obtain a desired mate. This uses precisely
`homParityShiftCommute` and `homParityShiftAdd` in
`RouquierHomContentCoherence.lean`, with `PiSupercategory.β` written as
beta here. The underlying source is Brundan--Ellis, *Monoidal
supercategories*, Corollary 3.3, as implemented in `Super/Pi.lean`.
There is not yet a Lean definition of a complete fused crossing/action.

For clarity, this convention also transports both prescribed dots:

```
L(delta_H);Theta_H = Theta_H;M(d_H),
delta_(LH);Theta_H = Theta_H;d_(MH).                       (2)
```

Each equality has two exchanges of parities kappa and p, hence coefficient
`(-1)^(2 kappa p)=1`. The first uses supernaturality of z after functoriality;
the second additionally uses supernaturality of d against `z_kappa(MH)`.
Consequently the factor nilHecke slides transport without a scalar change.
Multiplying t alone by a sign would change their identity term and is not
part of (1). Neither a dot gauge nor an adjunction gauge is being introduced.

## 2. Coordinates and the unit--map--cap calculation

Put `e=(-1)^kappa` and introduce the parity-kappa maps

```
l_H=z_kappa(MH):LH -> MH,
r_H=N(z_kappa H):RH -> NH.
```

For a homogeneous f of parity a they obey
`L(f);l=(-1)^(kappa a) l;M(f)` and
`R(f);r=(-1)^(kappa a) r;N(f)`. Define the even maps

```
a_H=e l_(RH);M(r_H)
   =e z_kappa(MNSH);MN(z_kappa H):LRH -> MNH,
b_H=e r_(LH);N(l_H)=N(xi_kappa(MH)):RLH -> NMH.           (3)
```

These are exactly B_s and B_t, not the unsigned pair of z removals.
Also `Theta_H=e l_(LH);M(l_H)`, by one kappa-by-kappa exchange.
The specified `homContentPostAdjunction` has components

```
eta_H=u_H;b_H^-1,
eps_H=a_H;v_H=S(v_(SH));xi_kappa(H).                    (4)
```

These are the formulas of `HomSectorTransport.md` §3. In particular
eta and eps are even. The literal partial mate of (1), with its full
unit--map--cap order, is

```
P(T)_H = eta_(LRH);R(T_(RH));RL(eps_H):LRH -> RLH.      (5)
```

This is `rouquierMate` after the even functor reassociations, not a
uniqueness-of-adjoints argument. To evaluate (5), retain the following
explicit even intermediate comparison:

```
W_H=R(Theta_(RH));r_(MMRH);NMM(r_H):RLLRH -> NMMNH.
```

Expanding Theta and moving r past the two l maps gives two factors e.
Keeping the e already in Theta, one obtains

```
W_H=e r_(LLRH);N(l_(LRH));NM(l_(RH));NMM(r_H)
   =e b_(LRH);NM(a_H).                                (6)
```

Both occurrences of e in (3) are essential in the last equality. Now
naturality of the **even** u and b, and (4), give the endpoint equations

```
a_H^-1;eta_(LRH);W_H = e u_(MNH),
W_H^-1;RL(eps_H);b_H = e NM(v_H).                      (7)
```

For example the first is
`a^-1;u_(LRH);b_(LRH)^-1;e b_(LRH);NM(a)=e u_(MNH)`.
For the second, (6) gives
`W;NM(v)=e b_(LRH);NM(eps)=e RL(eps);b`.
No homogeneous object parity is used in either calculation.

The crossing step is

```
R(T_(RH));W_H = W_H;N(t_(NH)).                         (8)
```

After cancelling Theta, its two sign-bearing exchanges are exactly

```
R(t_(RH));r_(MMRH) = (-1)^(kappa p) r_(MMRH);N(t_(RH)),
t_(RH);MM(r_H) = (-1)^(kappa p) MM(r_H);t_(NH).
```

Their coefficients multiply to one. Equations (7)--(8) prove

```
a_H^-1;P(T)_H;b_H
 = e^2 [u_(MNH);N(t_(NH));NM(v_H)]
 = post(sigma_B)_H.                                   (B)
```

The last bracket is the raw probe's literal `rouquierMate` word.
Postcomposition preserves that word, including its even associators.
The total exponent is `kappa+kappa+2 kappa p=0` modulo two. There is
no surviving scalar, content twist, or exceptional zero-height sign.
In particular this establishes (B) for both colour parities and both
reservoir content parities, without using any central-mate formula.

## 3. Every dotted component, including negative probe powers

For an integer n when d is invertible, and for n>=0 otherwise, put

```
u_n=u;N(d^n),  v_n(H)=d_(NH)^n;v_H.
```

The sector cup and cap use delta in (1), not a transposed dot:

```
cup(n)=eta;R(delta^n),  cap(n)=delta_(R-)^n;eps.
cup(n);b=u_n,          cap(n)=a;v_n.                   (9)
```

For the cup use naturality of xi against `d^n`, of parity np.
For the cap use
`cap(n)=S(v_n(S-));xi`; moving the two z removals through v_n gives
`(-1)^(kappa np)` twice, leaving just the e already in a. Thus (9)
holds for every displayed integer n. For n<0, `delta^n=S(d^n)` follows
from preservation of inverse identities. The parity of `d^-1` is p,
so the same proof applies. No formula for the right transpose of d is
used; in particular no `(-1)^(p n(n-1)/2)` factor occurs.

These negative powers are precisely those needed in the central series
`v_(-r-1)` and `u_(-s-1)`. They are not additional negative-index columns
in the finite augmented matrix.

## 4. Transport of the whole augmented inverse

Fix the probe height h. Write `s=post(sigma_B)`, and `j=post(R_B)` for
the principal entry of the **factor's specified augmented inverse**.
The remaining entries are denoted A_n or D_n below. They are not new
choices: use `SuperRouquierLoc.invPos`/`invNeg`, respectively, after
postcomposition. Their five inverse identities are those of
`SuperSumInvTo` and `SuperSumInvFrom` in `RouquierData.lean`.

All displays in this section use target-row/source-column matrices;
individual components still use execution order. They are parity-indexed
matrices until the explicit even lifts below are applied.

For h>0 the raw factor matrix and inverse are

```
F_+=[s; (v_n)_(n<h)] : MN -> NM + (Id)^(h),
G_+=[j, (A_n)_(n<h)] : NM + (Id)^(h) -> MN.
```

Let `Csrc=a` and `Ctgt=diag(b,1,...,1)` at these unbundled coordinates.
Equations (B),(9) identify the specified sector matrix and its inverse:

```
F_+^Hom = Ctgt^-1 F_+ Csrc,
G_+^Hom = Csrc^-1 G_+ Ctgt,
I_B=b;j;a^-1,                  A_n^Hom=A_n;a^-1.        (10)
```

For h<0 put m=-h. The matrices instead are

```
F_-=[s, (u_n)_(n<m)] : MN + (Id)^m -> NM,
G_-=[j; (D_n)_(n<m)] : NM -> MN + (Id)^m.
```

Now `Csrc=diag(a,1,...,1)`, `Ctgt=b`, and the same conjugation formulas give

```
I_B=b;j;a^-1,                  D_n^Hom=b;D_n.           (11)
```

All entries are transported, not only the principal entry. Multiplying in
either order cancels Csrc/Ctgt and gives the corresponding identity from
`G_+ F_+=1`, `F_+ G_+=1`, or the two negative-height identities. At h=0
both windows are empty, so (B) alone gives `P(T)^-1=b;j;a^-1` with scalar
one; the two factor inverse presentations agree by the two inverse laws.

Here is the promised identity-summand interpretation, which prevents the
unbundled `1` coordinates from being mistaken for unsigned module maps.
Let `z_t(Z):S_t Z->Z` be the same homogeneous comparison as above.
For h>0 the **even** factor matrix has source MNH and target

```
S_p(NMH) + direct_sum_(n<h) S_(np) H.
```

Its entries are `s_H;z_p(NMH)^-1` and `v_n(H);z_(np)(H)^-1`.
The inverse entries are `z_p(NMH);j_H` and `z_(np)(H);A_n(H)`.
The even sector target replaces NMH by RLH, with principal coordinate
`S_p(b_H)` and literal identity on each same object `S_(np) H`.
Its entries and inverse entries are explicitly

```
P(T)_H;z_p(RLH)^-1,      cap(n)_H;z_(np)(H)^-1;
z_p(RLH);b_H;j_H;a_H^-1, z_(np)(H);A_n(H);a_H^-1.     (12)
```

For h<0 the **even** factor matrix has source
`S_p(MNH)+direct_sum_(n<m) S_(np) H` and target NMH.
Its entries are `z_p(MNH);s_H` and `z_(np)(H);u_n(H)`;
its inverse entries are `j_H;z_p(MNH)^-1` and
`D_n(H);z_(np)(H)^-1`. The sector source uses `S_p(LRH)` with
coordinate `S_p(a_H)`. Its entries and inverse entries are

```
z_p(LRH);P(T)_H,       z_(np)(H);cup(n)_H;
b_H;j_H;a_H^-1;z_p(LRH)^-1, b_H;D_n(H);z_(np)(H)^-1. (13)
```

Naturality of z against the even a,b verifies these even matrix
comparisons without signs. In the two products each z is adjacent to
its own inverse; one never replaces two z removals by an unsigned xi.
These are parity-completed identity functors and their actual maps.
No integer grading on the localized probe or on the fused action is
assumed; this is exactly the parity-indexed local-inversion interface.

## 5. Scope of the result

The probe augmented isomorphism is therefore supplied by the probe
factor's local inverse data and the prescribed coherent crossing (1).
In the notation of `HomCentralFeedback.md` §3 its principal coordinate is

```
Rcal_B=B_t^-1;I_B;B_s=post(R_B).                        (14)
```

Thus no additional probe-sector augmented-inverse hypothesis is needed
beyond the factor-action/local-inverse input already stated. This result
does not prove the factor action itself. It also does not validate the
independent central-feedback nilpotence calculation: it supplies precisely
that calculation's probe input. Its central C/D convention discrepancy,
residual matrices, multicolour fusion, integer word shifts, and separation
are unchanged and remain separate questions. No full (TC) or
nondegeneracy conclusion is drawn here.
