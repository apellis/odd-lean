# The principal component of the reversed Hom matrix

**Status: written mathematical derivation, not a Lean theorem.** With the
inherited reservoir dots and the same-colour KLR crossing convention, the
normalized-left Hom mixed mate has raw component

```
D_H(H) = gamma(k) P_R(H),
gamma(k) = (-1)^(p k) if k != 0, and (-1)^p if k = 0,       (1)
R = -sigL.
```

The scalar is an even degree-zero involutive unit. This evaluates the
principal component left open in `ReversedReservoirMatrix.md`. The
whole-matrix consequence below uses the finite-window calculations of that
note explicitly; the principal calculation itself does not use them.
It does not evaluate the shifted swapping mates or prove the tensor-support
condition (TC) in `FusedFeedbackComparison.md`.

## 1. Conventions and the upward crossing

Use execution order `f;g`, the words and coordinates of
`ReversedReservoirMatrix.md` §§1–2, and canonical even associators and
unitors. Thus, at reservoir height k,

```
E_-:lambda-alpha_i -> lambda, E_+:lambda -> lambda+alpha_i,
F_-:lambda -> lambda-alpha_i, F_+:lambda+alpha_i -> lambda,
X=F_- E_-, Y=E_+ F_+,
p=p(i), s=(-1)^p, sigma=p(k+1),
U_k:1->X, V_k:Y->1,
c(k)=(-1)^sigma e(k), e(k)=1 (k<0), e(k)=s (k>=0).
```

The source Hom weight has height -k. Its raising functors retain E,
not its right transpose. The library provides `homContentPreE` and
`homContentPreAdjunction`, but does not bundle a same-colour upward Hom
crossing. Here is the explicit crossing required by the inherited-dot
horizontal-reversal convention; no new Lean identifier is asserted.

Let t be the factor crossing on `E_- E_+`, and put
`A=E_- whisker x_+`, `B=x_- whisker E_+`. The factor relations are

```
A;t - s t;B = 1,       t;A - s B;t = 1.                 (2)
```

Precomposition reverses the two functor slots, preserves vertical
composition, and sends the two slot dots to B and A, respectively.
Consequently the crossing in raw coordinates is

```
tau_H(H) = -s (t whisker H).                            (3)
```

Indeed `B;(-s t)-s(-s t);A=t;A-s B;t=1`, and
`(-s t);B-s A;(-s t)=A;t-s t;B=1`. This determines the
coefficient within the prescribed scalar multiple of the inherited
crossing; it is not a uniqueness claim for all solutions of the slides.
The square remains zero and the two same-colour braid words acquire the
same scalar `(-s)^3`. No right transposition occurs, so there is no extra
transpose sign. In particular the coefficient is minus one for an even
colour and plus one for an odd colour. The even comparison is
`Categorification/TwoRep/RouqReverse.lean`, `RouqFamily.reverse`, which
retains the dots and negates the reversed crossing. Its cyclicity-based
mixed-inversion proof is not an input here.

The homogeneous transformation in (3) is obtained by
`homPreTransform`, with even reassociations from `homPreComp`.
Its degree is p. This specifies the unbundled same-colour datum only;
no multicolour action follows from the two slide checks.

## 2. Remove the shifts in the specified mate

Write `L_+=homPre(E_+)`, `K_+=homPre(F_+)`, and likewise with minus.
Functor application is functional order. Write S for the parity shift
of degree sigma and `z:S Z->Z` for its homogeneous comparison. On both
edges the parity is sigma, since their bottom heights differ by two.
The right adjoints are `R_+=S K_+`, `R_-=S K_-`.

For a Hom object H at source lambda, put

```
Q=L_+ R_+ H,        Q0=L_+ K_+ H=P_Y(H),
C=L_+(z_(K_+H)):Q->Q0,
C_tgt=z_(K_-L_-H):R_-L_-H->P_X(H).
```

Let `u_-(Z):Z->K_-L_-Z` be insertion of U_k; let
`v_+(Z):L_+K_+Z->Z` be insertion of `c(k)^(-1)V_k`.
Both have degree sigma. The specified units and counits, from
`HomSectorTransport.md` (4), are

```
eta_-(Z)=u_-(Z);z_(K_-L_-Z)^(-1),
eps_+(H)=(-1)^sigma L_+(z_(K_+H));v_+(H).               (4)
```

In particular the normalization uses c(k) at the cap edge, not c(k-2).
Write T for the upward transformation (3), on `L_-L_+`.
The defining partial-mate word, with functional-order functors, is

```
eta_-(Q);
S K_-(T_(R_+H));
S K_-L_-(eps_+(H)).                                    (5)
```

This is the substitution of the sector into `rouquierMate`, not an
arbitrary map selected to match R. The raw coordinate is (5) preceded
by C inverse and followed by C_tgt.

Here is the complete sign removal. Suppress only functor parentheses
and even coherence. Using `S(g);z=(-1)^(sigma |g|)z;g`, the z inverse
in eta and the final z give

```
D_H = (-1)^(sigma p)
      C^(-1);u_-(Q);K_-(T_(R_+H));K_-L_-(eps_+(H)).      (6)
```

The counit is even, so only T contributes to this first exponent.
Supernaturality of u_- gives

```
C^(-1);u_-(Q)
 = (-1)^sigma u_-(Q0);K_-L_-(C^(-1)).                  (7)
```

Next supernaturality of T, on the morphism `z_(K_+H)^(-1)`
of degree sigma, gives a factor `(-1)^(sigma p)`, replacing T evaluated
at `S K_+H` by T evaluated at `K_+H`. The remaining inverse z is
`K_-L_-L_+(z_(K_+H)^(-1))`. It cancels the z in eps_+ of (4),
whose explicit coefficient is `(-1)^sigma`. The four exponents are

```
sigma p + sigma + sigma p + sigma = 0 in Z/2.           (8)
```

Thus all shift-removal signs cancel, but the factor c(k) inverse and
the crossing coefficient -s remain. Define the unnormalized word

```
W_k = (U_k whisker Y);
      (F_- whisker t whisker F_+);
      (X whisker V_k) : Y->X.                           (9)
```

Equations (3)–(8) prove

```
D_H(H) = -s c(k)^(-1) P_(W_k)(H).                       (10)
```

This calculation works for arbitrary H and homogeneous maps between
such objects. It has not treated a homogeneous parity removal as an even
identification, nor discarded the extra counit sign.

## 3. Evaluate the unnormalized word by signed pitchforks

Put `L_k=sigL` at height k. The required identity is

```
W_k = w(k) L_k,   w(k)=1 (k<=0), w(k)=s (k>0).          (11)
```

The input is the same-colour local inversions, squares and upward braid,
the signed pitchforks in `RouquierPitchfork.lean`, and the unnormalized
F snake from `SignedFTriangle.md`. The F snake is available as a written
proof; this argument does not claim its Lean implementation is complete.

For k>=0 the theorem `cupL_pitchfork_of_nonneg` says

```
(U_k whisker E_+);(F_- whisker t)
 = b(k) (E_+ whisker U_(k+2));(L_k whisker E_+),
b(k)=s if k=0, and 1 if k>0.                            (12)
```

Whisker (12) with F_+ and finish with `X whisker V_k`.
Moving L_k, of degree p, past V_k, of degree sigma, costs
`(-1)^(p sigma)`. The remaining U_(k+2),V_k pair is exactly
the F_+ snake, whose value is c(k). Therefore

```
W_k=b(k)(-1)^(p sigma)c(k)L_k,    k>=0.                 (13)
```

Since `(-1)^(p sigma)=s^(k+1)` and `c(k)=s^k` in this
range, the product is `b(k)s`: it is one at k=0 and s at k>0.
The boundary factor in (12) must not be dropped.

For k<=0 apply `capL_pitchfork_below_neg_one` at lower height
h=k-2. Its upper local datum is the one at height k. In these indices
it reads

```
(t whisker F_+);(E_- whisker V_k)
 = (E_- whisker L_k);(V_(k-2) whisker E_-).              (14)
```

Whisker by F_- and precede by `U_k whisker Y`. Move U_k past
L_k once, costing `(-1)^(p sigma)`. The remaining U_k,V_(k-2)
pair is the F_- snake with coefficient c(k-2). Hence

```
W_k=(-1)^(p sigma)c(k-2)L_k,     k<=0.                  (15)
```

Here `c(k-2)=s^(k-1)`, so the product is `s^(2k)=1`.
This proves (11), including k=0 independently of (13). For the other
boundary k=1, `capL_pitchfork_at_neg_one` supplies a factor s;
its F_- snake has c(-1)=1 and sigma=0, again giving s L_1.
Thus neither exceptional boundary is inferred by an unsigned reflection.
All identities retain the inverse-defined L_k, not an inverse of the
bare crossing.

Combining (10), (11), and `L_k=-R` gives

```
gamma(k)=s c(k)^(-1) w(k).                              (16)
```

For k<0 this is `s*s^(k+1)=s^k`; for k>0 it is
`s*s^k*s=s^k`; for k=0 it is s. This proves (1) at every
integer height. The nonexceptional expression cannot be extended to
zero for an odd colour. All scalars in (12)–(16) have integer degree zero.

## 4. Whole augmented matrices, with all identity summands

This paragraph uses the window identities and ordered invertible changes
T_+, T_- in `ReversedReservoirMatrix.md` §§3–5. It is a consequence
of those calculations and (1), not an independent review of that note.
Keep its shifted summands and their homogeneous z lifts. Define

```
alpha_n=(-1)^(sigma n p),
beta_n=(-1)^(sigma(1+n p)) c(k)^(-1).
```

These are the actual cup and cap coefficients from the specified Hom
adjunction. In target-row/source-column notation the Hom matrices in
reservoir coordinates are

```
k>0: M_+=[gamma R, (alpha_n U_n)_(0<=n<k)] : Y+Anew->X,
k<0: M_-=[gamma R; (beta_n V_n)_(0<=n<-k)] : Y->X+Bnew,
k=0: M_0=gamma R : Y->X.                               (17)
```

If `Psi_+=[R,U]` and `Psi_-=[R;V]` denote the window matrices,
the complete rescalings and inverses are

```
M_+=Psi_+ diag(gamma,diag(alpha_n)),
M_+^(-1)=diag(gamma^(-1),diag(alpha_n^(-1))) Psi_+^(-1),
M_-=diag(gamma,diag(beta_n)) Psi_-,
M_-^(-1)=Psi_-^(-1) diag(gamma^(-1),diag(beta_n^(-1))),
M_0^(-1)=gamma^(-1) f.                                 (18)
```

In the fourth line the final diagonal has the two blocks gamma inverse
and the beta inverse diagonal; all its indices satisfy `0<=n<-k`.
Both inverse products cancel adjacent diagonal matrices and then the
corresponding Psi inverse product. Thus no identity block is omitted.
In particular the principal inverse is `gamma^(-1) f=gamma f`,
not automatically f. Scaling only R while leaving its inverse unchanged
would violate the principal inverse identities.

More explicitly, writing `Psi_+^(-1)=[f;vtilde]` and
`Psi_-^(-1)=[f,utilde]`, the full finite component equations are

```
k>0:
 R;f=1_Y, R;vtilde_n=0, U_n;f=0,
 U_n;vtilde_m=delta_nm, f;R+sum_n vtilde_n;U_n=1_X;
k<0:
 f;R=1_X, utilde_n;R=0, f;V_n=0,
 utilde_n;V_m=delta_nm, R;f+sum_n V_n;utilde_n=1_Y.
```

Replace each forward component by its coefficient in (17) and its
matching inverse component by the reciprocal coefficient in (18).
Diagonal terms and each summand in the total identity retain coefficient
one; every off-diagonal zero is multiplied by an even unit. At zero both
identity windows are empty and both `R;f=1_Y` and `f;R=1_X` are used.
This proves the finite inverse equations without assuming R or f is
invertible away from zero.

## 5. Consequence and remaining scope

The principal inverse in (18) has degree zero. The left closures
`U_r;(gamma f);V_s` have degree `2d_i(r+s+1)>0`. The fixed-content
supercentre argument can therefore bound these particular closures,
under its stated graded factor-action hypotheses. This is not yet a
proof that the complete Hom feedback has that supported form.

The two shifted swapping partial mates, their tensor support, the
residual identity-summand matrix, multicolour fusion relations and joint
separation remain open. In particular neither (TC) nor nondegeneracy is
claimed. No cyclicity, abstract uniqueness of adjoints, or preservation
of isomorphisms by an arbitrary partial mate was used in (1)–(16).
