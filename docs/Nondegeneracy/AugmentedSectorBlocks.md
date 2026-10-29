# Sector blocks of the equal-colour augmented maps

**Status.** §1 is checked in Lean
(`OddMath/QuiverHecke/SwappedAssembly/Sigma/SameColourBlocks.lean`). §§2–4 are a
**proposed** written bridge between the Hom-sector inversion of `SwappedHomInversion.md`
and the summand-path entries of `AugmentedInvertible` (`SwappedAssembly/LeftwardInverse.lean`).
They are not Lean theorems.

Notation. A summand path of a word is a choice of side, `P` (probe, precomposition) or `R`
(reservoir, postcomposition), for every letter, left letter first; `t` is the leftmost and
`s` the rightmost sector, and the entries are natural maps between functors `H s ⥤ H t`
(`pathFunctor`). The left letter of a path is applied last. Write `e = Finsupp.single i 1` and
`t ± (i,i) = (t.1 ± e, t.2 ± e)`.

## 1. The block decomposition (checked)

The four paths of `Eᵢ Fᵢ` from `t` end at

| sides | rightmost sector | condition |
|---|---|---|
| `(P,P)` | `t` | none |
| `(R,R)` | `t` | `1 ≤ t.2 i` |
| `(P,R)` | `t + (i,i)` | none |
| `(R,P)` | `t - (i,i)` | `1 ≤ t.1 i`, `1 ≤ t.2 i` |

and those of `Fᵢ Eᵢ` at `t` for `(P,P)` (`1 ≤ t.1 i`) and `(R,R)` (no condition), at
`t - (i,i)` for `(P,R)` and at `t + (i,i)` for `(R,P)` (same conditions). The empty word has
only the path `t → t`. Hence for `s ≠ t` the dotted windows of (1.13), (1.14) are empty and
each of `Eᵢ Fᵢ`, `Fᵢ Eᵢ` has at most one path, both existing together
(`SPath.subsingleton_upDn_self`, `SPath.subsingleton_dnUp_self`,
`SPath.nonempty_dnUp_self_iff`, `SPath.isEmpty_nil_of_ne`). Between such sectors the
augmented map is the single entry `σ` (for (1.13)) or `-σ` (for (1.14)), and in both cases
the leftward-crossing component of the inverse is `lc = -σ⁻¹`, with no `♦`-cups or caps (`posInverse_of_ne`, `negInverse_of_ne`). So

    AugmentedInvertible c  ⇐  CentralInvertible c  ∧  SwappingInvertible c

(`augmentedInvertible_of_central_of_swapping`): the augmented maps at `s = t` have inverses,
and the entries `σ` between distinct sectors are isomorphisms.

## 2. The swapping entries (proposed)

`σ = sigmaL i i` is the cup on the left, the crossing in the middle and the cap on the right.
In `compList` the intermediate paths are forced by the sectors: the cup and the cap each join
two letters into a path from a sector to itself, so both of their letters are on the same
side. This leaves one term in each swapping entry.

* `s = t + (i,i)`: `p = (P,R)`, `q = (R,P)`. The cup is on `R`, the crossing input is `(R,P)`,
  the cap (on the letter facing the `F` of `p`, side `R`) forces crossing output `(P,R)`. The
  crossing entry is `(R,P) → (P,R) = -(a ; a ; J⁻¹)`. So `σ` is the reservoir (post) mate of
  `-(a ; a ; J⁻¹)`: this is `W_B` of `SwappedHomInversion.md` §7.
* `s = t - (i,i)`: `p = (R,P)`, `q = (P,R)`. The cup is on `P`, the crossing input is
  `(P,R)`, the cap forces output `(R,P)`. The crossing entry is `J`. So `σ` is the probe (pre)
  mate of `J`: this is `W_A` of §7.

`SwappedHomInversion.md` (15)–(16) and `HomSwappingMates.md` give the inverses: `W_A` is the
mate of the interchange (no inverse of a dot is needed), `W_B` needs `g_B⁻¹` with the probe dot
a unit and the transposed reservoir dot nilpotent (F2, F3). The Lean form of this step is: the
`compList` reduction to the single term above, followed by the identification of that term with
the mates of `RouquierHomMixedInterchange` and of the mixed coefficient.

## 3. The central block (proposed)

At `s = t` the summands are: `Eᵢ Fᵢ`: `(P,P)` (`X_A` of §2 there, A = probe) and `(R,R)`
(`X_B`, absent when `t.2 i = 0`); `Fᵢ Eᵢ`: `(P,P)` (`Y_A`, absent when `t.1 i = 0`) and `(R,R)`
(`Y_B`); and one copy of the identity for each dot index of the window. By the same
cup/cap argument the four `σ` entries are single terms:

| entry | cup | crossing input → output | crossing entry |
|---|---|---|---|
| `(P,P) → (P,P)` | `P` | `(P,P) → (P,P)` | `-q` times the probe crossing (`s_A`) |
| `(R,R) → (R,R)` | `R` | `(R,R) → (R,R)` | the reservoir crossing (`s_B`) |
| `(P,P) → (R,R)` (`D`) | `R` | `(R,P) → (R,P)` | `a` |
| `(R,R) → (P,P)` (`C`) | `P` | `(P,R) → (P,R)` | `-(J ; a ; J⁻¹)` |

The window entries `ε xⁿ` on `(P,P)` and `(R,R)` are the dotted caps `v_A(n)`, `v_B(n)` of §2
there, and `xⁿ η` on `Fᵢ Eᵢ` the dotted cups `u_A(n)`, `u_B(n)`; the fused windows of §5 there
are exactly the single empty path with `n` ranging over `Fin |⟨hᵢ, ν⟩|`. A zero corner (an
absent path) is the zero summand of `SwappedHomInversion.md`, which states its formulas on
zero corners as well. The recovery formulas (13), (14) there then give `PosInverse` (`H ≥ 0`)
and `NegInverse` (`H < 0`) at `s = t`, with `lc` the `X ← Y` block of the inverse and `dc` the
window rows or columns.

## 4. The sign of the central entries at even colours

The crossing entries in the table above are those of `Generators/Cross.lean`, whose diagonal
signs are checked against the relations `quadEq` and `slideEq` (`QuadSame.lean`,
`SlideSame.lean`). They are `-q` times the diagonal entries of (2) of
`SwappedHomInversion.md` read with its labels (A = probe, execution word `AB` = path `(R,P)`):
(2) has `-q a` on `(R,P)` and `q J⁻¹ a J` on `(P,R)`, the checked entries are `a` and
`-(J ; a ; J⁻¹)`. The off-diagonal swapping entries agree. Hence the central entries of the
checked crossing are `-q` times (4) there, and the matrix `K` of (6) is replaced by `-q K`,
which is the `K` of the earlier version for both parities. For `p = 1` nothing changes. For
`p = 0` this would make the §5 tables, which are still written with the earlier sign, the
correct ones. This reading of the labels is proposed and has to be rechecked against
`ProbeWindowInverse.md` (4) before the even-colour case of §§5–6 there is used.
