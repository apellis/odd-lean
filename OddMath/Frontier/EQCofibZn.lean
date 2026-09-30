import OddMath.Frontier.EQOnhDGZn
import OddMath.Frontier.EQOnhDGAcyclic
import OddMath.Frontier.EQZnFiniteCell
import OddMath.Frontier.SmallRank
import DG.Homotopy.Lifting
import DG.Homotopy.Regular

/-!
# Cofibrancy of `Z_n` over `ONH_n` (Proposition 3.17)

Source: A. P. Ellis, Y. Qi, *The differential graded odd nilHecke algebra*, arXiv:1504.01712v2,
§2.2 (the definition of cofibrant dg modules, before Proposition 2.3) and §3.4, Proposition 3.17:
the following are equivalent:

1. as a left dg module over `ONH_n`, `Z_n` is cofibrant;
2. as a chain complex, `Z_n` is not acyclic;
3. `n = 0` or `n = 1`.

## Cofibrant

Ellis–Qi §2.2 call a dg module `P` *cofibrant* (or K-projective) if for every surjective
quasi-isomorphism `f : M → N` every morphism `g : P → N` lifts along `f`. This is literally
`DG.HasLiftingProperty` of the `DG` library, which is used here. (It is equivalent to being
K-projective *and* projective as a graded module, `DG.hasLiftingProperty_iff`; for the
non-cofibrancy of `Z_n`, `n ≥ 2`, the stronger statement that `Z_n` is not even K-projective,
`DG.IsKProjective`, is proved.) The test modules of these properties range over a universe
parameter `w`; all statements below hold for every `w`.

## Ranks

For `N = n + 2 ≥ 2`, `ONH_N` is the dg ring `OddMath.Frontier.EQOnhDG.ONH n` and `Z_N` is a
left dg `ONH_N`-module by `ONH.instDGModuleZn` (Corollary 3.9). For `N ≤ 1` there are no
crossings: the odd nilHecke algebra on `N ≤ 1` strands is the polynomial algebra, `ONH_1 = OPol_1`
(with `d(x) = x²`) and `ONH_0 = OPol_0 = ℤ`; these are the dg rings
`OddMath.Frontier.EQSkewDifferential.OPol N`, and `Z_N` is a left dg `OPol_N`-module
(`OPolAlpha.instDGModule`).

## Contents

* The generic inputs come from the `DG` library: `DG.isContractible_of_isKProjective` (an
  acyclic K-projective dg module is contractible, for test modules in any universe, via the
  universe lift `ULift M`) and `DG.isGradedProjective_self`, `DG.hasLiftingProperty_self` (the
  regular dg module `A` is cofibrant).
* `ONH.zn_not_isContractible`: `Z_{n+2}` is not contractible as a left dg `ONH_{n+2}`-module;
  a null-homotopy of the identity would be an odd left `OPol_{n+2}`-linear null-homotopy,
  excluded by `EQZn.zn_not_contractible`.
* `ONH.zn_not_isKProjective`, `ONH.zn_not_hasLiftingProperty`: for `N ≥ 2`, `Z_N` is not
  K-projective, hence not cofibrant, over `ONH_N`.
* `znEquivRegular`: for `N ≤ 1`, `Z_N ≅ OPol_N = ONH_N` as left dg modules (the regular module);
  `zn_hasLiftingProperty_small`: so `Z_N` is cofibrant.
* `opolZeroEquiv`, `opolZero_mem_grading`, `opolZero_d`: `OPol_0 ≅ ℤ`, concentrated in degree
  `0` with `d = 0`.
* `zn_isAcyclic_iff`: `Z_N` is acyclic iff `N ≥ 2`.
* `ZnCofibrant N`: the statement (1); `prop_3_17`: the equivalences (1) ⟺ (2) ⟺ (3).

## Proof for `n ≥ 2`

Ellis–Qi argue with the multiplication map `ONH_n ⊗ Z_n → Z_n` and `HOM_{ONH_n}(-, Z_n)`. Here
the argument is shorter: an acyclic cofibrant (indeed K-projective) module is contractible, and
a contracting homotopy of `Z_n` would be an odd `OPol_n`-linear map `h` with `dh + hd = id`;
evaluating at `1_z` and taking constant terms gives `1 = 0` (`EQZn.zn_not_contractible`).
-/

noncomputable section

universe w

namespace OddMath.Frontier.EQCofib

open OddMath.SkewPolynomial (SkewPolynomial generator)
open OddMath.Frontier.EQSkewDifferential (OPol OPolAlpha Zn zAlpha sAlpha dAlpha indicator
  oddStrands)
open OddMath.Frontier.EQOnhDG

/-- The ring structure of `OPol`, preferred over the pointwise `Finsupp` structure. -/
local instance (priority := high) cofibZnNUNASemiring (m : ℕ) :
    NonUnitalNonAssocSemiring (SkewPolynomial m) :=
  @NonAssocSemiring.toNonUnitalNonAssocSemiring _
    (@Semiring.toNonAssocSemiring _ (OddMath.PbwL3.instSemiring m))

local instance (priority := high) cofibZnNUNARing (m : ℕ) :
    NonUnitalNonAssocRing (SkewPolynomial m) :=
  @NonAssocRing.toNonUnitalNonAssocRing _ (@Ring.toNonAssocRing _ (OddMath.PbwL3.instRing m))

/-! ## `N ≥ 2`: `Z_N` is not cofibrant over `ONH_N` -/

namespace ONH

variable {n : ℕ}

/-- The identification of `Z_{n+2}` with the skew-polynomial model. -/
abbrev zEquiv (n : ℕ) : SkewPolynomial (n + 2) ≃+ Zn (n + 2) :=
  OPolAlpha.equiv (n + 2) (oddStrands (n + 2))

theorem zEquiv_generator_mul (j : Fin (n + 2)) (f : SkewPolynomial (n + 2)) :
    zEquiv n (generator j * f) = ONH.x j • zEquiv n f := by
  rw [← ONH.polyHom_x, ONH.polyHom_smul, OPolAlpha.smul_equiv]
  rfl

theorem zEquiv_dAlpha (f : SkewPolynomial (n + 2)) :
    zEquiv n (dAlpha (zAlpha (n + 2)) f) = DG.d (zEquiv n f) := by
  rw [OPolAlpha.d_equiv, EQSkewDifferential.indicator_oddStrands]

/-- **`Z_{n+2}` is not contractible** as a left dg `ONH_{n+2}`-module: a null-homotopy `h` of the
identity is a cochain of degree `-1`, hence odd and left `OPol_{n+2}`-linear
(`h(x_j z) = -x_j h(z)`), which `EQZn.zn_not_contractible` excludes. -/
theorem zn_not_isContractible : ¬ DG.IsContractible (ONH n) (Zn (n + 2)) := by
  rintro ⟨h⟩
  apply EQZn.zn_not_contractible (N := n + 2)
  let H : SkewPolynomial (n + 2) →+ SkewPolynomial (n + 2) :=
    { toFun := fun f => (zEquiv n).symm (h.hom (zEquiv n f))
      map_zero' := by rw [map_zero, map_zero, map_zero]
      map_add' := fun f g => by rw [map_add, map_add, map_add] }
  refine ⟨H, fun j f => ?_, fun f => ?_⟩
  · change (zEquiv n).symm (h.hom (zEquiv n (generator j * f))) =
      -(generator j * (zEquiv n).symm (h.hom (zEquiv n f)))
    rw [zEquiv_generator_mul, h.hom.map_smul (ONH.x_mem_grading (n := n) j),
      show (-1 : ℤ) * 1 = -1 by norm_num, DG.koszulSign_odd (by decide), Units.smul_def,
      Units.val_neg, Units.val_one, neg_one_zsmul, map_neg, ← ONH.polyHom_x, ONH.polyHom_smul,
      OPolAlpha.symm_smul]
    rfl
  · have hc := h.comm (zEquiv n f)
    rw [DG.DGModuleHom.zero_apply, add_zero, DG.DGModuleHom.id_apply] at hc
    have hd : ∀ z, dAlpha (zAlpha (n + 2)) ((zEquiv n).symm z) = (zEquiv n).symm (DG.d z) :=
      fun z => by
        apply (zEquiv n).injective
        rw [AddEquiv.apply_symm_apply, zEquiv_dAlpha, AddEquiv.apply_symm_apply]
    change dAlpha (zAlpha (n + 2)) ((zEquiv n).symm (h.hom (zEquiv n f))) +
      (zEquiv n).symm (h.hom (zEquiv n (dAlpha (zAlpha (n + 2)) f))) = f
    rw [hd, zEquiv_dAlpha, ← map_add, ← hc, AddEquiv.symm_apply_apply]

/-- **Ellis–Qi, Proposition 3.17** (`n ≥ 2`, K-projective form): `Z_{n+2}` is not K-projective
as a left dg `ONH_{n+2}`-module. It is acyclic (Proposition 3.16(2)), so K-projectivity would
make it contractible, contradicting `zn_not_isContractible`. -/
theorem zn_not_isKProjective : ¬ DG.IsKProjective.{w} (ONH n) (Zn (n + 2)) := fun h =>
  zn_not_isContractible
    (DG.isContractible_of_isKProjective h (ONH.isAcyclic_module (n := n) (Zn (n + 2))))

/-- **Ellis–Qi, Proposition 3.17** (`n ≥ 2`): `Z_{n+2}` is not cofibrant as a left dg
`ONH_{n+2}`-module (it does not have the lifting property against surjective
quasi-isomorphisms). -/
theorem zn_not_hasLiftingProperty : ¬ DG.HasLiftingProperty.{w} (ONH n) (Zn (n + 2)) :=
  fun h => zn_not_isKProjective h.isKProjective

end ONH

/-! ## `N ≤ 1`: `Z_N` is the regular module over `ONH_N = OPol_N` -/

section Small

variable {N : ℕ}

/-- `ONH_0 = OPol_0 ≅ ℤ` as rings (`SmallRank.zeroEquiv`; `SmallRank.ONH 0 = ℤ`,
`SmallRank.ONH 1 = OPol_1`). -/
def opolZeroEquiv : OPol 0 ≃+* ℤ := (OPol.equiv 0).symm.trans SmallRank.zeroEquiv

/-- `OPol_0` is concentrated in degree `0`. -/
theorem opolZero_mem_grading (f : OPol 0) : f ∈ DG.grading (M := OPol 0) 0 :=
  OPol.mem_grading_iff.mpr fun _ _ => by simp [EQSkewDifferential.totalDeg]

/-- The differential of `OPol_0` vanishes: `OPol_0` is `ℤ` concentrated in degree `0` with
`d = 0`. -/
theorem opolZero_d (f : OPol 0) : DG.d f = 0 := by
  apply (OPol.equiv 0).symm.injective
  rw [OPol.symm_d, SmallRank.eq_intCast_zero ((OPol.equiv 0).symm f), ← zsmul_one, map_zsmul,
    EQSkewDifferential.d_one, smul_zero, map_zero]

theorem sAlpha_indicator_small (hN : N ≤ 1) : sAlpha (indicator (oddStrands N)) = 0 := by
  rw [EQSkewDifferential.indicator_oddStrands, EQZn.sAlpha_zAlpha_small hN]

theorem dAlpha_indicator_small (hN : N ≤ 1) (f : SkewPolynomial N) :
    dAlpha (indicator (oddStrands N)) f = EQSkewDifferential.d N f := by
  rw [EQSkewDifferential.dAlpha_apply, sAlpha_indicator_small hN, mul_zero, add_zero]

/-- For `N ≤ 1`, the identity `Z_N → OPol_N` (`f 1_z ↦ f`) as a morphism of left dg
`OPol_N`-modules: `d(1_z) = 0` since `α = 0`. -/
def znToRegular (hN : N ≤ 1) : Zn N →ᵈᵍ[OPol N] OPol N where
  toFun z := OPol.equiv N ((OPolAlpha.equiv N (oddStrands N)).symm z)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  map_mem' h := h
  map_d' _ := dAlpha_indicator_small hN _

/-- For `N ≤ 1`, the identity `OPol_N → Z_N` (`f ↦ f 1_z`) as a morphism of left dg
`OPol_N`-modules. -/
def regularToZn (hN : N ≤ 1) : OPol N →ᵈᵍ[OPol N] Zn N where
  toFun f := OPolAlpha.equiv N (oddStrands N) ((OPol.equiv N).symm f)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  map_mem' h := h
  map_d' _ := (dAlpha_indicator_small hN _).symm

/-- **Ellis–Qi, proof of Proposition 3.17** (`n ∈ {0, 1}`): `Z_N ≅ ONH_N = OPol_N` as the left
regular dg module. -/
def znEquivRegular (hN : N ≤ 1) : Zn N ≃ᵈᵍ[OPol N] OPol N where
  toFun := znToRegular hN
  invFun := regularToZn hN
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  map_mem' h := h
  map_d' := (znToRegular hN).map_d

/-- **Ellis–Qi, Proposition 3.17** (`n ∈ {0, 1}`): `Z_N` is cofibrant as a left dg module over
`ONH_N = OPol_N`, being isomorphic to the regular module. -/
theorem zn_hasLiftingProperty_small (hN : N ≤ 1) : DG.HasLiftingProperty.{w} (OPol N) (Zn N) :=
  have hri : (regularToZn hN).comp (znToRegular hN) = DG.DGModuleHom.id :=
    DG.DGModuleHom.ext fun _ => rfl
  DG.hasLiftingProperty_iff.mpr
    ⟨DG.IsKProjective.of_retract (DG.isKProjective_self (A := OPol N)) (znToRegular hN)
        (regularToZn hN) (DG.Homotopic.of_eq hri),
      DG.IsGradedProjective.of_retract (DG.isGradedProjective_self (OPol N)) (znToRegular hN)
        (regularToZn hN) hri⟩

end Small

/-! ## Acyclicity -/

/-- **Ellis–Qi, Proposition 3.17** (the acyclicity part, dg form): `Z_N` is acyclic iff
`N ≥ 2`. For `N ≥ 2` every dg `ONH_N`-module is acyclic (Proposition 3.16(2)); for `N ≤ 1`,
`1_z` is a cocycle of degree `0` which is not a coboundary. -/
theorem zn_isAcyclic_iff (N : ℕ) : DG.IsAcyclic (Zn N) ↔ 2 ≤ N := by
  constructor
  · intro h
    by_contra hN
    have hN : N ≤ 1 := by omega
    have hd : DG.d (OPolAlpha.one N (oddStrands N)) = 0 := by
      apply (OPolAlpha.equiv N (oddStrands N)).symm.injective
      rw [OPolAlpha.symm_d, EQSkewDifferential.indicator_oddStrands, map_zero]
      exact (EQZn.zn_not_acyclic hN).1
    obtain ⟨g, -, hg⟩ := h.exists_d_eq (OPolAlpha.one_mem_grading (n := N)) hd
    apply (EQZn.zn_not_acyclic hN).2 ((OPolAlpha.equiv N (oddStrands N)).symm g)
    have := congrArg (OPolAlpha.equiv N (oddStrands N)).symm hg
    rwa [OPolAlpha.symm_d, EQSkewDifferential.indicator_oddStrands] at this
  · intro hN
    obtain ⟨n, rfl⟩ : ∃ n, N = n + 2 := ⟨N - 2, by omega⟩
    exact ONH.isAcyclic_module (n := n) (Zn (n + 2))

/-! ## Proposition 3.17 -/

/-- Statement (1) of **Ellis–Qi, Proposition 3.17**: `Z_N` is cofibrant (has the lifting
property against surjective quasi-isomorphisms, test modules in `Type w`) as a left dg module over
`ONH_N`. Here `ONH_N = OPol_N` for `N ≤ 1` (no crossings) and `ONH_{n+2}` is `EQOnhDG.ONH n`. -/
def ZnCofibrant : ℕ → Prop
  | 0 => DG.HasLiftingProperty.{w} (OPol 0) (Zn 0)
  | 1 => DG.HasLiftingProperty.{w} (OPol 1) (Zn 1)
  | n + 2 => DG.HasLiftingProperty.{w} (ONH n) (Zn (n + 2))

/-- **Ellis–Qi, Proposition 3.17**: the following are equivalent:
(1) as a left dg module over `ONH_N`, `Z_N` is cofibrant;
(2) as a chain complex, `Z_N` is not acyclic;
(3) `N = 0` or `N = 1`. -/
theorem prop_3_17 (N : ℕ) :
    (ZnCofibrant.{w} N ↔ ¬ DG.IsAcyclic (Zn N)) ∧ (¬ DG.IsAcyclic (Zn N) ↔ N = 0 ∨ N = 1) := by
  have h23 : ¬ DG.IsAcyclic (Zn N) ↔ N = 0 ∨ N = 1 := by
    rw [zn_isAcyclic_iff]; omega
  refine ⟨?_, h23⟩
  rw [h23]
  match N with
  | 0 => exact iff_of_true (zn_hasLiftingProperty_small (by norm_num)) (Or.inl rfl)
  | 1 => exact iff_of_true (zn_hasLiftingProperty_small le_rfl) (Or.inr rfl)
  | n + 2 => exact iff_of_false ONH.zn_not_hasLiftingProperty (by omega)

end OddMath.Frontier.EQCofib

end
