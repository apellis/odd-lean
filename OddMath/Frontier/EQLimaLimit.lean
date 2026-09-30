import OddMath.Frontier.EQLimaOsym
import OddMath.Frontier.OddLRTableau
import OddMath.Frontier.OddLRMisc
import OddMath.Frontier.EKLSectionTwoG
import Mathlib.RingTheory.TwoSidedIdeal.Basic
import Mathlib.RingTheory.Congruence.Defs

/-!
# Ellis–Qi, Appendix A.1: the dg algebra `OΛ` and its cohomology ring

A. P. Ellis, Y. Qi, *The differential graded odd nilHecke algebra*, arXiv:1504.01712v2,
Appendix A.1.3: `OΛ` is the limit of the dg algebras `OΛ_n` under `x_{n+1} ↦ 0`; its
cohomology ring is the subject of Propositions A.2 (1) and A.3.

* `SuperDG.Data`: a ring with an odd differential `D` (`D(xy) = D(x) y + ι(x) D(y)`, `D² = 0`,
  `D ι = -ι D`) with respect to an involution `ι`; `cocycles` is a subring, `boundaries` a
  two-sided ideal of it, and `H` the cohomology ring (`cls : cocycles →+* H`).
* The dg algebra `OΛ`: the library's `Q` (Ellis–Khovanov's `OΛ`, with the odd Schur basis
  `s_λ = sK λ` and the projections `π_{n+2} : Q → OΛ̃_{n+2}`), which is the inverse limit of the
  `OΛ̃_N`. The untwisted `OΛ_N` of Ellis–Qi is identified with `OΛ̃_N` by `θ`
  (`map_theta_osym_kernel`), which sends `s_λ` to `s̃_λ`. The differential `DQ` is defined on
  the Schur basis by Proposition 3.11, and `piN_DQ` shows it is the limit of the differentials:
  `π_{n+2} ∘ DQ = θ d θ ∘ π_{n+2}` for every `n`, which determines `DQ`
  (`eq_of_piN`). `iotaQ` is the parity involution (`π ∘ ι = ι ∘ π`).
* `dataQ`: `(Q, DQ, iotaQ)` is a super dg ring; `HQ` its cohomology ring.
* `HQ_basis`: `H(OΛ)` is free with basis the classes of the Lima Schur functions
  (Proposition A.2 (1), now for the actual `OΛ`); `cls_sK_mul`: the product of classes is given
  by the odd Littlewood–Richardson coefficients of [E] (`OddLRTableau.oddLR`) restricted to Lima
  partitions.
* `oddLR_comm_of_lima`: for Lima `λ, μ, ν`, `c^λ_{μν} = c^λ_{νμ}` (from Ellis–Khovanov's
  anti-involution, `EKLSectionTwo.reverse_sK`, whose eigenvalue is `1` on Lima partitions);
  hence `HQ` is commutative (`HQ.instCommRing`).
-/

namespace OddMath.Frontier.EQLima

open Finset

/-! ### Super dg rings and their cohomology rings -/

namespace SuperDG

/-- A ring with an odd differential with respect to an involution `ι`. -/
structure Data (R : Type*) [Ring R] where
  /-- the differential -/
  D : R →+ R
  /-- the parity involution -/
  ι : R →+* R
  leibniz : ∀ x y, D (x * y) = D x * y + ι x * D y
  sq : ∀ x, D (D x) = 0
  anti : ∀ x, D (ι x) = -ι (D x)
  invol : ∀ x, ι (ι x) = x

variable {R : Type*} [Ring R] (S : Data R)

theorem Data.D_one : S.D 1 = 0 := by
  have h := S.leibniz 1 1
  simp only [mul_one, one_mul, S.ι.map_one] at h
  calc S.D 1 = (S.D 1 + S.D 1) - S.D 1 := by abel
    _ = S.D 1 - S.D 1 := by rw [← h]
    _ = 0 := sub_self _

/-- The cocycles, a subring. -/
def Data.cocycles : Subring R where
  carrier := {x | S.D x = 0}
  zero_mem' := map_zero S.D
  one_mem' := S.D_one
  add_mem' {x y} hx hy := by
    change S.D (x + y) = 0
    rw [map_add, hx, hy, add_zero]
  neg_mem' {x} hx := by
    change S.D (-x) = 0
    rw [map_neg, hx, neg_zero]
  mul_mem' {x y} hx hy := by
    change S.D (x * y) = 0
    rw [S.leibniz, hx, hy, zero_mul, mul_zero, add_zero]

theorem Data.mem_cocycles {x : R} : x ∈ S.cocycles ↔ S.D x = 0 := Iff.rfl

theorem Data.D_mem_cocycles (y : R) : S.D y ∈ S.cocycles := S.sq y

/-- The coboundaries, a two-sided ideal of the ring of cocycles. -/
def Data.boundaries : TwoSidedIdeal S.cocycles :=
  TwoSidedIdeal.mk' {z | ∃ y, S.D y = (z : R)}
    ⟨0, map_zero S.D⟩
    (by
      rintro x y ⟨a, ha⟩ ⟨b, hb⟩
      exact ⟨a + b, by rw [map_add, ha, hb]; rfl⟩)
    (by
      rintro x ⟨a, ha⟩
      exact ⟨-a, by rw [map_neg, ha]; rfl⟩)
    (by
      rintro z x ⟨a, ha⟩
      refine ⟨S.ι z * a, ?_⟩
      rw [S.leibniz, S.anti, S.invol, z.2, map_zero, neg_zero, zero_mul, zero_add, ha]
      rfl)
    (by
      rintro x z ⟨a, ha⟩
      refine ⟨a * z, ?_⟩
      rw [S.leibniz, z.2, mul_zero, add_zero, ha]
      rfl)

theorem Data.mem_boundaries {z : S.cocycles} : z ∈ S.boundaries ↔ ∃ y, S.D y = (z : R) := by
  rw [Data.boundaries, TwoSidedIdeal.mem_mk']
  rfl

/-- The cohomology ring `H = Z / B`. -/
abbrev Data.H : Type _ := S.boundaries.ringCon.Quotient

/-- The class of a cocycle. -/
def Data.cls : S.cocycles →+* S.H := RingCon.mk' S.boundaries.ringCon

theorem Data.cls_surjective : Function.Surjective S.cls := RingCon.mk'_surjective _

theorem Data.cls_eq_iff (x y : S.cocycles) : S.cls x = S.cls y ↔ ∃ w, S.D w = (x : R) - y := by
  change (S.boundaries.ringCon.mk' x = S.boundaries.ringCon.mk' y) ↔ _
  rw [RingCon.coe_mk', RingCon.eq, TwoSidedIdeal.rel_iff, Data.mem_boundaries]
  rfl

theorem Data.cls_eq_zero_iff (x : S.cocycles) : S.cls x = 0 ↔ ∃ w, S.D w = (x : R) := by
  rw [← map_zero S.cls, Data.cls_eq_iff]
  simp

end SuperDG

/-! ### The dg algebra `OΛ` -/

open OddMath.SkewPolynomial (SkewPolynomial)
open OddMath.Frontier.EQSkewDifferential (osym d theta parityInv)
open OddLREKIdentification (piN sK)
open OddGrassmannSchur (sBasis)
open EKRadicalQuotient (Q)

noncomputable section

instance (n : ℕ) (μ : YoungDiagram) : Decidable (LengthLE n μ) :=
  decidable_of_iff _ (lengthLE_iff n μ).symm

/-- The ring structure of `OPol`, preferred over the pointwise `Finsupp` structure. -/
local instance (priority := high) opolNUNASemiringEQLima (m : ℕ) :
    NonUnitalNonAssocSemiring (SkewPolynomial m) :=
  @NonAssocSemiring.toNonUnitalNonAssocSemiring _
    (@Semiring.toNonAssocSemiring _ (OddMath.PbwL3.instSemiring m))

local instance (priority := high) opolNUNARingEQLima (m : ℕ) :
    NonUnitalNonAssocRing (SkewPolynomial m) :=
  @NonAssocRing.toNonUnitalNonAssocRing _ (@Ring.toNonAssocRing _ (OddMath.PbwL3.instRing m))

/-- The twisted differential `d̃ = θ d θ` on `OPol_N`; it restricts to `OΛ̃_N`. -/
noncomputable def dt (N : ℕ) : SkewPolynomial N →+ SkewPolynomial N :=
  (theta N).toAddMonoidHom.comp ((d N).comp (theta N).toAddMonoidHom)

theorem dt_apply (N : ℕ) (f : SkewPolynomial N) : dt N f = theta N (d N (theta N f)) := rfl

/-- The right-hand side of Proposition 3.11 on `OΛ`: add one white box. -/
noncomputable def dQvec (μ : YoungDiagram) : Q :=
  ∑ b ∈ addableCells IsWhite μ, ((schurSign μ b : ℤˣ) : ℤ) • sK (addCell μ b)

/-- The differential of `OΛ`, defined on the odd Schur basis by Proposition 3.11. -/
noncomputable def DQ : Q →ₗ[ℤ] Q := sBasis.constr ℤ dQvec

theorem DQ_sK (μ : YoungDiagram) : DQ (sK μ) = dQvec μ := by
  rw [← OddGrassmannSchur.sBasis_apply, DQ, Module.Basis.constr_basis]

theorem piN_sK_eq (n : ℕ) (μ : YoungDiagram) :
    piN (n+2) (sK μ) = if LengthLE (n+2) μ then theta (n+2) (schurU (n+2) μ) else 0 := by
  split_ifs with h
  · rw [piN_sK_of n ⟨μ, h⟩, theta_schurU n ⟨μ, h⟩]
  · exact piN_sK_tall n μ h

theorem piN_sK_of_len {n : ℕ} {μ : YoungDiagram} (h : LengthLE (n+2) μ) :
    piN (n+2) (sK μ) = theta (n+2) (schurU (n+2) μ) := by
  rw [piN_sK_eq]; simp [h]

theorem piN_sK_of_not {n : ℕ} {μ : YoungDiagram} (h : ¬ LengthLE (n+2) μ) :
    piN (n+2) (sK μ) = 0 := by
  rw [piN_sK_eq]; simp [h]

theorem lengthLE_of_addCell {N : ℕ} {μ : YoungDiagram} {b : ℕ × ℕ} (hb : Addable μ b)
    (h : LengthLE N (addCell μ b)) : LengthLE N μ ∧ b.1 < N :=
  ⟨fun c hc => h c ((mem_addCell hb c).mpr (Or.inr hc)),
    h b ((mem_addCell hb b).mpr (Or.inl rfl))⟩

theorem lengthLE_addCell {N : ℕ} {μ : YoungDiagram} {b : ℕ × ℕ} (hb : Addable μ b)
    (h : LengthLE N μ) (hbN : b.1 < N) : LengthLE N (addCell μ b) := by
  intro c hc
  rcases (mem_addCell hb c).mp hc with rfl | hc
  · exact hbN
  · exact h c hc

/-- **The differential of `OΛ` is the limit of the differentials of the `OΛ_N`**:
`π_{n+2}(D x) = θ d θ (π_{n+2} x)`. -/
theorem piN_DQ (n : ℕ) (x : Q) : piN (n+2) (DQ x) = dt (n+2) (piN (n+2) x) := by
  have key : ((piN (n+2)).toAddMonoidHom.toIntLinearMap ∘ₗ DQ) =
      (dt (n+2)).toIntLinearMap ∘ₗ (piN (n+2)).toAddMonoidHom.toIntLinearMap := by
    refine sBasis.ext fun μ => ?_
    simp only [LinearMap.coe_comp, Function.comp_apply, AddMonoidHom.coe_toIntLinearMap,
      RingHom.toAddMonoidHom_eq_coe, AddMonoidHom.coe_coe, OddGrassmannSchur.sBasis_apply]
    rw [DQ_sK, dQvec, map_sum, piN_sK_eq]
    simp only [map_zsmul]
    split_ifs with h
    · rw [dt_apply, EQSchur.theta_theta, prop_3_11_cells, map_sum]
      simp only [map_zsmul]
      rw [← Finset.sum_filter_add_sum_filter_not (addableCells IsWhite μ) (fun b => b.1 < n + 2)]
      have e : (addableCells IsWhite μ).filter (fun b => b.1 < n + 2) =
          addableCells (fun c => IsWhite c ∧ c.1 < n + 2) μ := by
        ext b
        simp only [Finset.mem_filter, mem_addableCells]
        tauto
      rw [e, Finset.sum_eq_zero (s := (addableCells IsWhite μ).filter _), add_zero]
      · refine Finset.sum_congr rfl fun b hb => ?_
        obtain ⟨⟨-, hbN⟩, hab⟩ := mem_addableCells.mp hb
        rw [piN_sK_of_len (lengthLE_addCell hab h hbN)]
      · intro b hb
        obtain ⟨hb1, hb2⟩ := Finset.mem_filter.mp hb
        obtain ⟨-, hab⟩ := mem_addableCells.mp hb1
        rw [piN_sK_of_not (fun h' => hb2 (lengthLE_of_addCell hab h').2), smul_zero]
    · rw [map_zero]
      refine Finset.sum_eq_zero fun b hb => ?_
      obtain ⟨-, hab⟩ := mem_addableCells.mp hb
      rw [piN_sK_of_not (fun h' => h (lengthLE_of_addCell hab h').1), smul_zero]
  exact LinearMap.congr_fun key x

/-- An element of `OΛ` is determined by its projections to the `OΛ̃_{n+2}`. -/
theorem eq_zero_of_piN {x : Q} (h : ∀ n, piN (n+2) x = 0) : x = 0 := by
  apply sBasis.repr.injective
  ext μ
  have hx := (OddSymmetricLimit.piN_eq_zero_iff_mem_tallSpan (μ.colLen 0 + 2) x).mp (h _)
  rw [OddSymmetricLimit.tallSpan,
    OddGrassmannSchur.mem_span_sK_iff (fun lam => μ.colLen 0 + 2 < lam.colLen 0)] at hx
  rw [hx μ (by omega), map_zero, Finsupp.coe_zero, Pi.zero_apply]

theorem eq_of_piN {x y : Q} (h : ∀ n, piN (n+2) x = piN (n+2) y) : x = y := by
  rw [← sub_eq_zero]
  exact eq_zero_of_piN fun n => by rw [map_sub, h n, sub_self]

/-! ### The parity involution of `OΛ` -/

/-- The parity involution on the Schur basis: `s_λ ↦ (-1)^{|λ|} s_λ`. -/
noncomputable def iotaL : Q →ₗ[ℤ] Q := sBasis.constr ℤ (fun μ => (-1 : ℤ) ^ μ.card • sK μ)

theorem iotaL_sK (μ : YoungDiagram) : iotaL (sK μ) = (-1 : ℤ) ^ μ.card • sK μ := by
  rw [← OddGrassmannSchur.sBasis_apply, iotaL, Module.Basis.constr_basis,
    OddGrassmannSchur.sBasis_apply]

theorem card_eq_sum_rowLen (μ : YoungDiagram) :
    μ.card = ∑ i ∈ range (μ.colLen 0), μ.rowLen i := by
  have := OddLRMisc.sum_cells_fst μ (fun _ => 1)
  simp only [mul_one, Finset.sum_const, smul_eq_mul] at this
  exact this

theorem sum_rowExp {N : ℕ} {μ : YoungDiagram} (h : LengthLE N μ) :
    ∑ j, rowExp N μ j = μ.card := by
  have hc := (lengthLE_iff N μ).mp h
  simp only [rowExp]
  rw [Fin.sum_univ_eq_sum_range (fun i => μ.rowLen i) N, card_eq_sum_rowLen]
  symm
  apply Finset.sum_subset (Finset.range_subset_range.mpr hc)
  intro i _ hni
  rw [Finset.mem_range, not_lt] at hni
  by_contra hne
  have : (i, 0) ∈ μ := YoungDiagram.mem_iff_lt_rowLen.mpr (Nat.pos_of_ne_zero hne)
  rw [YoungDiagram.mem_iff_lt_colLen] at this
  omega

theorem piN_iotaL (n : ℕ) (x : Q) : piN (n+2) (iotaL x) = parityInv (n+2) (piN (n+2) x) := by
  have key : ((piN (n+2)).toAddMonoidHom.toIntLinearMap ∘ₗ iotaL) =
      (parityInv (n+2)).toAddMonoidHom.toIntLinearMap ∘ₗ
        (piN (n+2)).toAddMonoidHom.toIntLinearMap := by
    refine sBasis.ext fun μ => ?_
    simp only [LinearMap.coe_comp, Function.comp_apply, AddMonoidHom.coe_toIntLinearMap,
      RingHom.toAddMonoidHom_eq_coe, AddMonoidHom.coe_coe, OddGrassmannSchur.sBasis_apply]
    rw [iotaL_sK, map_zsmul, piN_sK_eq]
    split_ifs with h
    · rw [EQSchur.parityInv_theta, schurU, EQSchur.parityInv_untwisted, map_zsmul,
        sum_rowExp h]
    · rw [smul_zero, map_zero]
  exact LinearMap.congr_fun key x

/-- The parity involution of `OΛ`, a ring endomorphism. -/
noncomputable def iotaQ : Q →+* Q where
  toFun := iotaL
  map_one' := eq_of_piN fun n => by
    rw [piN_iotaL, map_one, map_one]
  map_mul' x y := eq_of_piN fun n => by
    rw [piN_iotaL, map_mul, map_mul, map_mul, piN_iotaL, piN_iotaL]
  map_zero' := map_zero iotaL
  map_add' := map_add iotaL

theorem piN_iotaQ (n : ℕ) (x : Q) : piN (n+2) (iotaQ x) = parityInv (n+2) (piN (n+2) x) :=
  piN_iotaL n x

theorem iotaQ_sK (μ : YoungDiagram) : iotaQ (sK μ) = (-1 : ℤ) ^ μ.card • sK μ := iotaL_sK μ

/-! ### `OΛ` is a super dg ring -/

theorem dt_mul (N : ℕ) (f g : SkewPolynomial N) :
    dt N (f * g) = dt N f * g + parityInv N f * dt N g := by
  rw [dt_apply, map_mul, EQSkewDifferential.d_mul, map_add, map_mul, map_mul, dt_apply, dt_apply,
    EQSchur.theta_theta, EQSchur.parityInv_theta, EQSchur.theta_theta]

theorem dt_dt (N : ℕ) (f : SkewPolynomial N) : dt N (dt N f) = 0 := by
  rw [dt_apply, dt_apply, EQSchur.theta_theta, EQSkewDifferential.d_d, map_zero]

theorem dt_parityInv (N : ℕ) (f : SkewPolynomial N) :
    dt N (parityInv N f) = -parityInv N (dt N f) := by
  rw [dt_apply, dt_apply, ← EQSchur.parityInv_theta, EQSkewDifferential.d_parityInv, map_neg,
    EQSchur.parityInv_theta]

/-- `(OΛ, D, ι)` is a super dg ring. -/
noncomputable def dataQ : SuperDG.Data Q where
  D := DQ.toAddMonoidHom
  ι := iotaQ
  leibniz x y := eq_of_piN fun n => by
    simp only [LinearMap.toAddMonoidHom_coe]
    rw [piN_DQ, map_mul, dt_mul, map_add, map_mul, map_mul, piN_DQ, piN_DQ, piN_iotaQ]
  sq x := eq_of_piN fun n => by
    simp only [LinearMap.toAddMonoidHom_coe]
    rw [piN_DQ, piN_DQ, dt_dt, map_zero]
  anti x := eq_of_piN fun n => by
    simp only [LinearMap.toAddMonoidHom_coe]
    rw [piN_DQ, piN_iotaQ, dt_parityInv, map_neg, piN_iotaQ, piN_DQ]
  invol x := by
    change iotaL (iotaL x) = x
    have : iotaL ∘ₗ iotaL = LinearMap.id := sBasis.ext fun μ => by
      simp only [LinearMap.coe_comp, Function.comp_apply, OddGrassmannSchur.sBasis_apply,
        iotaL_sK, map_zsmul, smul_smul, ← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow,
        one_smul, LinearMap.id_coe, id_eq]
    exact LinearMap.congr_fun this x

/-- The cohomology ring `H(OΛ)`. -/
abbrev HQ : Type _ := dataQ.H

/-! ### The cohomology of `OΛ`: basis and products -/

theorem actsByBoxes_DQ :
    ActsByBoxes whiteSystem sBasis (fun μ b => (schurSign μ b : ℤˣ)) DQ := by
  intro μ
  rw [OddGrassmannSchur.sBasis_apply, DQ_sK, dQvec]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [OddGrassmannSchur.sBasis_apply]
  rfl

theorem squareCond_Q :
    whiteSystem.SquareCond (k := ℤ) (fun μ b => (schurSign μ b : ℤˣ)) :=
  squareCond_schurSign checker_white

theorem DQ_sK_lima {μ : YoungDiagram} (h : IsLima μ) : DQ (sK μ) = 0 := by
  have := schur_crit_cocycle actsByBoxes_DQ ((whiteSystem_crit_iff μ).mpr h)
  rwa [OddGrassmannSchur.sBasis_apply] at this

/-- The coordinates of a coboundary at a Lima partition vanish. -/
theorem repr_DQ_lima (y : Q) {μ : YoungDiagram} (h : IsLima μ) : sBasis.repr (DQ y) μ = 0 := by
  have e := actsByBoxes_intertwine actsByBoxes_DQ (sBasis.repr y)
  rw [LinearEquiv.symm_apply_apply] at e
  rw [e, LinearEquiv.apply_symm_apply]
  exact whiteSystem.delta_apply_of_crit _ _ ((whiteSystem_crit_iff μ).mpr h)

/-- The Lima Schur function `s_μ` as a cocycle. -/
def limaCocycle (μ : {μ : YoungDiagram // IsLima μ}) : dataQ.cocycles :=
  ⟨sK μ.1, DQ_sK_lima μ.2⟩

/-- The class `[s_μ] ∈ H(OΛ)` of a Lima Schur function. -/
def limaClass (μ : {μ : YoungDiagram // IsLima μ}) : HQ := dataQ.cls (limaCocycle μ)

/-- The Lima part of the coordinates of an element of `OΛ`. -/
def limaCoords (x : Q) : {μ : YoungDiagram // IsLima μ} →₀ ℤ :=
  (sBasis.repr x).subtypeDomain IsLima

theorem limaCoords_apply (x : Q) (μ : {μ : YoungDiagram // IsLima μ}) :
    limaCoords x μ = sBasis.repr x μ.1 := rfl

theorem limaCoords_DQ (y : Q) : limaCoords (DQ y) = 0 := by
  ext μ; exact repr_DQ_lima y μ.2

/-- The class of a cocycle is determined by its coordinates at the Lima partitions:
`[z] = Σ_{λ Lima} z_λ [s_λ]`. -/
theorem cls_eq_sum (z : dataQ.cocycles) :
    dataQ.cls z = (limaCoords (z : Q)).sum (fun μ a => a • limaClass μ) := by
  obtain ⟨y, f, hy⟩ := schur_cocycle_eq actsByBoxes_DQ squareCond_Q (z := (z : Q)) z.2
  -- the combination of Lima Schur functions as a cocycle
  set g : {μ : YoungDiagram // IsLima μ} →₀ ℤ := f.mapDomain whiteCritEquiv
  have hg : ∀ w : {μ : YoungDiagram // IsLima μ} →₀ ℤ,
      ((w.sum (fun μ a => a • limaCocycle μ) : dataQ.cocycles) : Q) =
        w.sum (fun μ a => a • sK μ.1) := by
    intro w
    simp only [Finsupp.sum, AddSubmonoidClass.coe_finsetSum, AddSubgroupClass.coe_zsmul]
    rfl
  have hfg : Finsupp.linearCombination ℤ (fun p : whiteSystem.critSet => sBasis p) f =
      g.sum (fun μ a => a • sK μ.1) := by
    rw [Finsupp.linearCombination_apply, Finsupp.sum_mapDomain_index
      (h := fun (μ : {μ : YoungDiagram // IsLima μ}) (a : ℤ) => a • sK μ.1)
      (fun _ => zero_smul _ _) (fun _ _ _ => add_smul _ _ _)]
    simp only [OddGrassmannSchur.sBasis_apply]
    rfl
  -- `z` and the combination differ by a coboundary
  have hcls : dataQ.cls z = dataQ.cls (g.sum (fun μ a => a • limaCocycle μ)) := by
    rw [SuperDG.Data.cls_eq_iff]
    refine ⟨y, ?_⟩
    rw [hg, ← hfg, hy]
    change DQ y = DQ y + _ - _
    abel
  -- the coordinates of `z` at Lima partitions are `g`
  have hcoord : limaCoords (z : Q) = g := by
    have : g.sum (fun μ a => a • sK μ.1) =
        Finsupp.linearCombination ℤ sBasis (g.mapDomain Subtype.val) := by
      rw [Finsupp.linearCombination_mapDomain, Finsupp.linearCombination_apply]
      simp only [Function.comp_apply, OddGrassmannSchur.sBasis_apply]
    ext μ
    rw [limaCoords_apply, hy, map_add, Finsupp.add_apply, repr_DQ_lima y μ.2, zero_add, hfg,
      this, Module.Basis.repr_linearCombination,
      Finsupp.mapDomain_apply_of_injective Subtype.val_injective]
  rw [hcls, hcoord, map_finsuppSum]
  simp only [map_zsmul]
  rfl

theorem limaClass_linearIndependent : LinearIndependent ℤ limaClass := by
  rw [linearIndependent_iff]
  intro l hl
  have hl' : dataQ.cls (l.sum (fun μ a => a • limaCocycle μ)) = 0 := by
    rw [map_finsuppSum]
    simp only [map_zsmul]
    rw [Finsupp.linearCombination_apply] at hl
    exact hl
  obtain ⟨w, hw⟩ := (SuperDG.Data.cls_eq_zero_iff _ _).mp hl'
  have hsum : ((l.sum (fun μ a => a • limaCocycle μ) : dataQ.cocycles) : Q) =
      Finsupp.linearCombination ℤ (fun p : whiteSystem.critSet => sBasis p)
        (l.mapDomain whiteCritEquiv.symm) := by
    rw [Finsupp.linearCombination_apply, Finsupp.sum_mapDomain_index
      (h := fun (p : whiteSystem.critSet) (a : ℤ) => a • sBasis p)
      (fun _ => zero_smul _ _) (fun _ _ _ => add_smul _ _ _)]
    simp only [Finsupp.sum, AddSubmonoidClass.coe_finsetSum, AddSubgroupClass.coe_zsmul,
      OddGrassmannSchur.sBasis_apply]
    rfl
  have key := schur_independent actsByBoxes_DQ squareCond_Q (y := w) (hsum.symm.trans hw.symm)
  have := congrArg (Finsupp.mapDomain whiteCritEquiv) key
  rwa [Finsupp.mapDomain_zero, ← Finsupp.mapDomain_comp, Equiv.self_comp_symm,
    Finsupp.mapDomain_id] at this

theorem limaClass_span : ⊤ ≤ Submodule.span ℤ (Set.range limaClass) := by
  rintro x -
  obtain ⟨z, rfl⟩ := dataQ.cls_surjective x
  rw [cls_eq_sum]
  exact Submodule.finsuppSum_mem _ _ _ _ fun μ _ =>
    Submodule.smul_mem _ _ (Submodule.subset_span ⟨μ, rfl⟩)

/-- **Proposition A.2 (1)** for the dg algebra `OΛ`: the cohomology ring `H(OΛ)` is a free
abelian group with basis the classes of the Lima Schur functions. -/
noncomputable def HQ_basis : Module.Basis {μ : YoungDiagram // IsLima μ} ℤ HQ :=
  Module.Basis.mk limaClass_linearIndependent limaClass_span

theorem HQ_basis_apply (μ : {μ : YoungDiagram // IsLima μ}) : HQ_basis μ = limaClass μ :=
  Module.Basis.mk_apply _ _ _

/-- Products of Lima classes are given by the odd Littlewood–Richardson coefficients of [E]
at Lima partitions: `[s_μ][s_ν] = Σ_{λ Lima} c^λ_{μν} [s_λ]`. -/
theorem limaClass_mul (μ ν : {μ : YoungDiagram // IsLima μ}) :
    limaClass μ * limaClass ν =
      (limaCoords (sK μ.1 * sK ν.1)).sum (fun lam a => a • limaClass lam) := by
  rw [limaClass, limaClass, ← map_mul]
  exact cls_eq_sum _

theorem limaCoords_sK_mul (μ ν : YoungDiagram) (lam : {μ : YoungDiagram // IsLima μ}) :
    limaCoords (sK μ * sK ν) lam = OddLRTableau.oddLR lam.1 μ ν := rfl

/-! ### Commutativity -/

theorem even_north_of_lima {μ : YoungDiagram} (h : IsLima μ) (i : ℕ) : Even (μ.rowLen i) := by
  obtain ⟨k, hk | hk⟩ := Nat.even_or_odd' i
  · subst hk; exact (h k).1
  · subst hk; rw [(h k).2]; exact (h k).1

theorem eta_lima {μ : YoungDiagram} (h : IsLima μ) : EKLSectionTwo.eta μ = 1 := by
  rw [OddLRMisc.eta_eq_directNorth_north, EKKostkaValues.directNorth_eq_rows,
    OddLRMisc.north_eq_rows]
  apply Even.neg_one_pow
  apply Even.add
  · exact Finset.even_sum _ fun i _ => (even_north_of_lima h i).mul_left _
  · exact Finset.even_sum _ fun i _ => (even_north_of_lima h i).mul_right _

theorem repr_reverse (x : Q) (lam : YoungDiagram) :
    sBasis.repr (EKAutomorphisms.reverseLinear x) lam =
      EKLSectionTwo.eta lam * sBasis.repr x lam := by
  classical
  have key : (Finsupp.lapply lam ∘ₗ sBasis.repr.toLinearMap ∘ₗ EKAutomorphisms.reverseLinear) =
      EKLSectionTwo.eta lam • (Finsupp.lapply lam ∘ₗ sBasis.repr.toLinearMap) := by
    refine sBasis.ext fun κ => ?_
    simp only [LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe,
      Finsupp.lapply_apply, LinearMap.smul_apply, OddGrassmannSchur.sBasis_apply,
      EKLSectionTwo.reverse_sK, map_zsmul, smul_eq_mul]
    rw [← OddGrassmannSchur.sBasis_apply, Module.Basis.repr_self, Finsupp.single_apply]
    split_ifs with hκ
    · subst hκ; rfl
    · rw [mul_zero, mul_zero]
  exact LinearMap.congr_fun key x

/-- For Lima partitions `λ, μ, ν` the odd Littlewood–Richardson coefficients are symmetric:
`c^λ_{μν} = c^λ_{νμ}`. -/
theorem oddLR_comm_of_lima {lam μ ν : YoungDiagram} (hlam : IsLima lam) (hμ : IsLima μ)
    (hν : IsLima ν) : OddLRTableau.oddLR lam μ ν = OddLRTableau.oddLR lam ν μ := by
  have h := repr_reverse (sK μ * sK ν) lam
  rw [EKAutomorphisms.reverse_mul, EKLSectionTwo.reverse_sK, EKLSectionTwo.reverse_sK,
    eta_lima hμ, eta_lima hν, eta_lima hlam, one_smul, one_smul, one_mul] at h
  exact h.symm

theorem limaClass_mul_comm (μ ν : {μ : YoungDiagram // IsLima μ}) :
    limaClass μ * limaClass ν = limaClass ν * limaClass μ := by
  rw [limaClass_mul, limaClass_mul]
  have : limaCoords (sK μ.1 * sK ν.1) = limaCoords (sK ν.1 * sK μ.1) := by
    ext lam
    exact oddLR_comm_of_lima lam.2 μ.2 ν.2
  rw [this]

theorem HQ_mul_comm (x y : HQ) : x * y = y * x := by
  have key : LinearMap.mul ℤ HQ = (LinearMap.mul ℤ HQ).flip := by
    refine LinearMap.ext_basis HQ_basis HQ_basis fun i j => ?_
    simp only [LinearMap.mul_apply', LinearMap.flip_apply, HQ_basis_apply]
    exact limaClass_mul_comm i j
  exact LinearMap.congr_fun₂ key x y

/-- `H(OΛ)` is a commutative ring. -/
instance HQ.instCommRing : CommRing HQ :=
  { (inferInstance : Ring HQ) with mul_comm := HQ_mul_comm }

end

end OddMath.Frontier.EQLima
