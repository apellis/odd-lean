/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.CoveringQuantum.UDot.Triangular
import OddMath.CoveringQuantum.UDot.RhoHalfWords
import Mathlib.RingTheory.TensorProduct.Maps

/-!
# Change of coefficients for the presentation of `U̇_{q,π}(𝔤)`

The covering quantum group of Brundan–Ellis, arXiv:1701.04133v2, §9, is presented over a
commutative ring `k` with parameters `q ∈ kˣ`, `π ∈ k`. A ring homomorphism `f : k → k'` sending
`q ↦ q'` and `π ↦ π'` sends the defining relations (9.2)–(9.4) for `(q, π)` to those for
`(q', π')`. This file constructs the induced ring homomorphism and identifies
`k' ⊗[k] U̇_{q,π}` with `U̇_{q',π'}`. It serves the nondegeneracy statement of
Brundan–Ellis, arXiv:1701.04133v2, Theorem 10.1, by allowing the coefficients to be specialized.

The parameters `q'`, `π'` of the target are separate variables tied to `f` by the equations
`f q = q'` and `f π = π'`.

## Main definitions

* `UDot.freeMap`: the coefficient change on the free algebra.
* `UDot.mapCoeffs`: the induced ring homomorphism `U̇_{q,π} → U̇_{q',π'}`.
* `UDot.baseChangeEquiv`: `k' ⊗[k] U̇_{q,π} ≃ U̇_{q',π'}` as `k'`-algebras.

## Main results

* `UDot.map_qpNat_eq`, `UDot.map_qpInt_eq`, `UDot.map_qpBinom_eq`, `UDot.map_serreCoeff_eq`.
* `UDot.mapCoeffs_one`, `UDot.mapCoeffs_E`, `UDot.mapCoeffs_F`, `UDot.mapCoeffs_smul`,
  `UDot.mapCoeffs_halfWord`, `UDot.mapCoeffs_mem_block`, `UDot.mapCoeffs_mem_modified`,
  `UDot.mapCoeffs_rho`.
-/

noncomputable section

namespace OddMath.CoveringQuantum.UDot

open Finset TensorProduct

variable {k k' I X : Type*} [CommRing k] [CommRing k']
variable (f : k →+* k') {q : kˣ} {π : k} {q' : k'ˣ} {π' : k'}

/-! ### Scalars -/

theorem units_map_eq (hq : f q = q') : Units.map f.toMonoidHom q = q' := Units.ext hq

theorem map_qpNat_eq (hq : f q = q') (hπ : f π = π') (n : ℕ) :
    f (qpNat q π n) = qpNat q' π' n := by
  rw [map_qpNat, units_map_eq f hq, hπ]

theorem map_qpInt_eq (hq : f q = q') (hπ : f π = π') (n : ℤ) :
    f (qpInt q π n) = qpInt q' π' n := by
  rw [map_qpInt, units_map_eq f hq, hπ]

theorem map_qpBinom_eq (hq : f q = q') (hπ : f π = π') (n r : ℕ) :
    f (qpBinom q π n r) = qpBinom q' π' n r := by
  rw [map_qpBinom, units_map_eq f hq, hπ]

theorem map_qi_eq (C : SuperCartanDatum I) (hq : f q = q') (i : I) :
    f (C.qi q i : k) = (C.qi q' i : k') := by
  simp [SuperCartanDatum.qi, hq]

theorem map_pii_eq (C : SuperCartanDatum I) (hπ : f π = π') (i : I) :
    f (C.pii π i) = C.pii π' i := by
  simp [SuperCartanDatum.pii, hπ]

theorem map_serreCoeff_eq (C : SuperCartanDatum I) (hq : f q = q') (hπ : f π = π')
    (i j : I) (r : ℕ) : f (C.serreCoeff q π i j r) = C.serreCoeff q' π' i j r := by
  simp only [SuperCartanDatum.serreCoeff, map_mul, map_pow, map_neg, map_one,
    map_pii_eq f C hπ, map_qpBinom_eq f (map_qi_eq f C hq i) (map_pii_eq f C hπ i)]

theorem map_qp_eq (hq : f q = q') (z : ℤ) : f (qp q z) = qp q' z := by
  simp only [qp, ← units_map_eq f hq, RingHom.toMonoidHom_eq_coe]
  rw [← map_zpow]
  rfl

/-! ### The free algebra -/

/-- Change of coefficients on the free algebra on the generators. -/
def freeMap : Free k I X →+* Free k' I X :=
  letI := f.toAlgebra
  (FreeAlgebra.lift k (FreeAlgebra.ι k' : Gen I X → Free k' I X)).toRingHom

@[simp] theorem freeMap_ι (g : Gen I X) :
    freeMap f (FreeAlgebra.ι k g) = FreeAlgebra.ι k' g := by
  let _ := f.toAlgebra
  exact FreeAlgebra.lift_ι_apply _ _

theorem freeMap_algebraMap (c : k) :
    freeMap f (algebraMap k (Free k I X) c) = algebraMap k' (Free k' I X) (f c) := by
  let _ := f.toAlgebra
  change (FreeAlgebra.lift k (FreeAlgebra.ι k' : Gen I X → Free k' I X)) _ = _
  rw [AlgHom.commutes, IsScalarTower.algebraMap_apply k k' (Free k' I X)]
  rfl

theorem freeMap_smul (c : k) (x : Free k I X) :
    freeMap f (c • x) = f c • freeMap f x := by
  rw [Algebra.smul_def, map_mul, freeMap_algebraMap, ← Algebra.smul_def]


@[simp] theorem freeMap_one (μ : X) : freeMap f (Free.one k μ : Free k I X) = Free.one k' μ :=
  freeMap_ι f _

@[simp] theorem freeMap_E (i : I) (μ : X) : freeMap f (Free.E k i μ : Free k I X) = Free.E k' i μ :=
  freeMap_ι f _

@[simp] theorem freeMap_F (i : I) (μ : X) : freeMap f (Free.F k i μ : Free k I X) = Free.F k' i μ :=
  freeMap_ι f _

variable [AddCommGroup X] (D : RootDatum I X)

@[simp] theorem freeMap_epow (i : I) (n : ℕ) (μ : X) :
    freeMap f (epow (k := k) D i n μ) = epow D i n μ := by
  induction n with
  | zero => simp [epow]
  | succ n ih => simp [epow, ih]

@[simp] theorem freeMap_fpow (i : I) (n : ℕ) (μ : X) :
    freeMap f (fpow (k := k) D i n μ) = fpow D i n μ := by
  induction n with
  | zero => simp [fpow]
  | succ n ih => simp [fpow, ih]

variable [DecidableEq I] [DecidableEq X]

omit [DecidableEq I] [DecidableEq X] in
theorem freeMap_serreE (hq : f q = q') (hπ : f π = π') (i j : I) (μ : X) :
    freeMap f (serreE D q π i j μ) = serreE D q' π' i j μ := by
  simp [serreE, map_sum, freeMap_smul, map_serreCoeff_eq f D.toSuperCartanDatum hq hπ]

omit [DecidableEq I] [DecidableEq X] in
theorem freeMap_serreF (hq : f q = q') (hπ : f π = π') (i j : I) (μ : X) :
    freeMap f (serreF D q π i j μ) = serreF D q' π' i j μ := by
  simp [serreF, map_sum, freeMap_smul, map_serreCoeff_eq f D.toSuperCartanDatum hq hπ]

omit [DecidableEq I] [DecidableEq X] in
theorem freeMap_comm_left (hπ : f π = π') (i j : I) (μ : X) :
    freeMap f (Free.E k i (μ - D.α j) * Free.F k j μ -
        π ^ (D.parity i * D.parity j).val • (Free.F k j (μ + D.α i) * Free.E k i μ) :
        Free k I X) =
      Free.E k' i (μ - D.α j) * Free.F k' j μ -
        π' ^ (D.parity i * D.parity j).val • (Free.F k' j (μ + D.α i) * Free.E k' i μ) := by
  simp [freeMap_smul, hπ]

omit [DecidableEq X] in
theorem freeMap_comm_right (hq : f q = q') (hπ : f π = π') (i j : I) (μ : X) :
    freeMap f (if i = j then qpInt (D.qi q i) (D.pii π i) (D.h i μ) • Free.one k μ else 0 :
        Free k I X) =
      if i = j then qpInt (D.qi q' i) (D.pii π' i) (D.h i μ) • Free.one k' μ else 0 := by
  split_ifs
  · rw [freeMap_smul, freeMap_one,
      map_qpInt_eq f (map_qi_eq f D.toSuperCartanDatum hq i)
        (map_pii_eq f D.toSuperCartanDatum hπ i)]
  · exact map_zero _

omit [AddCommGroup X] [DecidableEq I] in
theorem freeMap_one_one (μ ν : X) :
    freeMap f (if μ = ν then Free.one k μ else 0 : Free k I X) =
      if μ = ν then Free.one k' μ else 0 := by
  split_ifs <;> simp

/-- The coefficient change sends each defining relation for `(q, π)` to the corresponding
relation for `(q', π')`. -/
theorem rel_freeMap (hq : f q = q') (hπ : f π = π') {x y : Free k I X} (h : Rel D q π x y) :
    Rel D q' π' (freeMap f x) (freeMap f y) := by
  cases h with
  | one_one μ ν => rw [freeMap_one_one, map_mul, freeMap_one, freeMap_one]; exact Rel.one_one μ ν
  | one_E i μ => rw [map_mul, freeMap_one, freeMap_E]; exact Rel.one_E i μ
  | E_one i μ => rw [map_mul, freeMap_one, freeMap_E]; exact Rel.E_one i μ
  | one_F i μ => rw [map_mul, freeMap_one, freeMap_F]; exact Rel.one_F i μ
  | F_one i μ => rw [map_mul, freeMap_one, freeMap_F]; exact Rel.F_one i μ
  | comm i j μ =>
    rw [freeMap_comm_left f D hπ, freeMap_comm_right f D hq hπ]; exact Rel.comm i j μ
  | serreE i j μ h => rw [freeMap_serreE f D hq hπ, map_zero]; exact Rel.serreE i j μ h
  | serreF i j μ h => rw [freeMap_serreF f D hq hπ, map_zero]; exact Rel.serreF i j μ h

/-- Every defining relation for `(q', π')` is the image of a defining relation for `(q, π)`. -/
theorem exists_rel_freeMap (hq : f q = q') (hπ : f π = π') {x y : Free k' I X}
    (h : Rel D q' π' x y) :
    ∃ x₀ y₀ : Free k I X, Rel D q π x₀ y₀ ∧ freeMap f x₀ = x ∧ freeMap f y₀ = y := by
  cases h with
  | one_one μ ν =>
    exact ⟨_, _, Rel.one_one μ ν, by rw [map_mul, freeMap_one, freeMap_one], freeMap_one_one f μ ν⟩
  | one_E i μ => exact ⟨_, _, Rel.one_E i μ, by simp, by simp⟩
  | E_one i μ => exact ⟨_, _, Rel.E_one i μ, by simp, by simp⟩
  | one_F i μ => exact ⟨_, _, Rel.one_F i μ, by simp, by simp⟩
  | F_one i μ => exact ⟨_, _, Rel.F_one i μ, by simp, by simp⟩
  | comm i j μ =>
    exact ⟨_, _, Rel.comm i j μ, freeMap_comm_left f D hπ i j μ,
      freeMap_comm_right f D hq hπ i j μ⟩
  | serreE i j μ h =>
    exact ⟨_, _, Rel.serreE i j μ h, freeMap_serreE f D hq hπ i j μ, map_zero _⟩
  | serreF i j μ h =>
    exact ⟨_, _, Rel.serreF i j μ h, freeMap_serreF f D hq hπ i j μ, map_zero _⟩

/-! ### The induced map of covering quantum groups -/

/-- The ring homomorphism `U̇_{q,π} → U̇_{q',π'}` induced by `f : k → k'` with `f q = q'` and
`f π = π'`. -/
def mapCoeffs (hq : f q = q') (hπ : f π = π') :
    CoveringUDot k D q π →+* CoveringUDot k' D q' π' :=
  RingQuot.lift ⟨(mk D q' π').toRingHom.comp (freeMap f), fun _ _ h ↦ by
    simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
    exact mk_rel D q' π' (rel_freeMap f D hq hπ h)⟩

variable {f D}
variable (hq : f q = q') (hπ : f π = π')

theorem mapCoeffs_mk (x : Free k I X) :
    mapCoeffs f D hq hπ (mk D q π x) = mk D q' π' (freeMap f x) := by
  change RingQuot.lift _ ((RingQuot.mkAlgHom k (Rel D q π)).toRingHom x) = _
  have h : (RingQuot.mkAlgHom k (Rel D q π)).toRingHom = RingQuot.mkRingHom _ :=
    RingQuot.mkAlgHom_coe k _
  rw [h, RingQuot.lift_mkRingHom_apply]
  rfl


@[simp] theorem mapCoeffs_one (μ : X) : mapCoeffs f D hq hπ (one D q π μ) = one D q' π' μ := by
  rw [one, mapCoeffs_mk, freeMap_one]; rfl

@[simp] theorem mapCoeffs_E (i : I) (μ : X) :
    mapCoeffs f D hq hπ (E D q π i μ) = E D q' π' i μ := by
  rw [E, mapCoeffs_mk, freeMap_E]; rfl

@[simp] theorem mapCoeffs_F (i : I) (μ : X) :
    mapCoeffs f D hq hπ (F D q π i μ) = F D q' π' i μ := by
  rw [F, mapCoeffs_mk, freeMap_F]; rfl

theorem mapCoeffs_algebraMap (c : k) :
    mapCoeffs f D hq hπ (algebraMap k (CoveringUDot k D q π) c) =
      algebraMap k' (CoveringUDot k' D q' π') (f c) := by
  rw [← (mk D q π).commutes, mapCoeffs_mk, freeMap_algebraMap, (mk D q' π').commutes]

@[simp] theorem mapCoeffs_smul (c : k) (x : CoveringUDot k D q π) :
    mapCoeffs f D hq hπ (c • x) = f c • mapCoeffs f D hq hπ x := by
  rw [Algebra.smul_def, map_mul, mapCoeffs_algebraMap, ← Algebra.smul_def]

@[simp] theorem mapCoeffs_halfGen (positive : Bool) (i : I) (μ : X) :
    mapCoeffs f D hq hπ (halfGen D q π positive i μ) = halfGen D q' π' positive i μ := by
  cases positive <;> simp [halfGen]

@[simp] theorem mapCoeffs_halfWord (positive : Bool) (w : List I) (μ : X) :
    mapCoeffs f D hq hπ (halfWord D q π positive w μ) = halfWord D q' π' positive w μ := by
  induction w with
  | nil => simp [halfWord]
  | cons i w ih => simp [halfWord, ih]

theorem mapCoeffs_mem_block {μ η : X} {x : CoveringUDot k D q π} (hx : x ∈ block D q π μ η) :
    mapCoeffs f D hq hπ x ∈ block D q' π' μ η := by
  constructor
  · rw [← mapCoeffs_one hq hπ, ← map_mul, hx.1]
  · rw [← mapCoeffs_one hq hπ, ← map_mul, hx.2]

theorem mapCoeffs_mem_modified {x : CoveringUDot k D q π} (hx : x ∈ modified D q π) :
    mapCoeffs f D hq hπ x ∈ modified D q' π' := by
  refine Submodule.iSup_induction (fun b : X × X ↦ block D q π b.1 b.2)
    (motive := fun x ↦ mapCoeffs f D hq hπ x ∈ modified D q' π') hx ?_ ?_ ?_
  · intro b x hx
    exact block_le_modified D q' π' b.1 b.2 (mapCoeffs_mem_block hq hπ hx)
  · rw [map_zero]; exact zero_mem _
  · intro x y hx hy
    rw [map_add]; exact add_mem hx hy

/-- The coefficient change commutes with the antiautomorphism `ρ` of (9.8). -/
theorem mapCoeffs_rho (hπ2 : π ^ 2 = 1) (hπ2' : π' ^ 2 = 1) (x : CoveringUDot k D q π) :
    mapCoeffs f D hq hπ (rho D q π hπ2 x).unop =
      (rho D q' π' hπ2' (mapCoeffs f D hq hπ x)).unop := by
  obtain ⟨y, rfl⟩ := mk_surjective D q π x
  induction y using FreeAlgebra.induction with
  | grade0 c =>
    rw [(mk D q π).commutes, mapCoeffs_algebraMap, AlgHom.commutes, AlgHom.commutes,
      MulOpposite.algebraMap_apply, MulOpposite.algebraMap_apply, MulOpposite.unop_op,
      MulOpposite.unop_op, mapCoeffs_algebraMap]
  | grade1 g =>
    cases g with
    | one μ => rw [← Free.one, ← one, rho_one, mapCoeffs_one, rho_one]
    | e i μ => rw [← Free.E, ← E, rho_E, mapCoeffs_smul, mapCoeffs_E, mapCoeffs_F, rho_E,
        map_qp_eq f hq]
    | f i μ => rw [← Free.F, ← F, rho_F, mapCoeffs_smul, mapCoeffs_F, mapCoeffs_E, rho_F,
        map_qp_eq f hq]
  | add a b ha hb => simp only [map_add, MulOpposite.unop_add, ha, hb]
  | mul a b ha hb => simp only [map_mul, MulOpposite.unop_mul, ha, hb]


/-! ### Extension of scalars -/

section BaseChange

variable [Algebra k k'] (D)
variable (hq : algebraMap k k' q = q') (hπ : algebraMap k k' π = π')

/-- `mapCoeffs` along `algebraMap k k'`, as a `k`-algebra homomorphism. -/
def mapCoeffsAlgHom : CoveringUDot k D q π →ₐ[k] CoveringUDot k' D q' π' :=
  { mapCoeffs (algebraMap k k') D hq hπ with
    commutes' := fun c ↦ by
      change mapCoeffs (algebraMap k k') D hq hπ _ = _
      rw [mapCoeffs_algebraMap, ← IsScalarTower.algebraMap_apply] }

@[simp] theorem mapCoeffsAlgHom_apply (x : CoveringUDot k D q π) :
    mapCoeffsAlgHom D hq hπ x = mapCoeffs (algebraMap k k') D hq hπ x := rfl

/-- The inverse of the base change map on the free algebra. -/
def baseChangeInvFree : Free k' I X →ₐ[k'] k' ⊗[k] CoveringUDot k D q π :=
  FreeAlgebra.lift k' fun g ↦ 1 ⊗ₜ mk D q π (FreeAlgebra.ι k g)

theorem baseChangeInvFree_freeMap (x : Free k I X) :
    baseChangeInvFree (q := q) (π := π) D (freeMap (algebraMap k k') x) = 1 ⊗ₜ mk D q π x := by
  induction x using FreeAlgebra.induction with
  | grade0 c =>
    rw [freeMap_algebraMap, AlgHom.commutes, AlgHom.commutes,
      Algebra.TensorProduct.algebraMap_apply,
      Algebra.algebraMap_self, RingHom.id_apply, Algebra.TensorProduct.tmul_one_eq_one_tmul]
  | grade1 g => rw [freeMap_ι]; exact FreeAlgebra.lift_ι_apply _ _
  | add a b ha hb => rw [map_add, map_add, ha, hb, map_add, tmul_add]
  | mul a b ha hb =>
    rw [map_mul, map_mul, ha, hb, map_mul, Algebra.TensorProduct.tmul_mul_tmul, one_mul]

/-- The inverse of the base change map. -/
def baseChangeInv : CoveringUDot k' D q' π' →ₐ[k'] k' ⊗[k] CoveringUDot k D q π :=
  RingQuot.liftAlgHom k' ⟨baseChangeInvFree D, fun _ _ h ↦ by
    obtain ⟨x, y, hr, rfl, rfl⟩ := exists_rel_freeMap (algebraMap k k') D hq hπ h
    rw [baseChangeInvFree_freeMap, baseChangeInvFree_freeMap, mk_rel D q π hr]⟩

theorem baseChangeInv_mk (x : Free k' I X) :
    baseChangeInv D hq hπ (mk D q' π' x) = baseChangeInvFree D x := by
  rw [baseChangeInv, mk, RingQuot.liftAlgHom_mkAlgHom_apply]

theorem baseChangeInv_mapCoeffs (x : CoveringUDot k D q π) :
    baseChangeInv D hq hπ (mapCoeffs (algebraMap k k') D hq hπ x) = 1 ⊗ₜ x := by
  obtain ⟨y, rfl⟩ := mk_surjective D q π x
  rw [mapCoeffs_mk, baseChangeInv_mk]
  exact baseChangeInvFree_freeMap D y

/-- The base change map `k' ⊗[k] U̇_{q,π} → U̇_{q',π'}`. -/
def baseChangeHom : k' ⊗[k] CoveringUDot k D q π →ₐ[k'] CoveringUDot k' D q' π' :=
  Algebra.TensorProduct.lift (Algebra.ofId k' _) (mapCoeffsAlgHom D hq hπ)
    (fun c _ ↦ Algebra.commute_algebraMap_left c _)

theorem baseChangeHom_tmul (c : k') (x : CoveringUDot k D q π) :
    baseChangeHom D hq hπ (c ⊗ₜ x) = c • mapCoeffs (algebraMap k k') D hq hπ x := by
  rw [baseChangeHom, Algebra.TensorProduct.lift_tmul, mapCoeffsAlgHom_apply, Algebra.ofId_apply,
    ← Algebra.smul_def]

/-- Extension of scalars of the covering quantum group:
`k' ⊗[k] U̇_{q,π} ≃ U̇_{q',π'}` as `k'`-algebras. -/
def baseChangeEquiv : k' ⊗[k] CoveringUDot k D q π ≃ₐ[k'] CoveringUDot k' D q' π' :=
  AlgEquiv.ofAlgHom (baseChangeHom D hq hπ) (baseChangeInv D hq hπ)
    (by
      apply RingQuot.ringQuot_ext'
      apply FreeAlgebra.hom_ext
      funext g
      change baseChangeHom D hq hπ (baseChangeInv D hq hπ (mk D q' π' (FreeAlgebra.ι k' g))) =
        mk D q' π' (FreeAlgebra.ι k' g)
      rw [baseChangeInv_mk, baseChangeInvFree, FreeAlgebra.lift_ι_apply, baseChangeHom_tmul,
        one_smul, mapCoeffs_mk, freeMap_ι])
    (by
      apply Algebra.TensorProduct.ext'
      intro c x
      simp only [AlgHom.comp_apply, baseChangeHom_tmul, map_smul, baseChangeInv_mapCoeffs,
        AlgHom.id_apply, smul_tmul', smul_eq_mul, mul_one])

@[simp] theorem baseChangeEquiv_tmul (c : k') (x : CoveringUDot k D q π) :
    baseChangeEquiv D hq hπ (c ⊗ₜ x) = c • mapCoeffs (algebraMap k k') D hq hπ x :=
  baseChangeHom_tmul D hq hπ c x

end BaseChange

end OddMath.CoveringQuantum.UDot
