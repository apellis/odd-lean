/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.CoveringQuantum.UDot.BaseChange
import Mathlib.RingTheory.Localization.BaseChange

/-!
# Homomorphisms on the `𝓛`-form through extension of scalars

Brundan–Ellis, arXiv:1701.04133v2, proof of Theorem 11.7 (existence). Let `k → k'` be an
algebra over which `U̇_{q,π}(𝔤)` is defined on both sides, with the `(q_i, π_i)`-factorials units
of `k'`, and let `g : U̇_{q,π}(𝔤)_k → A` be a `k`-algebra homomorphism such that `g(1_λ)`,
`g(e_i^n 1_λ) / [n]!` and `g(f_i^n 1_λ) / [n]!` make sense in a non-unital `k`-algebra `B ⊆ A`.
Extending scalars (`baseHom`), the `𝓛`-form (9.5) of `U̇_{q,π}(𝔤)_{k'}` (with `𝓛 = k`) lands in
`1 ⊗ B ⊆ k' ⊗_k A`. When `B → k' ⊗_k A` is injective (`includeRight_comp_injective`: for instance
`k'` a localization of `k` and `B` without torsion) this gives a homomorphism `lFormHom` from the
`𝓛`-form to `B`, sending `1_λ`, `e_i^{(n)} 1_λ`, `f_i^{(n)} 1_λ` to the given elements of `B`, and
it is the only such homomorphism (`lFormHom_unique`).
-/

noncomputable section
open scoped TensorProduct

namespace OddMath.CoveringQuantum.UDot

variable {k k' I X : Type*} [CommRing k] [CommRing k'] [Algebra k k'] [AddCommGroup X]
  [DecidableEq I] [DecidableEq X] (D : RootDatum I X) {q : kˣ} {π : k} {q' : k'ˣ} {π' : k'}
  (hq : algebraMap k k' q = q') (hπ : algebraMap k k' π = π')
  {A : Type*} [Ring A] [Algebra k A] (g : CoveringUDot k D q π →ₐ[k] A)

/-- Extension of scalars of `g : U̇_{q,π}(𝔤)_k → A` to `U̇_{q,π}(𝔤)_{k'} → k' ⊗_k A`. -/
def baseHom : CoveringUDot k' D q' π' →ₐ[k'] k' ⊗[k] A :=
  (Algebra.TensorProduct.map (AlgHom.id k' k') g).comp (baseChangeInv D hq hπ)

theorem baseHom_freeMap (x : Free k I X) :
    baseHom D hq hπ g (mk D q' π' (freeMap (algebraMap k k') x)) = 1 ⊗ₜ g (mk D q π x) := by
  rw [baseHom, AlgHom.comp_apply, baseChangeInv_mk, baseChangeInvFree_freeMap,
    Algebra.TensorProduct.map_tmul, AlgHom.id_apply]

theorem baseHom_one (μ : X) : baseHom D hq hπ g (one D q' π' μ) = 1 ⊗ₜ g (one D q π μ) := by
  have h := baseHom_freeMap D hq hπ g (Free.one k μ)
  rwa [freeMap_one] at h

omit [DecidableEq I] [DecidableEq X] in
include hq hπ in
theorem algebraMap_qpFact (i : I) (n : ℕ) :
    algebraMap k k' (qpFact (D.qi q i) (D.pii π i) n) = qpFact (D.qi q' i) (D.pii π' i) n := by
  rw [map_qpFact]
  congr 1
  · rw [SuperCartanDatum.qi, SuperCartanDatum.qi, map_pow, units_map_eq _ hq]
  · rw [SuperCartanDatum.pii, SuperCartanDatum.pii, map_pow, hπ]

variable (hu : ∀ i n, IsUnit (qpFact (D.qi q' i) (D.pii π' i) n))

omit [DecidableEq I] [DecidableEq X] in
include hq hπ hu in
theorem inverse_smul_tmul (i : I) (n : ℕ) (a : A) :
    Ring.inverse (qpFact (D.qi q' i) (D.pii π' i) n) •
        ((1 : k') ⊗ₜ[k] (qpFact (D.qi q i) (D.pii π i) n • a)) = (1 : k') ⊗ₜ a := by
  rw [← TensorProduct.smul_tmul, TensorProduct.smul_tmul', Algebra.smul_def (R := k) _ (1 : k'),
    mul_one, algebraMap_qpFact D hq hπ, smul_eq_mul, Ring.inverse_mul_cancel _ (hu i n)]

include hu in
theorem baseHom_edp {i : I} {n : ℕ} {μ : X} {a : A}
    (ha : g (mk D q π (epow D i n μ)) = qpFact (D.qi q i) (D.pii π i) n • a) :
    baseHom D hq hπ g (edp D q' π' i n μ) = 1 ⊗ₜ a := by
  have h := baseHom_freeMap D hq hπ g (epow D i n μ)
  rw [freeMap_epow, ha] at h
  rw [edp, map_smul, h]
  exact inverse_smul_tmul D hq hπ hu i n a

include hu in
theorem baseHom_fdp {i : I} {n : ℕ} {μ : X} {a : A}
    (ha : g (mk D q π (fpow D i n μ)) = qpFact (D.qi q i) (D.pii π i) n • a) :
    baseHom D hq hπ g (fdp D q' π' i n μ) = 1 ⊗ₜ a := by
  have h := baseHom_freeMap D hq hπ g (fpow D i n μ)
  rw [freeMap_fpow, ha] at h
  rw [fdp, map_smul, h]
  exact inverse_smul_tmul D hq hπ hu i n a

theorem baseHom_smul (r : k) (x : CoveringUDot k' D q' π') :
    baseHom D hq hπ g (r • x) = r • baseHom D hq hπ g x := by
  rw [← algebraMap_smul k' r x, map_smul, algebraMap_smul]

/-! ### Restriction to the `𝓛`-form -/

variable {B : Type*} [NonUnitalRing B] [Module k B]
  (j : B →ₙₐ[k] A)

/-- `b ↦ 1 ⊗ j(b)`. -/
abbrev includeB : B →ₙₐ[k] k' ⊗[k] A :=
  (Algebra.TensorProduct.includeRight : A →ₐ[k] k' ⊗[k] A).toNonUnitalAlgHom.comp j

variable {D g j} (o : X → B) (e f : I → ℕ → X → B)
  (ho : ∀ μ, g (one D q π μ) = j (o μ))
  (he : ∀ i n μ, g (mk D q π (epow D i n μ)) = qpFact (D.qi q i) (D.pii π i) n • j (e i n μ))
  (hf : ∀ i n μ, g (mk D q π (fpow D i n μ)) = qpFact (D.qi q i) (D.pii π i) n • j (f i n μ))

include hu ho he hf in
/-- Extension of scalars maps the `𝓛`-form into `1 ⊗ B`. -/
theorem baseHom_mem {x : CoveringUDot k' D q' π'} (hx : x ∈ lForm D q' π' k) :
    baseHom D hq hπ g x ∈ NonUnitalAlgHom.range (includeB (k' := k') j) := by
  induction hx using NonUnitalAlgebra.adjoin_induction with
  | mem x hx =>
    rcases hx with (⟨μ, rfl⟩ | ⟨⟨i, n, μ⟩, rfl⟩) | ⟨⟨i, n, μ⟩, rfl⟩
    · exact (NonUnitalAlgHom.mem_range _).mpr ⟨o μ, ((baseHom_one D hq hπ g μ).trans
        (congrArg _ (ho μ))).symm⟩
    · exact (NonUnitalAlgHom.mem_range _).mpr ⟨e i n μ, (baseHom_edp D hq hπ g hu (he i n μ)).symm⟩
    · exact (NonUnitalAlgHom.mem_range _).mpr ⟨f i n μ, (baseHom_fdp D hq hπ g hu (hf i n μ)).symm⟩
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | zero => rw [map_zero]; exact zero_mem _
  | mul x y _ _ hx hy => rw [map_mul]; exact mul_mem hx hy
  | smul r x _ hx => rw [baseHom_smul]; exact SMulMemClass.smul_mem r hx

/-- The value of the restricted homomorphism. -/
def lFormFun (x : lForm D q' π' k) : B :=
  Classical.choose ((NonUnitalAlgHom.mem_range _).mp (baseHom_mem hq hπ hu o e f ho he hf x.2))

theorem includeB_lFormFun (x : lForm D q' π' k) :
    includeB (k' := k') j (lFormFun hq hπ hu o e f ho he hf x) = baseHom D hq hπ g x :=
  Classical.choose_spec ((NonUnitalAlgHom.mem_range _).mp (baseHom_mem hq hπ hu o e f ho he hf x.2))

variable (hinj : Function.Injective (includeB (k' := k') j))

/-- **The homomorphism on the `𝓛`-form**: `U̇_{q,π}(𝔤)_𝓛 → B`, characterized by
`1 ⊗ lFormHom x = baseHom x`. -/
def lFormHom : lForm D q' π' k →ₙₐ[k] B where
  toFun := lFormFun hq hπ hu o e f ho he hf
  map_smul' r x := hinj (by
    rw [includeB_lFormFun, MonoidHom.id_apply, map_smul, includeB_lFormFun]
    exact baseHom_smul D hq hπ g r x)
  map_zero' := hinj (by
    rw [includeB_lFormFun, map_zero]; exact map_zero _)
  map_add' x y := hinj (by
    rw [includeB_lFormFun, map_add, includeB_lFormFun, includeB_lFormFun]; exact map_add _ _ _)
  map_mul' x y := hinj (by
    rw [includeB_lFormFun, map_mul, includeB_lFormFun, includeB_lFormFun]; exact map_mul _ _ _)

theorem includeB_lFormHom (x : lForm D q' π' k) :
    includeB (k' := k') j (lFormHom hq hπ hu o e f ho he hf hinj x) = baseHom D hq hπ g x :=
  includeB_lFormFun hq hπ hu o e f ho he hf x

theorem lFormHom_one (μ : X) :
    lFormHom hq hπ hu o e f ho he hf hinj ⟨_, one_mem_lForm D q' π' k μ⟩ = o μ :=
  hinj ((includeB_lFormHom hq hπ hu o e f ho he hf hinj _).trans
    ((baseHom_one D hq hπ g μ).trans (congrArg _ (ho μ))))

theorem lFormHom_edp (i : I) (n : ℕ) (μ : X) :
    lFormHom hq hπ hu o e f ho he hf hinj ⟨_, edp_mem_lForm D q' π' k i n μ⟩ = e i n μ :=
  hinj ((includeB_lFormHom hq hπ hu o e f ho he hf hinj _).trans
    (baseHom_edp D hq hπ g hu (he i n μ)))

theorem lFormHom_fdp (i : I) (n : ℕ) (μ : X) :
    lFormHom hq hπ hu o e f ho he hf hinj ⟨_, fdp_mem_lForm D q' π' k i n μ⟩ = f i n μ :=
  hinj ((includeB_lFormHom hq hπ hu o e f ho he hf hinj _).trans
    (baseHom_fdp D hq hπ g hu (hf i n μ)))

/-- Two homomorphisms on the `𝓛`-form agreeing on `1_λ`, `e_i^{(n)} 1_λ`, `f_i^{(n)} 1_λ` are
equal. -/
theorem lForm_hom_ext {D : RootDatum I X} {ψ ψ' : lForm D q' π' k →ₙₐ[k] B}
    (h1 : ∀ μ, ψ ⟨_, one_mem_lForm D q' π' k μ⟩ = ψ' ⟨_, one_mem_lForm D q' π' k μ⟩)
    (h2 : ∀ i n μ, ψ ⟨_, edp_mem_lForm D q' π' k i n μ⟩ = ψ' ⟨_, edp_mem_lForm D q' π' k i n μ⟩)
    (h3 : ∀ i n μ, ψ ⟨_, fdp_mem_lForm D q' π' k i n μ⟩ = ψ' ⟨_, fdp_mem_lForm D q' π' k i n μ⟩) :
    ψ = ψ' := by
  ext ⟨x, hx⟩
  induction hx using NonUnitalAlgebra.adjoin_induction with
  | mem x hx =>
    rcases hx with (⟨μ, rfl⟩ | ⟨⟨i, n, μ⟩, rfl⟩) | ⟨⟨i, n, μ⟩, rfl⟩
    · exact h1 μ
    · exact h2 i n μ
    · exact h3 i n μ
  | add x y hx' hy' hx hy =>
    change ψ (⟨x, hx'⟩ + ⟨y, hy'⟩) = ψ' (⟨x, hx'⟩ + ⟨y, hy'⟩)
    rw [map_add, map_add, hx, hy]
  | zero =>
    change ψ 0 = ψ' 0
    rw [map_zero, map_zero]
  | mul x y hx' hy' hx hy =>
    change ψ (⟨x, hx'⟩ * ⟨y, hy'⟩) = ψ' (⟨x, hx'⟩ * ⟨y, hy'⟩)
    rw [map_mul, map_mul, hx, hy]
  | smul r x hx' hx =>
    change ψ (r • ⟨x, hx'⟩) = ψ' (r • ⟨x, hx'⟩)
    rw [map_smul, map_smul, hx]

/-! ### Injectivity of extension of scalars -/

omit [DecidableEq I] [DecidableEq X] in
/-- If `k'` is a localization of `k` at `M`, `B` has no `M`-torsion and `j` has a `k`-linear
retraction, then `b ↦ 1 ⊗ j(b)` is injective. -/
theorem includeB_injective (M : Submonoid k) [IsLocalization M k'] (r : A →ₗ[k] B)
    (hr : ∀ b, r (j b) = b) (htor : ∀ s ∈ M, ∀ b : B, s • b = 0 → b = 0) :
    Function.Injective (includeB (k' := k') j) := by
  have : IsLocalizedModule M (TensorProduct.mk k k' B 1) :=
    (isLocalizedModule_iff_isBaseChange M k' _).mpr (TensorProduct.isBaseChange _ _ _)
  have hzero : ∀ b, includeB (k' := k') j b = 0 → b = 0 := by
    intro b hb
    have h1 := congrArg (LinearMap.lTensor k' r) hb
    change (1 : k') ⊗ₜ[k] r (j b) = _ at h1
    rw [hr, map_zero] at h1
    obtain ⟨s, hs⟩ := (IsLocalizedModule.eq_zero_iff M (TensorProduct.mk k k' B 1)).mp h1
    exact htor s s.2 b hs
  intro x y h
  rw [← sub_eq_zero]
  exact hzero _ ((map_sub _ x y).trans (sub_eq_zero.mpr h))

end OddMath.CoveringQuantum.UDot
