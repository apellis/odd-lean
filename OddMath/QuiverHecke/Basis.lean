/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.Realization.Leading

/-!
# The basis theorem for the quiver Hecke supercategory

For words `t`, `t'` of colours, the normal forms `x^u ψ_w : t → t'` (dots on the strands of an
increasing list `l`, below the crossings of the canonical reduced word of a permutation `w`)
form a basis of the Hom space of the quiver Hecke supercategory `H` (Brundan–Ellis,
arXiv:1701.04133v2, §11; Kang–Kashiwara–Tsuchioka, arXiv:1107.1039v2, Corollary 3.15), over
any commutative ring.

Spanning is `span_normalForms`. Linear independence uses the polynomial–Clifford
representation: applied to `1 ⊗ 1`, the normal form `x^u ψ_w` has an invertible leading
coefficient at `w` and is otherwise supported on shorter permutations (`Realization.lead`), and
the dot coefficients of distinct increasing lists are linearly independent
(`Realization.mdC_independent`).
-/

noncomputable section
open scoped TensorProduct
open CategoryTheory StringDiagrams Categorification.TypeA
namespace OddMath.QuiverHecke

universe u v w
variable {I : Type u} {X : Type v} [AddCommGroup X] (D : SKM.Datum I X) {k : Type w} [CommRing k]
  (Sc : SKM.Scalars D k)

@[simp] theorem tgt_map_dot (t : List I) (l : List ℕ) : tgt t (l.map PG.dot) = t := by
  induction l with
  | nil => rfl
  | cons p l ih => exact ih

/-- The normal forms `t → t'`: an increasing list of strands for the dots and a permutation
`w` of the strands, whose canonical reduced word goes from `t` to `t'`. -/
def NFIdx (t t' : List I) :=
  {p : List ℕ × Equiv.Perm (Fin t.length) // p.1.Pairwise (· ≤ ·) ∧ (∀ x ∈ p.1, x < t.length) ∧
    SChain t (pl t (p.1.map PG.dot ++ cw (canWord t.length p.2))) t'}

variable {D Sc} in
/-- The normal form `x^l ψ_w` of an index. -/
def NFIdx.nf {t t' : List I} (i : NFIdx t t') :
    (pres D Sc).obj (ob D t) ⟶ (pres D Sc).obj (ob D t') :=
  cl D Sc t t' _ i.2.2.2

theorem span_nf (t t' : List I) :
    Submodule.span k (Set.range fun i : NFIdx t t' => i.nf (D := D) (Sc := Sc)) = ⊤ := by
  rw [← span_normalForms D Sc t t']
  congr 1
  ext f
  constructor
  · rintro ⟨i, rfl⟩
    exact ⟨i.1.1, i.2.1, i.2.2.1, i.1.2, i.2.2.2, rfl⟩
  · rintro ⟨l, hs, hl, w, h, rfl⟩
    exact ⟨⟨(l, w), hs, hl, h⟩, rfl⟩

theorem NFIdx.tgt_cw {t t' : List I} (i : NFIdx t t') :
    tgt t (cw (canWord t.length i.1.2)) = t' := by
  have := tgt_eq i.2.2.2
  rwa [tgt_append, tgt_map_dot] at this

/-- **Linear independence** of the normal forms. -/
theorem linearIndependent_nf (t t' : List I) :
    LinearIndependent k fun i : NFIdx t t' => i.nf (D := D) (Sc := Sc) := by
  classical
  set F := (pres D Sc).lift (Realization.respects D Sc)
  set x₀ : Realization.M k :=
    Finsupp.single 1 ((1 : Realization.K k) ⊗ₜ[k] (1 : Realization.Cl k))
  let ev : ((pres D Sc).obj (ob D t) ⟶ (pres D Sc).obj (ob D t')) →ₗ[k] Realization.M k :=
    { toFun := fun f => (F.map f).hom x₀
      map_add' := fun f g => by simp [F, Functor.map_add]
      map_smul' := fun c f => by simp [F, Functor.map_smul] }
  set ν := Realization.seqOf t
  set mC : List ℕ → Realization.Coeff k := fun l =>
    Realization.mdC D.parity ν l ((1 : Realization.K k) ⊗ₜ[k] (1 : Realization.Cl k))
  have hev : ∀ i : NFIdx t t', ev i.nf = Realization.ldList D Sc 0
      (pl t (cw (canWord t.length i.1.2))) (Realization.sgl ν (Finsupp.single 1 (mC i.1.1)))
        (Realization.seqOf t') := by
    intro i
    show (F.map (cl D Sc t t' _ i.2.2.2)).hom x₀ = _
    rw [Realization.lift_map_cl, pl_append, Realization.ldList_append, Module.End.mul_apply,
      Realization.ldList_dots D Sc t _ i.2.2.1, tgt_map_dot]
    simp [x₀, mC, ν]
  rw [linearIndependent_iff']
  intro s g hg i hi
  by_contra hne
  have hs' : (s.filter fun j => g j ≠ 0).Nonempty := ⟨i, Finset.mem_filter.mpr ⟨hi, hne⟩⟩
  obtain ⟨i₀, hi₀, hmax⟩ := Finset.exists_max_image _ (fun j : NFIdx t t' => length t.length j.1.2) hs'
  rw [Finset.mem_filter] at hi₀
  set w₀ := i₀.1.2
  set W := Realization.extN t.length w₀
  obtain ⟨G, hG, hlead⟩ := Realization.lead D Sc t (isReduced_canWord t.length w₀)
  have hA : ∀ j ∈ s, j.1.2 ≠ w₀ → g j • ev j.nf W = 0 := by
    intro j hj hw
    by_cases hgj : g j = 0
    · simp [hgj]
    obtain ⟨G', -, hl⟩ := Realization.lead D Sc t (isReduced_canWord t.length j.1.2)
    obtain ⟨m, e, -, hsupp⟩ := hl (mC j.1.1)
    rw [hev j, e, NFIdx.tgt_cw]
    simp only [Realization.sgl, Pi.single_eq_same]
    have hlen := hmax j (Finset.mem_filter.mpr ⟨hj, hgj⟩)
    by_contra hW
    rcases hsupp W (fun h0 => hW (by rw [h0, smul_zero])) with h | ⟨u, hu, hlu⟩
    · exact hw (Realization.extN_injective _ (by rw [wordProd_canWord] at h; exact h.symm))
    · rw [← Realization.extN_injective _ hu, length_canWord] at hlu
      omega
  have hB : ∀ j : NFIdx t t', j.1.2 = w₀ → ev j.nf W = G (Realization.perm W (mC j.1.1)) := by
    intro j hw
    obtain ⟨m, e, hv, -⟩ := hlead (mC j.1.1)
    rw [hev j, hw, e]
    have := NFIdx.tgt_cw j
    rw [hw] at this
    rw [this]
    simp only [Realization.sgl, Pi.single_eq_same]
    rw [wordProd_canWord] at hv
    exact hv
  have h1 := congrArg (fun f => ev f W) hg
  simp only [map_sum, map_smul, Finsupp.coe_finsetSum, Finset.sum_apply, Finsupp.coe_smul,
    Pi.smul_apply, map_zero, Finsupp.coe_zero, Pi.zero_apply] at h1
  set s₀ := s.filter fun j => j.1.2 = w₀
  have h1' : ∑ j ∈ s₀, g j • ev j.nf W = 0 := by
    rw [← Finset.sum_filter_add_sum_filter_not s (fun j => j.1.2 = w₀)] at h1
    rwa [Finset.sum_eq_zero (fun j hj => hA j (Finset.mem_filter.mp hj).1
      (Finset.mem_filter.mp hj).2), add_zero] at h1
  have h2 : G (Realization.perm W (∑ j ∈ s₀, g j • mC j.1.1)) = 0 := by
    rw [map_sum, map_sum, ← h1']
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [map_smul, map_smul, hB j (Finset.mem_filter.mp hj).2]
  have h3 : ∑ j ∈ s₀, g j • mC j.1.1 = 0 :=
    Realization.perm_injective W (((Module.End.isUnit_iff G).mp hG).injective
      (h2.trans (map_zero G).symm) |>.trans (map_zero _).symm)
  have h4 := Realization.mdC_independent D.parity ν s₀ (fun j => j.1.1)
    (fun j hj j' hj' e => Subtype.ext (Prod.ext e
      ((Finset.mem_filter.mp hj).2.trans (Finset.mem_filter.mp hj').2.symm)))
    (fun j _ => j.2.1) g h3 i₀ (Finset.mem_filter.mpr ⟨hi₀.1, rfl⟩)
  exact hi₀.2 h4

/-- **The basis theorem** for the quiver Hecke supercategory: the normal forms `x^l ψ_w`
form a basis of every Hom space `t → t'` (Brundan–Ellis, arXiv:1701.04133v2, §11;
Kang–Kashiwara–Tsuchioka, arXiv:1107.1039v2, Corollary 3.15). -/
def basisNF (t t' : List I) :
    Module.Basis (NFIdx t t') k ((pres D Sc).obj (ob D t) ⟶ (pres D Sc).obj (ob D t')) :=
  Module.Basis.mk (linearIndependent_nf D Sc t t') (span_nf D Sc t t').ge

@[simp] theorem basisNF_apply (t t' : List I) (i : NFIdx t t') : basisNF D Sc t t' i = i.nf :=
  Module.Basis.mk_apply _ _ _

end OddMath.QuiverHecke
