/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.ELVPDescent
import OddMath.QuiverHecke.CyclotomicAction.ELVQPProduct

/-!
# Moving-chain descent and the signed QP operation

Q is precomposition by the moving chain on the append-old quotient. Its
relation preservation uses the full coefficient parity twist. The composite
with P is the existing signed QP polynomial, including repeated-even factors
−1. These are ground-ring linear maps, not polynomial-module equivalences.
-/

noncomputable section
open CategoryTheory StringDiagrams Supercategory
open scoped TensorProduct
namespace OddMath.QuiverHecke.ELVOld
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

/-- Different word parities have zero full-coefficient Hom space. -/
theorem hom_zero_of_wordParity_ne {v t : List I}
    (hp : wordSumParity D t ≠ wordSumParity D v) (r : hom D Sc cutoff v t) : r = 0 := by
  induction r using TensorProduct.inductionOn with
  | add r s hr hs => simp only [hr, hs, add_zero]
  | tmul a f =>
    have hf : f = 0 := by
      have hle : Submodule.span k {f : (pres D Sc).obj (ob D v) ⟶ (pres D Sc).obj (ob D t) |
          ∃ l : List ℕ, l.Pairwise (· ≤ ·) ∧ (∀ x ∈ l, x < v.length) ∧
            ∃ w : Equiv.Perm (Fin v.length),
              ∃ h, cl D Sc v t (l.map PG.dot ++ cw (Categorification.TypeA.canWord v.length w)) h = f} ≤
          (⊥ : Submodule k _) := by
        apply Submodule.span_le.mpr
        rintro _ ⟨l, -, -, w, h, rfl⟩
        have ht := sChain_target (sChain_pl v
          (l.map PG.dot ++ cw (Categorification.TypeA.canWord v.length w))) h
        exact (hp (by rw [← ht, wordSumParity_tgt])).elim
      rw [span_normalForms D Sc v t] at hle
      exact hle Submodule.mem_top
    simp only [hf, TensorProduct.tmul_zero]

/-- Moving-chain naturality without a word-parity side condition. -/
theorem move_comp_rightContext (i : I) {v t : List I} (r : hom D Sc cutoff v t) :
    move D Sc cutoff i v ≫ rightContext D Sc cutoff [i] v t r =
      insert D Sc cutoff i v t (twist k (D.parity i * wordSumParity D v) r) ≫
        move D Sc cutoff i t := by
  by_cases hp : wordSumParity D t = wordSumParity D v
  · simpa only [twist_twist] using
      (insert_comp_move D Sc cutoff i hp (twist k (D.parity i * wordSumParity D v) r)).symm
  · rw [hom_zero_of_wordParity_ne D Sc cutoff hp r]
    simp only [map_zero, Limits.comp_zero, Limits.zero_comp]

/-- Q carries every append-old relation to a prepend-old relation. -/
theorem move_appendRelations (i : I) {v w : List I}
    {h : hom D Sc cutoff (v ++ [i]) w} (hh : h ∈ appendRelations D Sc cutoff i v w) :
    move D Sc cutoff i v ≫ h ∈ relations D Sc cutoff i v w := by
  induction hh using Submodule.span_induction with
  | mem h hh =>
    obtain ⟨t, r, hr, a, rfl⟩ := hh
    rw [← Category.assoc, move_comp_rightContext, Category.assoc]
    exact Submodule.subset_span ⟨t, _, twist_ideal D Sc cutoff _ hr, _, rfl⟩
  | zero => simp
  | add a b _ _ ha hb =>
    rw [Preadditive.comp_add]
    exact Submodule.add_mem _ ha hb
  | smul c a _ ha =>
    rw [Linear.comp_smul]
    exact Submodule.smul_mem _ c ha

/-- Q on the old-only quotients, with no assumed descent or balance. -/
def qMap (i : I) (v w : List I) :
    AppendTarget D Sc cutoff i v w →ₗ[k] Target D Sc cutoff i v w :=
  (appendRelations D Sc cutoff i v w).mapQ (relations D Sc cutoff i v w)
    (Linear.leftComp k _ (move D Sc cutoff i v))
    (fun _ hh => move_appendRelations D Sc cutoff i hh)

@[simp] theorem qMap_projection (i : I) (v w : List I)
    (h : hom D Sc cutoff (v ++ [i]) w) :
    qMap D Sc cutoff i v w (appendProjection D Sc cutoff i v w h) =
      projection D Sc cutoff i v w
        (affineUnit D Sc cutoff (i :: v) (v ++ [i]) (moveHom D Sc i [] v) ≫ h) := rfl

/-- The literal quotient composite is the signed QP polynomial operation. -/
theorem qMap_pMap_projection (i : I) (v w : List I)
    (h : hom D Sc cutoff (i :: v) w) :
    qMap D Sc cutoff i v w (pMap D Sc cutoff i v w (projection D Sc cutoff i v w h)) =
      projection D Sc cutoff i v w
        ((affineUnit D Sc cutoff _ _ (qpProduct D Sc i v) ≫ relation D Sc cutoff i v) ≫ h) := by
  have he := congrArg (act D Sc cutoff i h) (qp_projection_product D Sc cutoff i v)
  rw [affineUnit_comp D Sc cutoff (v := i :: v) (w := v ++ [i]) (z := i :: v)
    (moveHom D Sc i [] v) (lastToFirstHom D Sc i v)] at he
  simpa only [act_projection, pMap_projection, qMap_projection, Category.assoc] using he

/-- The signed polynomial followed by the full relation preserves the old span. -/
theorem qpProduct_relation_relations (i : I) {v w : List I}
    {h : hom D Sc cutoff (i :: v) w} (hh : h ∈ relations D Sc cutoff i v w) :
    (affineUnit D Sc cutoff _ _ (qpProduct D Sc i v) ≫ relation D Sc cutoff i v) ≫ h ∈
      relations D Sc cutoff i v w := by
  apply (Submodule.Quotient.mk_eq_zero _).mp
  change projection D Sc cutoff i v w _ = 0
  rw [← qMap_pMap_projection]
  have hz : projection D Sc cutoff i v w h = 0 := (Submodule.Quotient.mk_eq_zero _).mpr hh
  rw [hz, map_zero, map_zero]

/-- The existing signed polynomial and full relation, descended to old-only coordinates. -/
def signedQPMap (i : I) (v w : List I) :
    Target D Sc cutoff i v w →ₗ[k] Target D Sc cutoff i v w :=
  (relations D Sc cutoff i v w).mapQ (relations D Sc cutoff i v w)
    (Linear.leftComp k _
      (affineUnit D Sc cutoff _ _ (qpProduct D Sc i v) ≫ relation D Sc cutoff i v))
    (fun _ hh => qpProduct_relation_relations D Sc cutoff i hh)

@[simp] theorem signedQPMap_projection (i : I) (v w : List I)
    (h : hom D Sc cutoff (i :: v) w) :
    signedQPMap D Sc cutoff i v w (projection D Sc cutoff i v w h) =
      projection D Sc cutoff i v w
        ((affineUnit D Sc cutoff _ _ (qpProduct D Sc i v) ≫ relation D Sc cutoff i v) ≫ h) := rfl

/-- Equality of maps on the actual quotients, not just an affine identity. -/
theorem qMap_comp_pMap (i : I) (v w : List I) :
    (qMap D Sc cutoff i v w).comp (pMap D Sc cutoff i v w) =
      signedQPMap D Sc cutoff i v w := by
  apply LinearMap.ext
  intro x
  obtain ⟨h, rfl⟩ := (relations D Sc cutoff i v w).mkQ_surjective x
  exact qMap_pMap_projection D Sc cutoff i v w h

end OddMath.QuiverHecke.ELVOld
