/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.ELVParabolicTransport
import OddMath.QuiverHecke.OutputShuffle

/-!
# The ELV ideal-sum decomposition

The output-parabolic transport and the short/long shuffle endpoints give (IS2)
of `DeformedIdealSum.md`. All coefficients and cutoffs are retained over an
arbitrary commutative ground ring. The empty old word falls in the long case.
-/

noncomputable section
open CategoryTheory StringDiagrams Supercategory MonoidalCategory
open scoped TensorProduct
namespace OddMath.QuiverHecke.ELVOld
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

private theorem short_relation_mem (i j : I) (v l t s w : List I)
    (hl : l ≠ []) (es : s = j :: t) (el : s = l ++ [i])
    (F : (pres D Sc).obj (ob D (v ++ [i])) ⟶ (pres D Sc).obj (ob D s))
    (f : (pres D Sc).obj (ob D v) ⟶ (pres D Sc).obj (ob D l))
    (hF : F ≫ eqToHom (congrArg (fun z => (pres D Sc).obj (ob D z)) el) =
      f ▷ (pres D Sc).obj (ob D [i]))
    (c : hom D Sc cutoff s w) :
    affineUnit D Sc cutoff _ _ F ≫
      (eqToHom (congrArg (obj D Sc cutoff) es) ≫ relation D Sc cutoff j t ≫
        eqToHom (congrArg (obj D Sc cutoff) es.symm)) ≫ c ∈
      appendRelations D Sc cutoff i v w := by
  subst s
  cases l with
  | nil => exact (hl rfl).elim
  | cons j' l =>
    have hh := List.cons.inj el
    obtain ⟨rfl, rfl⟩ := hh
    simp only [eqToHom_refl, Category.comp_id] at hF
    change F = affineRightContext D Sc [i] v (j :: l) f at hF
    rw [hF]
    simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
    have H := appendRelations_mem D Sc cutoff i
      (comp_ideal D Sc cutoff (affineUnit D Sc cutoff v (j :: l) f)
        (relation_mem D Sc cutoff j l)) c
    rw [rightContext_comp, rightContext_affineUnit, rightContext_relation] at H
    simp only [Category.assoc] at H
    convert H using 1
    rfl

private theorem long_relation_mem (i j : I) (v t s w : List I)
    (es : s = j :: t) (el : s = i :: v)
    (F : (pres D Sc).obj (ob D (v ++ [i])) ⟶ (pres D Sc).obj (ob D s))
    (hF : F ≫ eqToHom (congrArg (fun z => (pres D Sc).obj (ob D z)) el) =
      lastToFirstHom D Sc i v)
    (c : hom D Sc cutoff s w) :
    affineUnit D Sc cutoff _ _ F ≫
      (eqToHom (congrArg (obj D Sc cutoff) es) ≫ relation D Sc cutoff j t ≫
        eqToHom (congrArg (obj D Sc cutoff) es.symm)) ≫ c ∈
      LinearMap.range (Linear.leftComp k (obj D Sc cutoff w) (appendW D Sc cutoff i v)) := by
  subst s
  obtain ⟨rfl, rfl⟩ := List.cons.inj el
  simp only [eqToHom_refl, Category.comp_id] at hF
  subst F
  refine ⟨c, ?_⟩
  simp only [Linear.leftComp_apply, appendW, eqToHom_refl, Category.id_comp, Category.assoc]

/-- Each output-parabolic ideal term lies in the append-old span plus the moving-strand image.
The short shuffle extends an old relation; the long shuffle factors through `appendW`. -/
theorem parabolic_term_mem_appendRelations_sup_range (i : I) (v w : List I)
    (j : I) (t : List I) (hN : [j].length + t.length = (v ++ [i]).length)
    (x : ShIdx hN) (a : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff)
    (b : hom D Sc cutoff (j :: t) w) :
    (affineUnit D Sc cutoff _ _ (shPsi D Sc [j].length x.1.1) ≫
      shuffleParabolic D Sc cutoff x a) ≫ relation D Sc cutoff j t ≫ b ∈
        appendRelations D Sc cutoff i v w ⊔
          LinearMap.range (Linear.leftComp k (obj D Sc cutoff w) (appendW D Sc cutoff i v)) := by
  obtain ⟨c, hc⟩ := outputParabolic_relation_transport D Sc cutoff x a
  rw [Category.assoc, ← Category.assoc (shuffleParabolic D Sc cutoff x a), hc]
  simp only [Category.assoc]
  have ht : t.length = v.length := by
    simp only [List.length_singleton, List.length_append] at hN
    omega
  obtain ⟨r, hr, he⟩ := OutputShuffle.shuffle_word_cases hN x.1
  rw [ht] at hr
  by_cases hs : r < v.length
  · let e := Categorification.TypeA.wordProd v.length (List.range r)
    have he' : cw (Categorification.TypeA.canWord (v ++ [i]).length x.1.1) =
        cw (Categorification.TypeA.canWord v.length e) := by
      rw [he, OutputShuffle.canWord_wordProd_range hs, OutputShuffle.cw_range]
    apply Submodule.mem_sup_left
    apply short_relation_mem D Sc cutoff i j v
      (shL v 1 e ++ shR v 1 e) (shR (v ++ [i]) 1 x.1.1) _ w
      _ (congrArg (fun l => l ++ shR (v ++ [i]) 1 x.1.1)
        (outputParabolic_first_block x))
      (OutputShuffle.short_target_of_word i v x.1.1 e he')
      (shPsi D Sc 1 x.1.1) (shPsi D Sc 1 e)
      (OutputShuffle.short_eq_of_word D Sc i v x.1.1 e he') (c ≫ b)
    intro hz
    have hh := congrArg List.length hz
    rw [List.length_append, length_shL (by omega : 1 ≤ v.length)] at hh
    simp only [List.length_nil] at hh
    omega
  · have he' : cw (Categorification.TypeA.canWord (v ++ [i]).length x.1.1) =
        crossingDescent v.length := by
      have : r = v.length := by omega
      simpa only [this] using he
    apply Submodule.mem_sup_right
    exact long_relation_mem D Sc cutoff i j v (shR (v ++ [i]) 1 x.1.1) _ w
      (congrArg (fun l => l ++ shR (v ++ [i]) 1 x.1.1) (outputParabolic_first_block x))
      (OutputShuffle.long_target_of_word D Sc i v x.1.1 he')
      (shPsi D Sc 1 x.1.1) (OutputShuffle.long_eq_of_word D Sc i v x.1.1 he') (c ≫ b)

/-- (IS2): containment of the full ELV ideal in the two prescribed summands. -/
theorem ideal_le_appendRelations_sup_range (i : I) (v w : List I) :
    ideal D Sc cutoff (v ++ [i]) w ≤ appendRelations D Sc cutoff i v w ⊔
      LinearMap.range (Linear.leftComp k (obj D Sc cutoff w) (appendW D Sc cutoff i v)) :=
  ideal_le_appendRelations_sup_range_of_parabolic_terms D Sc cutoff i v w
    (parabolic_term_mem_appendRelations_sup_range D Sc cutoff i v w)

/-- The ELV ideal is the sum of the append-old relations and the prescribed moving-strand image. -/
theorem ideal_eq_appendRelations_sup_range (i : I) (v w : List I) :
    ideal D Sc cutoff (v ++ [i]) w = appendRelations D Sc cutoff i v w ⊔
      LinearMap.range (Linear.leftComp k (obj D Sc cutoff w) (appendW D Sc cutoff i v)) := by
  apply le_antisymm (ideal_le_appendRelations_sup_range D Sc cutoff i v w)
  apply sup_le (appendRelations_le_ideal D Sc cutoff i v w)
  rintro _ ⟨b, rfl⟩
  exact ideal_comp D Sc cutoff (appendW_mem_ideal D Sc cutoff i v) b

end OddMath.QuiverHecke.ELVOld
