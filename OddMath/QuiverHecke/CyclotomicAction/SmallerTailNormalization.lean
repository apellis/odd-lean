/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.ELVOutputDotCoordinates
import OddMath.QuiverHecke.CyclotomicAction.AppendContentShortWord
import OddMath.QuiverHecke.CyclotomicAction.ELVPrependDescent

/-!
# Relative shortness by smaller-tail normalization

The bare smaller moving tail, extended by an untouched right strand, lies in
the full short prepend PBW span. Arbitrary old coefficients are reattached
using `replaceOld` and `rebase`, after the bare-tail crossing estimate.
`chronological_scalar_long_zero` and `chronological_scalar_output_stability`
provide actual relative-coset vanishing for `DeformedMackeyBoundary.md` (2).
No total crossing bound on the old coefficient is imposed.
-/

noncomputable section
open CategoryTheory StringDiagrams Categorification.TypeA Equiv MonoidalCategory
open scoped TensorProduct Classical
namespace OddMath.QuiverHecke.SmallerTailNormalization

theorem prepend_length_le (n : ℕ) (u : PrependShuffle n) :
    (canWord (n + 1) u.1⁻¹).length ≤ n := by
  rw [length_canWord, length_eq_invCount]
  have hmono : StrictMono (fun x : Fin n => u.1⁻¹ x.succ) := by
    intro x y hxy
    have he (z : Fin n) : blockEquiv (Nat.add_comm 1 n) (Sum.inr z) = z.succ := by
      apply Fin.ext
      simp [blockEquiv_inr_val, Nat.add_comm]
    simpa only [he] using u.2.2 hxy
  have hsub : invSet (n + 1) u.1⁻¹ ⊆
      Finset.univ.filter (fun p : Fin (n + 1) × Fin (n + 1) => p.1 = 0 ∧ p.2 ≠ 0) := by
    intro p hp
    have hp' := mem_invSet.mp hp
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_, ?_⟩
    · by_contra hn
      obtain ⟨a, ha⟩ := Fin.exists_succ_eq.mpr hn
      have hn' : p.2 ≠ 0 := by intro hz; simp [hz] at hp'
      obtain ⟨b, hb⟩ := Fin.exists_succ_eq.mpr hn'
      rw [← ha, ← hb] at hp'
      exact (not_lt_of_ge (hmono (Fin.succ_lt_succ_iff.mp hp'.1)).le) hp'.2
    · intro hz; simp [hz] at hp'
  have hc : (invSet (n + 1) u.1⁻¹).card ≤
      (Finset.univ.erase (0 : Fin (n + 1))).card := by
    apply Finset.card_le_card_of_injOn Prod.snd
    · intro p hp
      exact Finset.mem_erase.mpr ⟨(Finset.mem_filter.mp (hsub hp)).2.2, Finset.mem_univ _⟩
    · intro p hp q hq he
      apply Prod.ext
      · exact (Finset.mem_filter.mp (hsub hp)).2.1.trans
          (Finset.mem_filter.mp (hsub hq)).2.1.symm
      · exact he
  simpa only [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
    Fintype.card_fin, Nat.add_sub_cancel, invCount] using hc

universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k)

/-- Relative shortness retains arbitrary old input normal forms. -/
def shortSpan (i : I) (s t : List I) :
    Submodule k ((pres D Sc).obj (ob D (i :: s)) ⟶ (pres D Sc).obj (ob D t)) :=
  Submodule.span k (prependBasis D Sc ''
    {x : PrependIdx i s t | x.1.2.2.2 ≠ longPrependShuffle s.length})

/-- Exact coordinate criterion, not a total crossing bound. -/
theorem mem_shortSpan_iff (i : I) (s t : List I)
    (f : (pres D Sc).obj (ob D (i :: s)) ⟶ (pres D Sc).obj (ob D t)) :
    f ∈ shortSpan D Sc i s t ↔
      ∀ x : PrependIdx i s t, x.1.2.2.2 = longPrependShuffle s.length →
        (prependBasis D Sc).repr f x = 0 := by
  rw [shortSpan, Module.Basis.mem_span_image]
  constructor
  · intro h x hx
    by_contra hn
    exact h (Finsupp.mem_support_iff.mpr hn) hx
  · intro h x hx he
    exact Finsupp.mem_support_iff.mp hx (h x he)

/-- The already available absolute low bound implies relative shortness. -/
theorem low_le_shortSpan (i : I) (s t : List I) :
    Low D Sc (i :: s) t s.length ≤ shortSpan D Sc i s t := by
  intro f hf
  exact (mem_shortSpan_iff D Sc i s t f).mpr fun x hx =>
    prependBasis_long_repr_eq_zero_of_low D Sc i s t f hf x hx
/-- Arbitrarily complicated old input coefficients remain short on a fixed short tail.
This isolates the old coefficient before any total-crossing estimate is applied. -/
theorem arbitrary_old_on_short_tail {i : I} {s t : List I}
    (x : PrependIdx i s t) (hx : x.1.2.2.2 ≠ longPrependShuffle s.length)
    (f : (pres D Sc).obj (ob D s) ⟶ (pres D Sc).obj (ob D x.oldTarget)) :
    ELVOld.affineInsert D Sc i s x.oldTarget f ≫ ELVOld.prependTail D Sc x ∈
      shortSpan D Sc i s t := by
  have hf : f ∈ Submodule.span k (Set.range (basisNF D Sc s x.oldTarget)) := by
    rw [Module.Basis.span_eq]
    trivial
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨y, rfl⟩ := hf
    rw [basisNF_apply, ← ELVOld.prependElt_replaceOld]
    apply Submodule.subset_span
    exact ⟨x.replaceOld y, hx, prependBasis_apply D Sc _⟩
  | zero => simp
  | add f g _ _ hf hg =>
    rw [map_add, Preadditive.add_comp]
    exact Submodule.add_mem _ hf hg
  | smul a f _ hf =>
    rw [map_smul, Linear.smul_comp]
    exact Submodule.smul_mem _ a hf

/-- Only the bare smaller tail is bounded; its old coefficient is excluded. -/
theorem extended_prependTail_low {i : I} {s t : List I}
    (x : PrependIdx i s t) (j : I) :
    ELVOld.prependTail D Sc x ▷ (pres D Sc).obj (ob D [j]) ∈
      Low D Sc (i :: (x.oldTarget ++ [j])) (t ++ [j]) (s.length + 1) := by
  unfold ELVOld.prependTail
  rw [cl_whiskerRight D Sc _ _ [j] (fits_append
    (fits_dots (by intro p hp; have he := (List.mem_replicate.mp hp).2; subst p; simp))
    (by simpa only [List.length_cons, PrependIdx.oldTarget, length_tgt]
      using fits_cw (isReduced_canWord (s.length + 1) x.1.2.2.2.1⁻¹).1))]
  apply cl_mem_low
  simp only [crossCount_append, crossCount_dots, crossCount_cw, zero_add]
  exact Nat.lt_succ_of_le (prepend_length_le s.length x.1.2.2.2)

theorem extended_prependTail_short {i : I} {s t : List I}
    (x : PrependIdx i s t) (j : I) :
    ELVOld.prependTail D Sc x ▷ (pres D Sc).obj (ob D [j]) ∈
      shortSpan D Sc i (x.oldTarget ++ [j]) (t ++ [j]) := by
  apply low_le_shortSpan
  have hf := extended_prependTail_low D Sc x j
  change (ELVOld.prependTail D Sc x ▷ (pres D Sc).obj (ob D [j]) :
    (pres D Sc).obj (ob D (i :: (x.oldTarget ++ [j]))) ⟶
      (pres D Sc).obj (ob D (t ++ [j]))) ∈
      Low D Sc (i :: (x.oldTarget ++ [j])) (t ++ [j]) (s.length + 1) at hf
  have hl : (x.oldTarget ++ [j]).length = s.length + 1 := by
    simp only [List.length_append, List.length_singleton, PrependIdx.oldTarget, length_tgt]
  rw [hl]
  exact hf

private theorem insert_tail_transport {i : I} {v t t' w : List I}
    (e : t = t') (r : (pres D Sc).obj (ob D v) ⟶ (pres D Sc).obj (ob D t))
    (f : (pres D Sc).obj (ob D (i :: t)) ⟶ (pres D Sc).obj (ob D w))
    (g : (pres D Sc).obj (ob D (i :: t')) ⟶ (pres D Sc).obj (ob D w))
    (h : HEq f g) :
    ELVOld.affineInsert D Sc i v t r ≫ f =
    ELVOld.affineInsert D Sc i v t' (e ▸ r) ≫ g := by
  subst t'
  cases h
  rfl

theorem rebase_short {i : I} {v s t : List I} (z : PrependIdx i s t)
    (hz : z.1.2.2.2 ≠ longPrependShuffle s.length) (y : NFIdx v z.oldTarget) :
    (z.rebase y).1.2.2.2 ≠ longPrependShuffle v.length := by
  have hl : v.length = s.length := by
    have hh := congrArg List.length y.tgt_cw
    simpa only [length_tgt, PrependIdx.oldTarget] using hh
  change (hl.symm ▸ z.1.2.2.2) ≠ longPrependShuffle v.length
  exact (show ∀ {n m : ℕ} (h : n = m) (u : PrependShuffle m),
      u ≠ longPrependShuffle m → (h.symm ▸ u) ≠ longPrependShuffle n from
    by intro n m h; subst m; exact fun _ h => h) hl _ hz

theorem arbitrary_old_cross_source {i : I} {v s t : List I}
    (z : PrependIdx i s t) (hz : z.1.2.2.2 ≠ longPrependShuffle s.length)
    (r : (pres D Sc).obj (ob D v) ⟶ (pres D Sc).obj (ob D z.oldTarget)) :
    ELVOld.affineInsert D Sc i v z.oldTarget r ≫ ELVOld.prependTail D Sc z ∈
      shortSpan D Sc i v t := by
  by_cases hr : r = 0
  · simp [hr]
  · have hn : Nonempty (NFIdx v z.oldTarget) := by
      by_contra hn
      have : IsEmpty (NFIdx v z.oldTarget) := not_nonempty_iff.mp hn
      apply hr
      apply (basisNF D Sc v z.oldTarget).repr.injective
      ext y
      exact isEmptyElim y
    obtain ⟨y⟩ := hn
    rw [insert_tail_transport D Sc (z.rebase_target y).symm r _ _
      (ELVOld.prependTail_rebase D Sc z y).symm]
    exact arbitrary_old_on_short_tail D Sc (z.rebase y) (rebase_short z hz y) _

theorem old_comp_short {i : I} {v s t : List I}
    (r : (pres D Sc).obj (ob D v) ⟶ (pres D Sc).obj (ob D s))
    (f : (pres D Sc).obj (ob D (i :: s)) ⟶ (pres D Sc).obj (ob D t))
    (hf : f ∈ shortSpan D Sc i s t) :
    ELVOld.affineInsert D Sc i v s r ≫ f ∈ shortSpan D Sc i v t := by
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨z, hz, rfl⟩ := hf
    rw [prependBasis_apply, ELVOld.prependElt_insert_tail, ← Category.assoc]
    have he : ELVOld.affineInsert D Sc i v s r ≫
        ELVOld.affineInsert D Sc i s z.oldTarget z.old.nf =
        ELVOld.affineInsert D Sc i v z.oldTarget (r ≫ z.old.nf) := by
      exact (MonoidalSupercategory.whiskerLeft_comp (R := k) _ _ _).symm
    rw [he]
    exact arbitrary_old_cross_source D Sc z hz _
  | zero => simp
  | add f g _ _ hf hg =>
    rw [Preadditive.comp_add]
    exact Submodule.add_mem _ hf hg
  | smul a f _ hf =>
    rw [Linear.comp_smul]
    exact Submodule.smul_mem _ a hf

/-- Actual scalar chronological generators have no long coefficient. -/
theorem chronological_scalar_short {i j : I} {v s t : List I}
    (r : (pres D Sc).obj (ob D v) ⟶ (pres D Sc).obj (ob D (s ++ [j])))
    (h : (pres D Sc).obj (ob D (i :: s)) ⟶ (pres D Sc).obj (ob D t)) :
    ELVOld.affineInsert D Sc i v (s ++ [j]) r ≫
      (h ▷ (pres D Sc).obj (ob D [j])) ∈ shortSpan D Sc i v (t ++ [j]) := by
  have hh : h ∈ Submodule.span k (Set.range (prependBasis D Sc (i := i) (s := s) (t := t))) := by
    rw [Module.Basis.span_eq]
    trivial
  induction hh using Submodule.span_induction with
  | mem h hh =>
    obtain ⟨x, rfl⟩ := hh
    rw [prependBasis_apply, ELVOld.prependElt_insert_tail]
    erw [MonoidalSupercategory.comp_whiskerRight (R := k), ← Category.assoc]
    have he : ELVOld.affineInsert D Sc i v (s ++ [j]) r ≫
        (ELVOld.affineInsert D Sc i s x.oldTarget x.old.nf ▷ (pres D Sc).obj (ob D [j])) =
        ELVOld.affineInsert D Sc i v (x.oldTarget ++ [j])
          (r ≫ (x.old.nf ▷ (pres D Sc).obj (ob D [j]))) := by
      change ((pres D Sc).obj (ob D [i]) ◁ r) ≫
        (((pres D Sc).obj (ob D [i]) ◁ x.old.nf) ▷ (pres D Sc).obj (ob D [j])) =
        (pres D Sc).obj (ob D [i]) ◁ (r ≫ (x.old.nf ▷ (pres D Sc).obj (ob D [j])))
      erw [MonoidalSupercategory.whiskerLeft_comp (R := k)]
      congr 1
      have hh := MonoidalSupercategory.associator_naturality_middle k
        ((pres D Sc).obj (ob D [i])) x.old.nf ((pres D Sc).obj (ob D [j]))
      change (((pres D Sc).obj (ob D [i]) ◁ x.old.nf) ▷ (pres D Sc).obj (ob D [j])) ≫ 𝟙 _ =
        𝟙 _ ≫ ((pres D Sc).obj (ob D [i]) ◁ (x.old.nf ▷ (pres D Sc).obj (ob D [j]))) at hh
      simp only [Category.comp_id, Category.id_comp] at hh
      exact hh
    rw [he]
    exact old_comp_short D Sc _ _ (extended_prependTail_short D Sc x j)
  | zero =>
    erw [MonoidalSupercategory.zero_whiskerRight k, Limits.comp_zero]
    exact Submodule.zero_mem _
  | add f g _ _ hf hg =>
    erw [MonoidalSupercategory.add_whiskerRight (R := k), Preadditive.comp_add]
    exact Submodule.add_mem _ hf hg
  | smul a f _ hf =>
    erw [MonoidalSupercategory.smul_whiskerRight, Linear.comp_smul]
    exact Submodule.smul_mem _ a hf

/-- The scalar chronological generator is killed by every long PBW coordinate. -/
theorem chronological_scalar_long_zero {i j : I} {v s t : List I}
    (r : (pres D Sc).obj (ob D v) ⟶ (pres D Sc).obj (ob D (s ++ [j])))
    (h : (pres D Sc).obj (ob D (i :: s)) ⟶ (pres D Sc).obj (ob D t))
    (x : PrependIdx i v (t ++ [j]))
    (hx : x.1.2.2.2 = longPrependShuffle v.length) :
    (prependBasis D Sc).repr
      (ELVOld.affineInsert D Sc i v (s ++ [j]) r ≫
        (h ▷ (pres D Sc).obj (ob D [j]))) x = 0 :=
  (mem_shortSpan_iff D Sc i v (t ++ [j]) _).mp
    (chronological_scalar_short D Sc r h) x hx

/-- Output action on the smaller block preserves the exact scalar short summand. -/
theorem chronological_scalar_output_stability {i j : I} {v s t t' : List I}
    (r : (pres D Sc).obj (ob D v) ⟶ (pres D Sc).obj (ob D (s ++ [j])))
    (h : (pres D Sc).obj (ob D (i :: s)) ⟶ (pres D Sc).obj (ob D t))
    (g : (pres D Sc).obj (ob D t) ⟶ (pres D Sc).obj (ob D t')) :
    (ELVOld.affineInsert D Sc i v (s ++ [j]) r ≫
      (h ▷ (pres D Sc).obj (ob D [j]))) ≫
        (g ▷ (pres D Sc).obj (ob D [j])) ∈ shortSpan D Sc i v (t' ++ [j]) := by
  erw [Category.assoc, ← MonoidalSupercategory.comp_whiskerRight (R := k)]
  exact chronological_scalar_short D Sc r (h ≫ g)

end OddMath.QuiverHecke.SmallerTailNormalization

