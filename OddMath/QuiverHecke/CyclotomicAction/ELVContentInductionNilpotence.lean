/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.ELVTruncatedNilpotence
import OddMath.QuiverHecke.CyclotomicAction.ELVContentPairWhiskeredRelations

/-! # Nilpotence of the content induction dot

The fixed-content positive-integer-degree bound implies nilpotence of the
independently defined induction dot on arbitrary modules. The induction mate
acts by twisted precomposition, not by the target-word module action. Its
iterates carry the sign proved in `transformLinear_pow_tensor`, with the full
coefficient parity retained. This supplies the dot-nilpotence input of
`DeformedActionAssembly.md` §6; construction of the reservoir action is separate.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld
universe u
namespace BalancedInduction
variable {k : Type u} [CommRing k]
variable {C B : Type u} [Category.{u} C] [Category.{u} B]
  [Preadditive C] [Linear k C] [Supercategory k C]
  [Preadditive B] [Linear k B] [Supercategory k B]
variable {J : C ⥤ B} [J.Additive] [J.Linear k] [IsSuperfunctor k J]

/-- The signed iteration formula transports a common source exponent to all
balanced induction modules. No boundedness of the module is required. -/
theorem transformLinear_pow_zero {p : ZMod 2} {a : ∀ v, End (J.obj v)}
    (ha : IsSupernatural k p a) (n : ℕ) (hn : ∀ v, a v ^ n = 0)
    (M : Superfunctor k C (SVec k)) (w : B) :
    transformLinear ha M w ^ n = 0 := by
  apply hom_ext
  intro v h m
  rw [transformLinear_pow_tensor, hn v, Limits.zero_comp]
  simp [tensor]
/-- Total evaluation preserves endomorphism powers, without a transpose sign. -/
theorem end_total_pow (M : Superfunctor k C (SVec k)) (f : End M) (n : ℕ) (v : C) :
    (f ^ n).total v = (show End (M.obj v) from f.total v) ^ n := by
  induction n with
  | zero => exact SuperNatTrans.id_total _ _
  | succ n ih =>
    rw [pow_succ, End.mul_def, Superfunctor.comp_total, ih, pow_succ, End.mul_def]

/-- Total evaluation detects zero because the two parity summands are independent. -/
theorem end_eq_zero_of_total (M : Superfunctor k C (SVec k)) (f : End M)
    (hf : ∀ v, f.total v = 0) : f = 0 := by
  apply Superfunctor.hom_ext_parity
  · intro v
    have h := congrArg (proj (R := k) 0) (hf v)
    simpa only [SuperNatTrans.total, map_add, map_zero,
      proj_of_mem (f.app_mem 0 v), proj_of_mem_ne (f.app_mem 1 v) (by decide : (1 : ZMod 2) ≠ 0),
      add_zero, Superfunctor.zero_app] using h
  · intro v
    have h := congrArg (proj (R := k) 1) (hf v)
    simpa only [SuperNatTrans.total, map_add, map_zero,
      proj_of_mem (f.app_mem 1 v), proj_of_mem_ne (f.app_mem 0 v) (by decide : (0 : ZMod 2) ≠ 1),
      zero_add, Superfunctor.zero_app] using h

/-- Nilpotence of the entire homogeneous module transformation, not just its
value on a selected parity of vectors. -/
theorem transformComponent_pow_zero {p : ZMod 2} {a : ∀ v, End (J.obj v)}
    (ha : IsSupernatural k p a) (n : ℕ) (hn : ∀ v, a v ^ n = 0)
    (M : Superfunctor k C (SVec k)) :
    (show End (induced J M) from transformComponent ha M) ^ n = 0 := by
  apply end_eq_zero_of_total
  intro w
  rw [end_total_pow]
  have ht : (transformComponent ha M).total w = transformLinear ha M w := by
    rcases parity_eq_zero_or_one p with rfl | rfl <;>
      simp [SuperNatTrans.total, transformComponent_app]
  rw [ht]
  exact transformLinear_pow_zero ha n hn M w
end BalancedInduction

variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)
  (sy : SKM.Symmetrizer D) (hc : Sc.Homogeneous) (N : ℕ)

include sy hc in
/-- One positive exponent works for the actual content-induction dot at every
module and target object, in both parities, at fixed source content. Finite
colours supply the coefficient-degree bound; no global weight bound is claimed. -/
theorem contentInductionDot_pow_zero [Finite I] (ν : List I) (i : I) :
    ∃ e : ℕ, 0 < e ∧ ∀ (M : ContentModules D Sc cutoff N (ν : Multiset I))
      (w : ContentCategory D Sc cutoff N ((ν : Multiset I) + ([i] : Multiset I))),
      let f : End ((contentE D Sc cutoff N (ν : Multiset I) i).obj M |>.obj w) :=
        ((contentInductionDot D Sc cutoff N (ν : Multiset I) i).app (D.parity i) M).app
          (D.parity i) w
      f ^ e = 0 := by
  obtain ⟨e, he, hp⟩ := truncatedAppendDot_pow_zero D Sc cutoff sy hc N ν i
  refine ⟨e, he, fun M w => ?_⟩
  dsimp only
  rw [contentInductionDot_component, BalancedInduction.transformComponent_app, ite_eq_left rfl]
  apply BalancedInduction.transformLinear_pow_zero
  intro v
  have hv : v.obj.word.Perm ν := Multiset.coe_eq_coe.mp v.content
  simpa only [truncatedAppendDot_app, contentAppendToComponent] using hp v.obj hv

include sy hc in
/-- The independently defined content dot is nilpotent as an endomorphism in
the module supercategory, uniformly in the arbitrary input module. -/
theorem contentInductionDot_module_pow_zero [Finite I] (ν : List I) (i : I) :
    ∃ e : ℕ, 0 < e ∧ ∀ M : ContentModules D Sc cutoff N (ν : Multiset I),
      (show End ((contentE D Sc cutoff N (ν : Multiset I) i).obj M) from
        (contentInductionDot D Sc cutoff N (ν : Multiset I) i).app (D.parity i) M) ^ e = 0 := by
  obtain ⟨e, he, hp⟩ := truncatedAppendDot_pow_zero D Sc cutoff sy hc N ν i
  refine ⟨e, he, fun M => ?_⟩
  rw [contentInductionDot_component]
  apply BalancedInduction.transformComponent_pow_zero
  intro v
  have hv : v.obj.word.Perm ν := Multiset.coe_eq_coe.mp v.content
  simpa only [truncatedAppendDot_app, contentAppendToComponent] using hp v.obj hv

include sy hc in
/-- Any ground-scalar normalization, in particular either sign, has the same
uniform exponent. The exterior coefficient algebra is not made commutative. -/
theorem contentInductionDot_smul_pow_zero [Finite I] (ν : List I) (i : I) :
    ∃ e : ℕ, 0 < e ∧ ∀ (c : k) (M : ContentModules D Sc cutoff N (ν : Multiset I)),
      (c • (show End ((contentE D Sc cutoff N (ν : Multiset I) i).obj M) from
        (contentInductionDot D Sc cutoff N (ν : Multiset I) i).app (D.parity i) M)) ^ e = 0 := by
  obtain ⟨e, he, hp⟩ := contentInductionDot_module_pow_zero D Sc cutoff sy hc N ν i
  refine ⟨e, he, fun c M => ?_⟩
  rw [smul_pow, hp M, smul_zero]

end OddMath.QuiverHecke.ELVOld
