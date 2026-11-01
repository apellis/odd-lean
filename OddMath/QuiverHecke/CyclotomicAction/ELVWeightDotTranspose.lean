/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.ELVWeightDotBounds
import OddMath.QuiverHecke.CyclotomicAction.ELVWeightSuperAdjunction
import OddMath.SKM.RouquierRightTranspose

/-! # Fixed-content nilpotence of the actual full-ELV dot transpose

The induction-dot bound at blockSucc β is uniform in the input module.
The actual right transpose uses only that block when evaluated at β.
The reversal sign is retained and cancelled as a unit; no exponent on a whole
weight fibre or additional grading is assumed.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory BicategoryStruct
namespace OddMath.QuiverHecke.ELVOld
open OddMath.QuiverHecke.CyclotomicAction
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (bound : ℕ)
  (i : I) (Λ : X) {x y : X} (h : x + D.α i = y)

private theorem total_whiskerLeft
    {A B C : PiSCat.{u, u, u + 1} k} (F : A ⟶ B)
    {G H : B ⟶ C} (f : G ⟶ H) (M : A) :
    (F ◁ f).total M = f.total (F.obj M) := rfl

private theorem total_whiskerRight
    {A B C : PiSCat.{u, u, u + 1} k} {F G : A ⟶ B}
    (f : F ⟶ G) (H : B ⟶ C) (M : A) :
    (f ▷ H).total M = H.map (f.total M) := by
  change H.map (f.app 0 M) + H.map (f.app 1 M) =
    H.map (f.app 0 M + f.app 1 M)
  exact (H.toFunctor.map_add _ _).symm

private theorem end_total_pow
    {A B : PiSCat.{u, u, u + 1} k} (F : A ⟶ B) (f : End F) (n : ℕ) (M : A) :
    (f ^ n).total M = (show End (F.obj M) from f.total M) ^ n := by
  let ev : End F →* End (F.obj M) := {
    toFun := fun g => g.total M
    map_one' := by simp [SuperNatTrans.total]
    map_mul' := by intro g g'; exact Superfunctor.comp_total g' g M }
  exact ev.map_pow f n

private theorem end_total_zsmul
    {A B : PiSCat.{u, u, u + 1} k} {F G : A ⟶ B}
    (z : ℤ) (f : F ⟶ G) (M : A) :
    (z • f).total M = z • f.total M := by
  simpa only [SuperNatTrans.total, Superfunctor.zsmul_app] using
    (smul_add z (f.app 0 M) (f.app 1 M)).symm

private theorem end_total_eq_app
    {A B : PiSCat.{u, u, u + 1} k} {F G : A ⟶ B}
    (f : F ⟶ G) (p : ZMod 2) (hf : f ∈ parity (R := k) F G p) (M : A) :
    f.total M = f.app p M := by
  rcases parity_eq_zero_or_one p with rfl | rfl
  · simp only [SuperNatTrans.total,
      Superfunctor.app_eq_zero_of_mem hf (by decide : (1 : ZMod 2) ≠ 0), add_zero]
  · simp only [SuperNatTrans.total,
      Superfunctor.app_eq_zero_of_mem hf (by decide : (0 : ZMod 2) ≠ 1), zero_add]

private theorem adjointTranspose_total
    {A B : PiSCat.{u, u, u + 1} k} {E : A ⟶ B} {F : B ⟶ A}
    (adj : SKM.SuperAdjunction (k := k) E F) (f : End E) (N : B) :
    (SKM.SuperAdjunction.rightTranspose adj adj f).total N =
      adj.unit.total (F.obj N) ≫ F.map (f.total (F.obj N) ≫ adj.counit.total N) := by
  rw [SKM.SuperAdjunction.rightTranspose_apply]
  simp only [PiSCat.rightUnitor_inv, PiSCat.associator_inv, PiSCat.leftUnitor_hom]
  erw [Category.id_comp, Category.id_comp, Category.comp_id]
  rw [Superfunctor.comp_total, total_whiskerLeft, total_whiskerRight,
    Superfunctor.comp_total, total_whiskerLeft]

/-- The actual dot transpose through the actual induction/restriction adjunction. -/
abbrev elvActionDotTranspose : End (elvF D Sc cutoff bound i Λ h) :=
  SKM.SuperAdjunction.rightTranspose (elvActionAdjunction D Sc cutoff bound i Λ h)
    (elvActionAdjunction D Sc cutoff bound i Λ h) (elvActionDot D Sc cutoff bound i Λ h)

theorem elvActionDotTranspose_mem :
    elvActionDotTranspose D Sc cutoff bound i Λ h ∈ parity (R := k) _ _ (D.parity i) :=
  SKM.SuperAdjunction.rightTranspose_mem _ _ (elvActionDot_mem D Sc cutoff bound i Λ h)

private theorem elvTranspose_total_component_zero
    (f : End (elvE D Sc cutoff bound i Λ h))
    (N : ELVWeightProduct D Sc cutoff bound Λ y) (β : WeightBlocks D Λ x)
    (hf : f.total ((elvF D Sc cutoff bound i Λ h).obj N)
      (blockSucc D Λ i h β) = 0) :
    (SKM.SuperAdjunction.rightTranspose (elvActionAdjunction D Sc cutoff bound i Λ h)
      (elvActionAdjunction D Sc cutoff bound i Λ h) f).total N β = 0 := by
  rw [adjointTranspose_total]
  change
    (elvActionUnit D Sc cutoff bound i Λ h).total
        ((elvF D Sc cutoff bound i Λ h).obj N) β ≫
      (elvBlockRes D Sc cutoff bound i Λ h β).map
        (f.total ((elvF D Sc cutoff bound i Λ h).obj N) (blockSucc D Λ i h β) ≫
          (elvActionCounit D Sc cutoff bound i Λ h).total N (blockSucc D Λ i h β)) = 0
  rw [hf, Limits.zero_comp]
  simp [Superfunctor.map]

/-- One exponent at each actual source-content block works for every target
module after transposing the chosen dot, with its odd reversal sign retained. -/
theorem elvActionDotTranspose_component_pow_zero [Finite I]
    (sy : SKM.Symmetrizer D) (hc : Sc.Homogeneous) (β : WeightBlocks D Λ x) :
    ∃ e : ℕ, 0 < e ∧ ∀ N : ELVWeightProduct D Sc cutoff bound Λ y,
      (show End (((elvF D Sc cutoff bound i Λ h).obj N) β) from
        (elvActionDotTranspose D Sc cutoff bound i Λ h).app (D.parity i) N β) ^ e = 0 := by
  obtain ⟨e, he, hp⟩ := elvWeightDotComponent_pow_zero D Sc cutoff bound i Λ h sy hc
    (blockSucc D Λ i h β)
  refine ⟨e, he, fun N => ?_⟩
  let A := elvActionAdjunction D Sc cutoff bound i Λ h
  let d : End (elvE D Sc cutoff bound i Λ h) := elvActionDot D Sc cutoff bound i Λ h
  let t : End (elvF D Sc cutoff bound i Λ h) := elvActionDotTranspose D Sc cutoff bound i Λ h
  have hd : d ∈ parity (R := k) _ _ (D.parity i) :=
    elvActionDot_mem D Sc cutoff bound i Λ h
  have ht : t ∈ parity (R := k) _ _ (D.parity i) :=
    elvActionDotTranspose_mem D Sc cutoff bound i Λ h
  have hzero : (d ^ e).total ((elvF D Sc cutoff bound i Λ h).obj N)
      (blockSucc D Λ i h β) = 0 := by
    rw [end_total_pow, end_total_eq_app d (D.parity i) hd]
    exact hp ((elvF D Sc cutoff bound i Λ h).obj N)
  have htr := elvTranspose_total_component_zero D Sc cutoff bound i Λ h
    (d ^ e) N β hzero
  have hs := SKM.SuperAdjunction.rightTranspose_power A hd e
  rw [SKM.rouquierPower_eq_pow, SKM.rouquierPower_eq_pow] at hs
  have hh := congrArg (fun f : End (elvF D Sc cutoff bound i Λ h) => f.total N β) hs
  rw [end_total_zsmul, end_total_pow] at hh
  change
    (SKM.SuperAdjunction.rightTranspose A A (d ^ e)).total N β =
      koszulSign (D.parity i) (D.parity i) ^ (e.choose 2) •
        ((show End (((elvF D Sc cutoff bound i Λ h).obj N) β) from t.total N β) ^ e) at hh
  rw [htr] at hh
  let s : ℤ := koszulSign (D.parity i) (D.parity i) ^ (e.choose 2)
  have hss : s * s = 1 := by
    dsimp [s]
    rw [← mul_pow, koszulSign_mul_self, one_pow]
  have hnil :
      (show End (((elvF D Sc cutoff bound i Λ h).obj N) β) from t.total N β) ^ e = 0 := by
    calc
      _ = s • (s • ((show End (((elvF D Sc cutoff bound i Λ h).obj N) β) from
          t.total N β) ^ e)) := by rw [smul_smul, hss, one_smul]
      _ = 0 := by rw [← hh]; simp
  simpa only [end_total_eq_app t (D.parity i) ht] using hnil

end OddMath.QuiverHecke.ELVOld
