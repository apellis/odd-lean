/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.ELVWeightDotBounds
import OddMath.QuiverHecke.CyclotomicAction.ELVWeightSuperAdjunction
import OddMath.SKM.RouquierRightTranspose
import OddMath.SKM.RouquierCoupled

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
universe u v w t
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
  exact H.toFunctor.map_add.symm

private def totalEndRingHom
    {A B : PiSCat.{u, u, u + 1} k} (F : A ⟶ B) (M : A) :
    End F →+* End (F.obj M) where
  toFun f := f.total M
  map_zero' := by
    change (0 : End (F.obj M)) + 0 = 0
    exact add_zero 0
  map_one' := by
    change (𝟙 (F.obj M) : End (F.obj M)) + 0 = (1 : End (F.obj M))
    exact add_zero _
  map_add' f g := by
    change (f.app 0 M + g.app 0 M) + (f.app 1 M + g.app 1 M) =
      (f.app 0 M + f.app 1 M) + (g.app 0 M + g.app 1 M)
    abel
  map_mul' f g := Superfunctor.comp_total g f M

private def componentEndRingHom {J : Type v} (C : J → Type w)
    [∀ a, Category.{t} (C a)] [∀ a, Preadditive (C a)]
    (M : ∀ a, C a) (a : J) : End M →+* End (M a) where
  toFun f := f a
  map_zero' := rfl
  map_one' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl

private theorem end_total_id {A B : PiSCat.{u, u, u + 1} k}
    (F : A ⟶ B) (M : A) :
    (𝟙 F : End F).total M = 𝟙 (F.obj M) := by
  change (𝟙 (F.obj M) : End (F.obj M)) + 0 = 𝟙 _
  exact add_zero _

private theorem end_total_eq_app
    {A B : PiSCat.{u, u, u + 1} k} {F G : A ⟶ B}
    (f : F ⟶ G) (p : ZMod 2) (hf : f ∈ parity (R := k) F G p) (M : A) :
    f.total M = f.app p M := by
  rcases parity_eq_zero_or_one p with rfl | rfl
  · simp only [SuperNatTrans.total,
      Superfunctor.app_eq_zero_of_mem hf (by decide : (1 : ZMod 2) ≠ 0), add_zero]
  · simp only [SuperNatTrans.total,
      Superfunctor.app_eq_zero_of_mem hf (by decide : (0 : ZMod 2) ≠ 1), zero_add]

private theorem cupMapCap_total
    {A B : PiSCat.{u, u, u + 1} k} {E : A ⟶ B} {F : B ⟶ A}
    (η : 𝟙 A ⟶ E ≫ F) (ε : F ≫ E ⟶ 𝟙 B) (f : End E) (N : B) :
    ((rightUnitor F).inv ≫ F ◁ η ≫ (associator F E F).inv ≫
      (F ◁ f ≫ ε) ▷ F ≫ (leftUnitor F).hom).total N =
      η.total (F.obj N) ≫ F.map (f.total (F.obj N) ≫ ε.total N) := by
  erw [Superfunctor.comp_total, Superfunctor.comp_total,
    Superfunctor.comp_total, Superfunctor.comp_total]
  simp only [PiSCat.rightUnitor_inv, PiSCat.associator_inv, PiSCat.leftUnitor_hom]
  erw [end_total_id, end_total_id]
  let a : F.obj N ⟶ F.obj (E.obj (F.obj N)) := (F ◁ η).total N
  let b : F.obj (E.obj (F.obj N)) ⟶ F.obj N := ((F ◁ f ≫ ε) ▷ F).total N
  change 𝟙 (F.obj N) ≫ a ≫ 𝟙 (F.obj (E.obj (F.obj N))) ≫ b ≫ 𝟙 (F.obj N) = _
  simp only [Category.id_comp, Category.comp_id]
  change (F ◁ η).total N ≫ ((F ◁ f ≫ ε) ▷ F).total N = _
  erw [total_whiskerLeft, total_whiskerRight, Superfunctor.comp_total]
  rfl

private theorem adjointTranspose_total
    {A B : PiSCat.{u, u, u + 1} k} {E : A ⟶ B} {F : B ⟶ A}
    (adj : SKM.SuperAdjunction (k := k) E F) (f : End E) (N : B) :
    (SKM.SuperAdjunction.rightTranspose adj adj f).total N =
      adj.unit.total (F.obj N) ≫ F.map (f.total (F.obj N) ≫ adj.counit.total N) := by
  rw [SKM.SuperAdjunction.rightTranspose_apply]
  exact cupMapCap_total adj.unit adj.counit f N

private theorem ringHom_zsmul_pow {R S : Type*} [Ring R] [Ring S]
    (φ : R →+* S) (s : ℤ) (x : R) (n : ℕ) :
    φ (s • x ^ n) = s • (φ x) ^ n := by
  rw [map_zsmul, map_pow]

private theorem transpose_power_zero
    {A B : PiSCat.{u, u, u + 1} k} {E : A ⟶ B} {F : B ⟶ A}
    (adj : SKM.SuperAdjunction (k := k) E F) (d : End E)
    (p : ZMod 2) (hd : d ∈ parity (R := k) _ _ p)
    {S : Type*} [Ring S] (evt : End F →+* S) (n : ℕ)
    (hz : evt (SKM.SuperAdjunction.rightTranspose adj adj (d ^ n)) = 0) :
    (evt (SKM.SuperAdjunction.rightTranspose adj adj d)) ^ n = 0 := by
  have hs := SKM.SuperAdjunction.rightTranspose_power adj hd n
  rw [SKM.rouquierPower_eq_pow, SKM.rouquierPower_eq_pow] at hs
  let s : ℤ := koszulSign p p ^ (n.choose 2)
  have hh : evt (SKM.SuperAdjunction.rightTranspose adj adj (d ^ n)) =
      s • (evt (SKM.SuperAdjunction.rightTranspose adj adj d)) ^ n := by
    calc
      _ = evt (s • (show End F from SKM.SuperAdjunction.rightTranspose adj adj d) ^ n) :=
        congrArg evt hs
      _ = _ := ringHom_zsmul_pow evt s _ n
  rw [hz] at hh
  have hss : s * s = 1 := by
    dsimp [s]
    rw [← mul_pow, koszulSign_mul_self, one_pow]
  calc
    _ = s • (s • ((evt (SKM.SuperAdjunction.rightTranspose adj adj d)) ^ n)) := by
      rw [smul_smul, hss, one_smul]
    _ = 0 := by rw [← hh]; simp

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

private theorem elvDot_total_power_zero
    (M : ELVWeightProduct D Sc cutoff bound Λ x) (δ : WeightBlocks D Λ y) (n : ℕ)
    (hn : (show End (((elvE D Sc cutoff bound i Λ h).obj M) δ) from
      elvWeightDotComponent D Sc cutoff bound i Λ h (D.parity i) M δ) ^ n = 0) :
    ((show End (elvE D Sc cutoff bound i Λ h) from
      elvActionDot D Sc cutoff bound i Λ h) ^ n).total M δ = 0 := by
  let d : End (elvE D Sc cutoff bound i Λ h) := elvActionDot D Sc cutoff bound i Λ h
  let evd : End (elvE D Sc cutoff bound i Λ h) →+*
      End (((elvE D Sc cutoff bound i Λ h).obj M) δ) :=
    (componentEndRingHom
      (fun γ : WeightBlocks D Λ y => ContentModules D Sc cutoff bound γ.1)
      ((elvE D Sc cutoff bound i Λ h).obj M) δ).comp
      (totalEndRingHom (elvE D Sc cutoff bound i Λ h) M)
  change evd (d ^ n) = 0
  rw [map_pow]
  have hv : evd d =
      (show End (((elvE D Sc cutoff bound i Λ h).obj M) δ) from
        elvWeightDotComponent D Sc cutoff bound i Λ h (D.parity i) M δ) := by
    change d.total M δ = _
    rw [end_total_eq_app d (D.parity i) (elvActionDot_mem D Sc cutoff bound i Λ h)]
    rfl
  rw [hv]
  exact hn

private theorem elvTranspose_total_power_zero
    (d : End (elvE D Sc cutoff bound i Λ h)) (p : ZMod 2)
    (hd : d ∈ parity (R := k) _ _ p) (n : ℕ)
    (N : ELVWeightProduct D Sc cutoff bound Λ y) (β : WeightBlocks D Λ x)
    (hz : (d ^ n).total ((elvF D Sc cutoff bound i Λ h).obj N) (blockSucc D Λ i h β) = 0) :
    (show End (((elvF D Sc cutoff bound i Λ h).obj N) β) from
      (SKM.SuperAdjunction.rightTranspose
        (elvActionAdjunction D Sc cutoff bound i Λ h)
        (elvActionAdjunction D Sc cutoff bound i Λ h) d).total N β) ^ n = 0 := by
  let A := elvActionAdjunction D Sc cutoff bound i Λ h
  let evt : End (elvF D Sc cutoff bound i Λ h) →+*
      End (((elvF D Sc cutoff bound i Λ h).obj N) β) :=
    (componentEndRingHom
      (fun γ : WeightBlocks D Λ x => ContentModules D Sc cutoff bound γ.1)
      ((elvF D Sc cutoff bound i Λ h).obj N) β).comp
      (totalEndRingHom (elvF D Sc cutoff bound i Λ h) N)
  have htr := elvTranspose_total_component_zero D Sc cutoff bound i Λ h (d ^ n) N β hz
  change (SKM.SuperAdjunction.rightTranspose A A (d ^ n)).total N β = 0 at htr
  generalize htn : SKM.SuperAdjunction.rightTranspose A A (d ^ n) = tn at htr
  change evt tn = 0 at htr
  rw [← htn] at htr
  have hnil := transpose_power_zero A d p hd evt n htr
  generalize SKM.SuperAdjunction.rightTranspose A A d = t at hnil ⊢
  change (show End (((elvF D Sc cutoff bound i Λ h).obj N) β) from t.total N β) ^ n = 0 at hnil
  exact hnil

/-- One exponent at each source-content block works for every target module
after transposing the chosen dot, with its odd reversal sign retained. -/
theorem elvActionDotTranspose_component_pow_zero [Finite I]
    (hdot : TruncatedAppendDotNilpotent D Sc cutoff bound) (β : WeightBlocks D Λ x) :
    ∃ e : ℕ, 0 < e ∧ ∀ N : ELVWeightProduct D Sc cutoff bound Λ y,
      (show End (((elvF D Sc cutoff bound i Λ h).obj N) β) from
        (elvActionDotTranspose D Sc cutoff bound i Λ h).app (D.parity i) N β) ^ e = 0 := by
  obtain ⟨e, he, hp⟩ := elvWeightDotComponent_pow_zero D Sc cutoff bound i Λ h
    (hdot)
    (blockSucc D Λ i h β)
  refine ⟨e, he, fun N => ?_⟩
  have hz := elvDot_total_power_zero D Sc cutoff bound i Λ h
    ((elvF D Sc cutoff bound i Λ h).obj N) (blockSucc D Λ i h β) e
    (hp ((elvF D Sc cutoff bound i Λ h).obj N))
  have ht := elvTranspose_total_power_zero D Sc cutoff bound i Λ h
    (elvActionDot D Sc cutoff bound i Λ h) (D.parity i)
    (elvActionDot_mem D Sc cutoff bound i Λ h) e N β hz
  let t : End (elvF D Sc cutoff bound i Λ h) := elvActionDotTranspose D Sc cutoff bound i Λ h
  have hmem : t ∈ parity (R := k) _ _ (D.parity i) :=
    elvActionDotTranspose_mem D Sc cutoff bound i Λ h
  change (show End (((elvF D Sc cutoff bound i Λ h).obj N) β) from t.total N β) ^ e = 0 at ht
  simpa only [end_total_eq_app t (D.parity i) hmem] using ht

end OddMath.QuiverHecke.ELVOld

