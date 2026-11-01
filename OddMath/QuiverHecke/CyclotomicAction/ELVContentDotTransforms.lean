/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.ELVContentSuffixCrossingTransform
import OddMath.QuiverHecke.CyclotomicAction.ELVContentTripleDots

/-! # The three independently induced dot families on a content triple -/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
universe u
namespace OddMath.QuiverHecke.ELVOld
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (N : ℕ)

/-- Total evaluation preserves the endomorphism algebra operations, with the
categorical endomorphism-ring order retained on both sides. -/
def supernaturalTotalEndAlgHom
    {C B : Type*} [Category* C] [Category* B]
    [Preadditive C] [Linear k C] [Supercategory k C]
    [Preadditive B] [Linear k B] [Supercategory k B]
    (F : Superfunctor k C B) (M : C) : End F →ₐ[k] End (F.obj M) :=
  AlgHom.ofLinearMap
    { toFun := fun f => f.total M
      map_add' := by
        intro f g
        change (f.app 0 M + g.app 0 M) + (f.app 1 M + g.app 1 M) =
          (f.app 0 M + f.app 1 M) + (g.app 0 M + g.app 1 M)
        abel
      map_smul' := by
        intro r f
        change r • f.app 0 M + r • f.app 1 M = r • (f.app 0 M + f.app 1 M)
        exact (smul_add r _ _).symm }
    (SuperNatTrans.id_total F.toFunctor M)
    (fun f g => by rw [End.mul_def, Superfunctor.comp_total, End.mul_def])

theorem contentTripleLast_target_eq (β : Multiset I) (i j l : I) (γ : Multiset I)
    (h : β + ([i,j,l] : Multiset I) = γ) :
    ((β + ([i] : Multiset I)) + ([j] : Multiset I)) + ([l] : Multiset I) = γ := by
  rw [add_assoc, add_assoc]
  exact h

def contentETripleSuperfunctor (β : Multiset I) (i j l : I) (γ : Multiset I)
    (h : β + ([i,j,l] : Multiset I) = γ) :
    Superfunctor k (ContentModules D Sc cutoff N β) (ContentModules D Sc cutoff N γ) :=
  ⟨contentETripleTo D Sc cutoff N β i j l γ h⟩

section Dots
variable (β : Multiset I) (i j l : I) (γ : Multiset I)
  (h : β + ([i,j,l] : Multiset I) = γ)

def contentTripleFirstDotMorphism (M : ContentModules D Sc cutoff N β) :
    End ((contentETripleTo D Sc cutoff N β i j l γ h).obj M) :=
  (contentEPairTo D Sc cutoff N (β + ([i] : Multiset I)) j l γ
    (contentSuffix_target_eq β i j l γ h)).map
      ((contentInductionDot D Sc cutoff N β i).app (D.parity i) M)

def contentTripleMiddleDotMorphism (M : ContentModules D Sc cutoff N β) :
    End ((contentETripleTo D Sc cutoff N β i j l γ h).obj M) :=
  (contentInductionTo D Sc cutoff N ((β + ([i] : Multiset I)) + ([j] : Multiset I))
    [l] γ (contentTripleLast_target_eq β i j l γ h)).map
      ((contentInductionDot D Sc cutoff N (β + ([i] : Multiset I)) j).app
        (D.parity j) ((contentE D Sc cutoff N β i).obj M))

def contentTripleLastDotMorphism (M : ContentModules D Sc cutoff N β) :
    End ((contentETripleTo D Sc cutoff N β i j l γ h).obj M) :=
  (contentInductionTransform D Sc cutoff N
    (β := (β + ([i] : Multiset I)) + ([j] : Multiset I)) (γ := γ)
    (contentTripleLast_target_eq β i j l γ h) (contentTripleLast_target_eq β i j l γ h)
    (firstDot_parity D Sc l [])).app (D.parity l)
      ((contentE D Sc cutoff N (β + ([i] : Multiset I)) j).obj
        ((contentE D Sc cutoff N β i).obj M))

theorem contentTripleFirstDotMorphism_supernatural :
    IsSupernatural k (D.parity i)
      (fun M => contentTripleFirstDotMorphism D Sc cutoff N β i j l γ h M) :=
  ((contentInductionDot D Sc cutoff N β i).isSupernatural (D.parity i)).whiskerRight
    (contentEPairTo D Sc cutoff N (β + ([i] : Multiset I)) j l γ
      (contentSuffix_target_eq β i j l γ h))

theorem contentTripleMiddleDotMorphism_supernatural :
    IsSupernatural k (D.parity j)
      (fun M => contentTripleMiddleDotMorphism D Sc cutoff N β i j l γ h M) :=
  (((contentInductionDot D Sc cutoff N (β + ([i] : Multiset I)) j).isSupernatural
      (D.parity j)).whiskerLeft (contentE D Sc cutoff N β i)).whiskerRight
    (contentInductionTo D Sc cutoff N ((β + ([i] : Multiset I)) + ([j] : Multiset I))
      [l] γ (contentTripleLast_target_eq β i j l γ h))

theorem contentTripleLastDotMorphism_supernatural :
    IsSupernatural k (D.parity l)
      (fun M => contentTripleLastDotMorphism D Sc cutoff N β i j l γ h M) :=
  ((contentInductionTransform D Sc cutoff N
    (β := (β + ([i] : Multiset I)) + ([j] : Multiset I)) (γ := γ)
    (contentTripleLast_target_eq β i j l γ h) (contentTripleLast_target_eq β i j l γ h)
    (firstDot_parity D Sc l [])).isSupernatural (D.parity l)).whiskerLeft
      (contentE D Sc cutoff N β i ⋙ contentE D Sc cutoff N (β + ([i] : Multiset I)) j)

def contentTripleFirstDotTransform :
    SuperNatTrans k (contentETripleTo D Sc cutoff N β i j l γ h)
      (contentETripleTo D Sc cutoff N β i j l γ h) :=
  (contentTripleFirstDotMorphism_supernatural D Sc cutoff N β i j l γ h).toSuperNatTrans

def contentTripleMiddleDotTransform :
    SuperNatTrans k (contentETripleTo D Sc cutoff N β i j l γ h)
      (contentETripleTo D Sc cutoff N β i j l γ h) :=
  (contentTripleMiddleDotMorphism_supernatural D Sc cutoff N β i j l γ h).toSuperNatTrans

def contentTripleLastDotTransform :
    SuperNatTrans k (contentETripleTo D Sc cutoff N β i j l γ h)
      (contentETripleTo D Sc cutoff N β i j l γ h) :=
  (contentTripleLastDotMorphism_supernatural D Sc cutoff N β i j l γ h).toSuperNatTrans

private theorem homogeneous_family_total
    {C B : Type*} [Category* C] [Category* B]
    [Preadditive C] [Linear k C] [Supercategory k C]
    [Preadditive B] [Linear k B] [Supercategory k B]
    {F G : C ⥤ B} {p : ZMod 2} {x : ∀ M, F.obj M ⟶ G.obj M}
    (hx : IsSupernatural k p x) (M : C) :
    hx.toSuperNatTrans.total M = x M := by
  rcases parity_eq_zero_or_one p with rfl | rfl <;>
    simp [SuperNatTrans.total, IsSupernatural.toSuperNatTrans]

theorem contentTripleFirstDotTransform_total (M : ContentModules D Sc cutoff N β) :
    (contentTripleFirstDotTransform D Sc cutoff N β i j l γ h).total M =
      contentTripleFirstDotMorphism D Sc cutoff N β i j l γ h M :=
  homogeneous_family_total
    (contentTripleFirstDotMorphism_supernatural D Sc cutoff N β i j l γ h) M

theorem contentTripleMiddleDotTransform_total (M : ContentModules D Sc cutoff N β) :
    (contentTripleMiddleDotTransform D Sc cutoff N β i j l γ h).total M =
      contentTripleMiddleDotMorphism D Sc cutoff N β i j l γ h M :=
  homogeneous_family_total
    (contentTripleMiddleDotMorphism_supernatural D Sc cutoff N β i j l γ h) M

theorem contentTripleLastDotTransform_total (M : ContentModules D Sc cutoff N β) :
    (contentTripleLastDotTransform D Sc cutoff N β i j l γ h).total M =
      contentTripleLastDotMorphism D Sc cutoff N β i j l γ h M :=
  homogeneous_family_total
    (contentTripleLastDotMorphism_supernatural D Sc cutoff N β i j l γ h) M

end Dots
end OddMath.QuiverHecke.ELVOld
