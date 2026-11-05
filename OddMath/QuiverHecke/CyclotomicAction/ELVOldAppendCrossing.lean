import OddMath.QuiverHecke.CyclotomicAction.ELVOldAppendSuperfunctor
import OddMath.QuiverHecke.CyclotomicAction.ELVModuleInductionComp
import OddMath.QuiverHecke.CyclotomicAction.ELVModuleInductionTransform
import OddMath.QuiverHecke.CyclotomicAction.ELVAppendBalance
import OddMath.QuiverHecke.CyclotomicAction.ELVPScalarBalance

/-! # The signed equal-colour crossing on double old induction

The full-coefficient last crossing defines a supernatural transformation
of the twice-appended old category. Induction is contravariant in this
transformation. Its transport through the existing even induction-composition
isomorphism, with the prescribed extra minus, is the double-induction
crossing used by DeformedMatrixComparison (2), (4). No presentation relation
or matrix inverse is assumed here.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld.CyclotomicCrossingTensor
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

def equalCrossComponent (i : I) (s : OldCategory D Sc cutoff) :
    ((append D Sc cutoff i) ⋙ (append D Sc cutoff i)).obj s ⟶
      ((append D Sc cutoff i) ⋙ (append D Sc cutoff i)).obj s :=
  (ideal D Sc cutoff _ _).mkQ
    (affineUnit D Sc cutoff _ _ (crossLast D Sc s.word i i))

theorem equalCross_supernatural (i : I) :
    IsSupernatural k (D.parity i * D.parity i)
      (F := (append D Sc cutoff i) ⋙ (append D Sc cutoff i))
      (G := (append D Sc cutoff i) ⋙ (append D Sc cutoff i))
      (equalCrossComponent D Sc cutoff i) := by
  apply IsSupernatural.of_twist
  · intro s
    exact Submodule.mem_map_of_mem
      (ELVPScalar.affineUnit_mem D Sc cutoff (crossLast_mem D Sc s.word i i))
  · intro s t f
    obtain ⟨r, rfl⟩ := (ideal D Sc cutoff s.word t.word).mkQ_surjective f
    have htw : twist k (D.parity i * D.parity i) (X := s) (Y := t)
        (((ideal D Sc cutoff s.word t.word).mkQ r) : s ⟶ t) =
        ((ideal D Sc cutoff s.word t.word).mkQ (twist k (D.parity i * D.parity i) (X := obj D Sc cutoff s.word) (Y := obj D Sc cutoff t.word) r) : s ⟶ t) := by
      rw [twist_apply, oldCategory_proj, oldCategory_proj]
      change (ideal D Sc cutoff s.word t.word).mkQ (proj k 0 r) +
        sign k (D.parity i * D.parity i) • (ideal D Sc cutoff s.word t.word).mkQ (proj k 1 r) =
        (ideal D Sc cutoff s.word t.word).mkQ (twist k (D.parity i * D.parity i) (X := obj D Sc cutoff s.word) (Y := obj D Sc cutoff t.word) r)
      rw [twist_apply, map_add, map_smul]
    rw [htw]
    change (ideal D Sc cutoff (s.word ++ [i] ++ [i]) (t.word ++ [i] ++ [i])).mkQ
      (rightContext D Sc cutoff [i] _ _ (rightContext D Sc cutoff [i] _ _ r) ≫
        affineUnit D Sc cutoff _ _ (crossLast D Sc t.word i i)) =
      (ideal D Sc cutoff (s.word ++ [i] ++ [i]) (t.word ++ [i] ++ [i])).mkQ
        (affineUnit D Sc cutoff _ _ (crossLast D Sc s.word i i) ≫
          rightContext D Sc cutoff [i] _ _
            (rightContext D Sc cutoff [i] _ _ (twist k (D.parity i * D.parity i) (X := obj D Sc cutoff s.word) (Y := obj D Sc cutoff t.word) r)))
    have h := crossLast_comp_rightContext D Sc cutoff i i
      (twist k (D.parity i * D.parity i) (X := obj D Sc cutoff s.word) (Y := obj D Sc cutoff t.word) r)
    rw [twist_twist] at h
    exact congrArg
      (ideal D Sc cutoff (s.word ++ [i] ++ [i]) (t.word ++ [i] ++ [i])).mkQ h.symm

def doubleInductionFunctor (i : I) :
    Superfunctor k (Superfunctor k (OldCategory D Sc cutoff) (SVec k))
      (Superfunctor k (OldCategory D Sc cutoff) (SVec k)) :=
  ⟨BalancedInduction.induction (append D Sc cutoff i) ⋙
    BalancedInduction.induction (append D Sc cutoff i)⟩

/-- The canonical even flattening is used in both directions. -/
def equalCrossOnDoubleInduction (i : I)
    (M : Superfunctor k (OldCategory D Sc cutoff) (SVec k)) :
    (doubleInductionFunctor D Sc cutoff i).obj M ⟶
      (doubleInductionFunctor D Sc cutoff i).obj M :=
  (BalancedInduction.inductionComp (k := k) (append D Sc cutoff i) (append D Sc cutoff i)).hom.app M ≫
    BalancedInduction.transformComponent (equalCross_supernatural D Sc cutoff i) M ≫
      (BalancedInduction.inductionComp (k := k) (append D Sc cutoff i) (append D Sc cutoff i)).inv.app M

theorem equalCrossOnDoubleInduction_supernatural (i : I) :
    IsSupernatural k (D.parity i * D.parity i)
      (F := (doubleInductionFunctor D Sc cutoff i).toFunctor)
      (G := (doubleInductionFunctor D Sc cutoff i).toFunctor)
      (equalCrossOnDoubleInduction D Sc cutoff i) := by
  have hL := isSupernatural_of_natTrans
    (BalancedInduction.inductionComp (k := k) (append D Sc cutoff i) (append D Sc cutoff i)).hom
    (fun M => BalancedInduction.inductionComp_hom_mem
      (append D Sc cutoff i) (append D Sc cutoff i) M)
  have hT := BalancedInduction.transformComponent_supernatural
    (equalCross_supernatural D Sc cutoff i)
  have hR := isSupernatural_of_natTrans
    (BalancedInduction.inductionComp (k := k) (append D Sc cutoff i) (append D Sc cutoff i)).inv
    (fun M => BalancedInduction.inductionComp_inv_mem
      (append D Sc cutoff i) (append D Sc cutoff i) M)
  change IsSupernatural k (D.parity i * D.parity i)
    (F := BalancedInduction.induction (append D Sc cutoff i) ⋙
      BalancedInduction.induction (append D Sc cutoff i))
    (G := BalancedInduction.induction (append D Sc cutoff i) ⋙
      BalancedInduction.induction (append D Sc cutoff i))
    (fun M =>
      (BalancedInduction.inductionComp (k := k) (append D Sc cutoff i)
        (append D Sc cutoff i)).hom.app M ≫
        BalancedInduction.transformComponent (equalCross_supernatural D Sc cutoff i) M ≫
          (BalancedInduction.inductionComp (k := k) (append D Sc cutoff i)
            (append D Sc cutoff i)).inv.app M)
  simpa only [zero_add, add_zero, Category.assoc] using hL.comp (hT.comp hR)

/-- The prescribed extra minus is retained, as in the signed action crossing. -/
def signedEqualInductionCross (i : I) :
    doubleInductionFunctor D Sc cutoff i ⟶ doubleInductionFunctor D Sc cutoff i :=
  -Superfunctor.homMk (equalCrossOnDoubleInduction_supernatural D Sc cutoff i).toSuperNatTrans

@[simp] theorem signedEqualInductionCross_app (i : I) (q : ZMod 2)
    (M : Superfunctor k (OldCategory D Sc cutoff) (SVec k)) :
    (signedEqualInductionCross D Sc cutoff i).app q M =
      if q = D.parity i * D.parity i then -equalCrossOnDoubleInduction D Sc cutoff i M else 0 := by
  rw [signedEqualInductionCross, Superfunctor.neg_app]
  change -(if q = D.parity i * D.parity i then equalCrossOnDoubleInduction D Sc cutoff i M else 0) =
    if q = D.parity i * D.parity i then -equalCrossOnDoubleInduction D Sc cutoff i M else 0
  split_ifs <;> simp

end OddMath.QuiverHecke.ELVOld.CyclotomicCrossingTensor
