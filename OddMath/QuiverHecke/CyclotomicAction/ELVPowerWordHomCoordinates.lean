import OddMath.QuiverHecke.CyclotomicAction.ELVPowerWordCoefficients

/-! # Hom coordinates of the chosen E-word value

SwappedVacuumCoordinates §§3–6: transfer the existing regular-power Yoneda
coordinates through the selected native E-word chart, retaining every
content block and the same-weight target word family.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld.PowerWordHomCoordinates
open CyclotomicAction
universe u
section Generic
variable {k C : Type u} [CommRing k] [Category.{u} C] [Preadditive C] [Linear k C] [Supercategory k C]
private def evaluationLinear (M N : Superfunctor k C (SVec k)) (w : C) (b : M.obj w) :
    (M ⟶ N) →ₗ[k] N.obj w where
  toFun f := f.total w b
  map_add' f g := by
    change (f.app 0 w b + g.app 0 w b) + (f.app 1 w b + g.app 1 w b) =
      (f.app 0 w b + f.app 1 w b) + (g.app 0 w b + g.app 1 w b)
    abel
  map_smul' c f := by
    change c • f.app 0 w b + c • f.app 1 w b = c • (f.app 0 w b + f.app 1 w b)
    exact (smul_add _ _ _).symm

private theorem eval_comp {M N P : Superfunctor k C (SVec k)}
    (f : M ⟶ N) (g : N ⟶ P) (w : C) (b : M.obj w) :
    (f ≫ g).total w b = g.total w (f.total w b) := by
  rw [Superfunctor.comp_total, SVec.comp_apply]
private theorem eval_iso_comp {M N P : Superfunctor k C (SVec k)}
    (e : M ≅ N) (f : N ⟶ P) (w : C) (b : N.obj w) :
    (e.hom ≫ f).total w ((moduleIsoLinearEquiv e w).symm b) = f.total w b := by
  rw [eval_comp]
  exact congrArg (f.total w) ((moduleIsoLinearEquiv e w).apply_symm_apply b)
private theorem prepend_square {E : Type*} [Category* E] {A B P : E}
    (e : A ≅ B) (f : B ≅ P) (x : End B) (y : End P)
    (h : x ≫ f.hom = f.hom ≫ y) :
    e.hom ≫ x ≫ f.hom = (e ≪≫ f).hom ≫ y := by
  simpa only [Iso.trans_hom, Category.assoc] using congrArg (fun a => e.hom ≫ a) h
end Generic
private theorem nested_chart_hom {C B E : Type*} [Category* C] [Category* B] [Category* E]
    (J : C ⥤ B) (K : B ⥤ E) {A₀ M₀ : C} {A₁ M₁ : B} {A₂ M₂ : E}
    (h₁ : A₁ = J.obj A₀) (h₂ : A₂ = K.obj A₁) (h₃ : A₂ = K.obj (J.obj A₀))
    (e : A₀ ≅ M₀) (f : J.obj M₀ ≅ M₁) (g : K.obj M₁ ≅ M₂) :
    (eqToIso h₂ ≪≫ K.mapIso (eqToIso h₁ ≪≫ J.mapIso e ≪≫ f) ≪≫ g).hom =
      eqToHom h₃ ≫ ((J ⋙ K).mapIso e ≪≫ K.mapIso f ≪≫ g).hom := by
  cases h₁
  cases h₂
  simp only [eqToIso_refl, Iso.refl_trans, Iso.trans_hom, Functor.mapIso_hom,
    Functor.map_comp, Functor.comp_map, eqToHom_refl, Category.id_comp, Category.assoc]

private theorem prepend_cross_eq {C : Type*} [Category* C] {A B E S T : C}
    (h : A = B) (s : B ≅ S) (t : E ≅ T) (x : B ⟶ E) (y : S ⟶ T)
    (hx : x ≫ t.hom = s.hom ≫ y) :
    eqToHom h ≫ x ≫ t.hom = (eqToHom h ≫ s.hom) ≫ y := by
  simpa only [Category.assoc] using congrArg (fun a => eqToHom h ≫ a) hx

variable {I X k : Type u} [AddCommGroup X] [CommRing k] [Fintype I]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (L : I × ℕ → ℕ)
  (Λ : X) (ν : List I)
local notation "N" => PowerWordContent.powerBound D cutoff L
local notation "Xν" => PowerWordWeight.wordWeight D Λ ν
local notation "WB" => PowerWordWeight.wordBlock D Λ ν
local notation "WO" => PowerWordContentCyclicity.wordObject D Sc cutoff L ν (ν : Multiset I) rfl
local notation "WU" => PowerWordContentCyclicity.wordUnit D Sc cutoff L ν (ν : Multiset I) rfl
local notation "V" => PowerWordEvaluation.value D Sc cutoff L Λ ν
local notation "CH" => PowerWordEvaluation.chart D Sc cutoff L Λ ν

/-- The original word unit transferred through the selected native value chart. -/
def unitVector : ((V) WB).obj WO :=
  (moduleIsoLinearEquiv (Pi.isoApp CH WB) WO).symm WU

/-- Evaluation of a whole native module map at the selected cyclic unit. -/
def evaluate (Y : ELVWeightProduct D Sc cutoff N Λ Xν) :
    (V ⟶ Y) →ₗ[k] (Y WB).obj WO :=
  (evaluationLinear (V WB) (Y WB) WO (unitVector D Sc cutoff L Λ ν)).comp (LinearMap.proj WB)

/-- The selected unit detects every whole map out of the literal E-word
value; off-support blocks are included by the proved support theorem. -/
theorem evaluate_injective (Y : ELVWeightProduct D Sc cutoff N Λ Xν) :
    Function.Injective (evaluate D Sc cutoff L Λ ν Y) := by
  intro f g h
  have he : (CH).inv ≫ f = (CH).inv ≫ g := by
    funext δ
    classical
    by_cases hδ : δ = WB
    · subst δ
      apply PowerWordContentCyclicity.hom_ext D Sc cutoff L ν (ν : Multiset I) rfl (Y WB)
      change ((Pi.isoApp CH WB).inv ≫ f WB).total WO WU =
        ((Pi.isoApp CH WB).inv ≫ g WB).total WO WU
      rw [eval_comp, eval_comp]
      exact h
    · have hv : δ.1 ≠ (ν : Multiset I) := fun hv => hδ (Subtype.ext hv)
      exact (PowerWordWeight.wordAt_isZero D Sc cutoff L ν δ.1 hv).eq_of_src _ _
  have hh := congrArg (fun a => (CH).hom ≫ a) he
  simpa only [Category.assoc, Iso.hom_inv_id_assoc] using hh

/-- Every vector in the same-weight target word family is attained, using
the existing old-word generator and its already constructed module map. -/
theorem evaluate_surjective (τ : List I) :
    Function.Surjective (evaluate D Sc cutoff L Λ ν (PowerWordWeight.wordFamily D Sc cutoff L Λ Xν τ)) := by
  intro v
  obtain ⟨g, hg⟩ := PowerWordContentCyclicity.generator_surjective D Sc cutoff L τ (ν : Multiset I) WO v
  refine ⟨(CH).hom ≫ PowerWordWeightWhiskering.wordFamilyArrow D Sc cutoff L Λ Xν ν τ g, ?_⟩
  have hu := eval_iso_comp (Pi.isoApp CH WB)
    ((PowerWordWeightWhiskering.wordFamilyArrow D Sc cutoff L Λ Xν ν τ g) WB) WO WU
  have hc := PowerWordContentCross.contentWordArrow_unit D Sc cutoff L (ν : Multiset I) ν τ rfl g
  exact (hu.trans hc).trans hg

/-- Whole native Hom coordinates, as the direct selected-chart wrapper of
the established power-word Yoneda and generator results. The target is the
explicit same-weight word family, with no new action or quotient. -/
def homEquiv (τ : List I) :
    (V ⟶ PowerWordWeight.wordFamily D Sc cutoff L Λ Xν τ) ≃ₗ[k]
      (PowerWordWeight.wordAt D Sc cutoff L τ (ν : Multiset I)).obj WO :=
  LinearEquiv.ofBijective (evaluate D Sc cutoff L Λ ν (PowerWordWeight.wordFamily D Sc cutoff L Λ Xν τ))
    ⟨evaluate_injective D Sc cutoff L Λ ν _, evaluate_surjective D Sc cutoff L Λ ν τ⟩

/-- The coordinate is literal evaluation at the selected cyclic unit. -/
theorem homEquiv_apply (τ : List I) (f : V ⟶ PowerWordWeight.wordFamily D Sc cutoff L Λ Xν τ) :
    homEquiv D Sc cutoff L Λ ν τ f = (f WB).total WO (unitVector D Sc cutoff L Λ ν) := rfl

/-- The existing signed old-Hom map has its original full generator as
native Hom coordinate, without changing the action or its quotient. -/
theorem homEquiv_from_old (τ : List I)
    (g : (OldCategory.mk τ : OldCategory D Sc cutoff) ⟶ OldCategory.mk ν) :
    homEquiv D Sc cutoff L Λ ν τ
      ((CH).hom ≫ PowerWordWeightWhiskering.wordFamilyArrow D Sc cutoff L Λ Xν ν τ g) =
    PowerWordContentCyclicity.generator D Sc cutoff L τ (ν : Multiset I) WO g := by
  have hu := eval_iso_comp (Pi.isoApp CH WB)
    ((PowerWordWeightWhiskering.wordFamilyArrow D Sc cutoff L Λ Xν ν τ g) WB) WO WU
  exact hu.trans (PowerWordContentCross.contentWordArrow_unit D Sc cutoff L (ν : Multiset I) ν τ rfl g)

/-- The genuine A/T insertion on the native E-word value has the literal
coefficient endomorphism coordinate. The coefficient may be inhomogeneous. -/
theorem homEquiv_coefficient (a : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) :
    homEquiv D Sc cutoff L Λ ν ν
      (PowerWordCoefficients.coefficientValue D Sc cutoff L Λ
        ((coefficientPowerIdeal D cutoff (elementaryCoefficients (k := k) D cutoff) L).ringCon.mkₐ k a) ν ≫
        (CH).hom) =
    PowerWordContentCyclicity.generator D Sc cutoff L ν (ν : Multiset I) WO
      (coefficientEndomorphism D Sc cutoff ν a) := by
  rw [PowerWordCoefficients.coefficient_value]
  exact homEquiv_from_old D Sc cutoff L Λ ν ν _

/-- The given dot on the next native E value has the original old-dot
coordinate in the whole Hom chart. -/
theorem homEquiv_dot (i : I) :
    homEquiv D Sc cutoff L Λ (ν ++ [i]) (ν ++ [i])
      ((eqToIso (PowerWordEvaluation.value_append D Sc cutoff L Λ ν i)).hom ≫
        (elvActionDot D Sc cutoff N i Λ (PowerWordWeight.wordWeight_append D Λ ν i)).app (D.parity i)
          (PowerWordEvaluation.value D Sc cutoff L Λ ν) ≫
        (PowerWordEvaluation.appendChart D Sc cutoff L Λ ν i).hom) =
    PowerWordContentCyclicity.generator D Sc cutoff L (ν ++ [i]) ((ν ++ [i] : List I) : Multiset I)
      (PowerWordContentCyclicity.wordObject D Sc cutoff L (ν ++ [i]) ((ν ++ [i] : List I) : Multiset I) rfl)
      (CyclotomicCrossingTensor.oldAppendDotComponent D Sc cutoff i (OldCategory.mk ν)) := by
  have hChart : PowerWordEvaluation.chart D Sc cutoff L Λ (ν ++ [i]) =
      eqToIso (PowerWordEvaluation.value_append D Sc cutoff L Λ ν i) ≪≫
        PowerWordEvaluation.appendChart D Sc cutoff L Λ ν i :=
    PowerWordEvaluation.chart_append D Sc cutoff L Λ ν i
  have hDot := prepend_square (eqToIso (PowerWordEvaluation.value_append D Sc cutoff L Λ ν i))
    (PowerWordEvaluation.appendChart D Sc cutoff L Λ ν i) _ _
    (PowerWordEvaluation.dot_append_value D Sc cutoff L Λ ν i)
  rw [← hChart] at hDot
  have hY : PowerWordWeightDot.wordFamilyDot D Sc cutoff L Λ ν i =
      PowerWordWeightWhiskering.wordFamilyArrow D Sc cutoff L Λ
        (PowerWordWeight.wordWeight D Λ (ν ++ [i])) (ν ++ [i]) (ν ++ [i])
        (CyclotomicCrossingTensor.oldAppendDotComponent D Sc cutoff i (OldCategory.mk ν)) := rfl
  rw [hY] at hDot
  rw [hDot]
  exact homEquiv_from_old D Sc cutoff L Λ (ν ++ [i]) (ν ++ [i]) _

private theorem value_pair (i j : I) :
    PowerWordEvaluation.value D Sc cutoff L Λ ((ν ++ [j]) ++ [i]) =
      (elvEFunctor D Sc cutoff N j Λ (PowerWordWeight.wordWeight_append D Λ ν j) ⋙
        elvEFunctor D Sc cutoff N i Λ (PowerWordWeight.wordWeight_append D Λ (ν ++ [j]) i)).obj V :=
  (PowerWordEvaluation.value_append D Sc cutoff L Λ (ν ++ [j]) i).trans
    (congrArg (elvEFunctor D Sc cutoff N i Λ (PowerWordWeight.wordWeight_append D Λ (ν ++ [j]) i)).obj
      (PowerWordEvaluation.value_append D Sc cutoff L Λ ν j))

private theorem recursivePair_canonical (i j : I) :
    PowerWordWeightCross.recursivePairIso D Sc cutoff L Λ ν i j rfl
      (PowerWordWeight.wordWeight_append D Λ ν j) (PowerWordWeight.wordWeight_append D Λ (ν ++ [j]) i) =
    (elvEFunctor D Sc cutoff N i Λ (PowerWordWeight.wordWeight_append D Λ (ν ++ [j]) i)).mapIso
      (PowerWordWeight.weightAppendIso D Sc cutoff L Λ ν j) ≪≫
        PowerWordWeight.weightAppendIso D Sc cutoff L Λ (ν ++ [j]) i := rfl

private theorem chart_pair_hom (i j : I) :
    (PowerWordEvaluation.chart D Sc cutoff L Λ ((ν ++ [j]) ++ [i])).hom =
      eqToHom (value_pair D Sc cutoff L Λ ν i j) ≫
        (PowerWordEvaluation.pairChart D Sc cutoff L Λ ν i j
          (PowerWordWeight.wordWeight_append D Λ ν j) (PowerWordWeight.wordWeight_append D Λ (ν ++ [j]) i)).hom := by
  have hh := nested_chart_hom
    (elvEFunctor D Sc cutoff N j Λ (PowerWordWeight.wordWeight_append D Λ ν j))
    (elvEFunctor D Sc cutoff N i Λ (PowerWordWeight.wordWeight_append D Λ (ν ++ [j]) i))
    (PowerWordEvaluation.value_append D Sc cutoff L Λ ν j)
    (PowerWordEvaluation.value_append D Sc cutoff L Λ (ν ++ [j]) i)
    (value_pair D Sc cutoff L Λ ν i j)
    (PowerWordEvaluation.chart D Sc cutoff L Λ ν)
    (PowerWordWeight.weightAppendIso D Sc cutoff L Λ ν j)
    (PowerWordWeight.weightAppendIso D Sc cutoff L Λ (ν ++ [j]) i)
  rw [PowerWordEvaluation.chart_append D Sc cutoff L Λ (ν ++ [j]) i,
    PowerWordEvaluation.chart_append D Sc cutoff L Λ ν j,
    PowerWordEvaluation.pairChart, recursivePair_canonical]
  exact hh

/-- The independently chosen crossing has the literal signed old crossing
as its whole native Hom coordinate. The target is the explicit same-weight
word family, and the given target-path weight certificate is retained. -/
theorem homEquiv_cross (i j : I)
    (h₄ : PowerWordWeight.wordWeight D Λ (ν ++ [i]) + D.α j =
      PowerWordWeight.wordWeight D Λ ((ν ++ [j]) ++ [i])) :
    homEquiv D Sc cutoff L Λ ((ν ++ [j]) ++ [i]) ((ν ++ [i]) ++ [j])
      (eqToHom (value_pair D Sc cutoff L Λ ν i j) ≫
        (elvActionCross D Sc cutoff N i j Λ
          (PowerWordWeight.wordWeight_append D Λ ν j) (PowerWordWeight.wordWeight_append D Λ (ν ++ [j]) i)
          (PowerWordWeight.wordWeight_append D Λ ν i) h₄).app (D.parity i * D.parity j) V ≫
        (PowerWordEvaluation.pairChart D Sc cutoff L Λ ν j i
          (PowerWordWeight.wordWeight_append D Λ ν i) h₄).hom) =
    PowerWordContentCyclicity.generator D Sc cutoff L ((ν ++ [i]) ++ [j])
      (((ν ++ [j]) ++ [i] : List I) : Multiset I)
      (PowerWordContentCyclicity.wordObject D Sc cutoff L ((ν ++ [j]) ++ [i])
        (((ν ++ [j]) ++ [i] : List I) : Multiset I) rfl)
      (PowerWordContentCross.normalizedOldCross D Sc cutoff ν i j) := by
  have hc := prepend_cross_eq (value_pair D Sc cutoff L Λ ν i j)
    (PowerWordEvaluation.pairChart D Sc cutoff L Λ ν i j
      (PowerWordWeight.wordWeight_append D Λ ν j) (PowerWordWeight.wordWeight_append D Λ (ν ++ [j]) i))
    (PowerWordEvaluation.pairChart D Sc cutoff L Λ ν j i (PowerWordWeight.wordWeight_append D Λ ν i) h₄) _ _
    (PowerWordEvaluation.cross_pair_value D Sc cutoff L Λ ν i j
      (PowerWordWeight.wordWeight_append D Λ ν j) (PowerWordWeight.wordWeight_append D Λ (ν ++ [j]) i)
      (PowerWordWeight.wordWeight_append D Λ ν i) h₄)
  rw [← chart_pair_hom] at hc
  have hY : PowerWordWeightCross.wordFamilyCross D Sc cutoff L Λ ν i j =
      PowerWordWeightWhiskering.wordFamilyArrow D Sc cutoff L Λ
        (PowerWordWeight.wordWeight D Λ ((ν ++ [j]) ++ [i]))
        ((ν ++ [j]) ++ [i]) ((ν ++ [i]) ++ [j])
        (PowerWordContentCross.normalizedOldCross D Sc cutoff ν i j) := rfl
  rw [hY] at hc
  rw [hc]
  exact homEquiv_from_old D Sc cutoff L Λ ((ν ++ [j]) ++ [i]) ((ν ++ [i]) ++ [j]) _
end OddMath.QuiverHecke.ELVOld.PowerWordHomCoordinates
