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

end OddMath.QuiverHecke.ELVOld.PowerWordHomCoordinates
