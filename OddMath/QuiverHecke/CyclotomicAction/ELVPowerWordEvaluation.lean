import OddMath.QuiverHecke.CyclotomicAction.ELVPowerWordChartParity
import OddMath.QuiverHecke.CyclotomicAction.ELVPowerWordWeightDot
import Mathlib.Data.List.Induction

/-! # Iterated chosen E values in regular-power word coordinates

SwappedVacuumCoordinates §§4–6: evaluate the given E functors on the
regular-power vacuum and retain the selected recursive, even word chart.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld.PowerWordEvaluation
open CyclotomicAction
universe u
section Generic
variable {k : Type u} [CommRing k] {C : Type*} [Category* C]
  [Preadditive C] [Linear k C] [Supercategory k C]
private theorem iso_even_comp {A B E : C} (e : A ≅ B) (f : B ≅ E)
    (he : e.hom ∈ parity (R := k) _ _ 0) (hf : f.hom ∈ parity (R := k) _ _ 0) :
    (e ≪≫ f).hom ∈ parity (R := k) _ _ 0 := by
  simpa only [Iso.trans_hom, zero_add] using comp_mem he hf
private theorem eq_iso_even {A B : C} (h : A = B) : (eqToIso h).hom ∈ parity (R := k) _ _ 0 := by
  cases h
  exact id_mem _
omit [Preadditive C] in
private theorem square_comp {A B E : C} (e : A ≅ B) (f : B ≅ E)
    (x : A ⟶ A) (y : B ⟶ B) (z : E ⟶ E)
    (he : x ≫ e.hom = e.hom ≫ y) (hf : y ≫ f.hom = f.hom ≫ z) :
    x ≫ (e ≪≫ f).hom = (e ≪≫ f).hom ≫ z := by
  simp only [Iso.trans_hom, Category.assoc]
  rw [← Category.assoc, he, Category.assoc, hf]

omit [Preadditive C] in
private theorem cross_comp {A B E F S T : C} (e : A ≅ B) (f : E ≅ F) (s : B ≅ S) (t : F ≅ T)
    (x : A ⟶ E) (y : B ⟶ F) (z : S ⟶ T)
    (hn : x ≫ f.hom = e.hom ≫ y) (hc : y ≫ t.hom = s.hom ≫ z) :
    x ≫ (f ≪≫ t).hom = (e ≪≫ s).hom ≫ z := by
  simp only [Iso.trans_hom, Category.assoc]
  rw [← Category.assoc, hn, Category.assoc, hc]

private theorem natural_even {A E : Type*} [Category* A] [Preadditive A] [Linear k A] [Supercategory k A]
    [Category* E] [Preadditive E] [Linear k E] [Supercategory k E]
    (F G : A ⥤ E) (a : SuperNatTrans k F G) {X Y : A} (e : X ≅ Y)
    (he : e.hom ∈ parity (R := k) _ _ 0) (p : ZMod 2) :
    a.app p X ≫ G.map e.hom = F.map e.hom ≫ a.app p Y := by
  simpa only [koszulSign_zero_right, one_smul] using (a.naturality p e.hom he).symm
end Generic
variable {I X k : Type u} [AddCommGroup X] [CommRing k] [Fintype I]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (L : I × ℕ → ℕ)
  (Λ : X)
local notation "N" => PowerWordContent.powerBound D cutoff L

/-- Literal iteration of the given E functors on the given regular-power vacuum. -/
def value (ν : List I) : ELVWeightProduct D Sc cutoff N Λ (PowerWordWeight.wordWeight D Λ ν) :=
  ν.reverseRecOn (PowerWordWeight.wordFamily D Sc cutoff L Λ (PowerWordWeight.wordWeight D Λ []) [])
    (fun ρ i M => (elvE D Sc cutoff N i Λ (PowerWordWeight.wordWeight_append D Λ ρ i)).obj M)

theorem value_nil : value D Sc cutoff L Λ [] =
    PowerWordWeight.wordFamily D Sc cutoff L Λ (PowerWordWeight.wordWeight D Λ []) [] := by
  simp only [value, List.reverseRecOn_nil]

theorem value_append (ν : List I) (i : I) : value D Sc cutoff L Λ (ν ++ [i]) =
    (elvE D Sc cutoff N i Λ (PowerWordWeight.wordWeight_append D Λ ν i)).obj
      (value D Sc cutoff L Λ ν) := by
  simp only [value, List.reverseRecOn_concat]

/-- The selected chart is built from the existing whole single-append comparisons. -/
def chart (ν : List I) : value D Sc cutoff L Λ ν ≅
    PowerWordWeight.wordFamily D Sc cutoff L Λ (PowerWordWeight.wordWeight D Λ ν) ν :=
  ν.reverseRecOn (eqToIso (value_nil D Sc cutoff L Λ)) (fun ρ i e =>
    eqToIso (value_append D Sc cutoff L Λ ρ i) ≪≫
      (elvE D Sc cutoff N i Λ (PowerWordWeight.wordWeight_append D Λ ρ i)).toFunctor.mapIso e ≪≫
        PowerWordWeight.weightAppendIso D Sc cutoff L Λ ρ i)

theorem chart_nil : chart D Sc cutoff L Λ [] = eqToIso (value_nil D Sc cutoff L Λ) := by
  simp only [chart, List.reverseRecOn_nil]

theorem chart_append (ν : List I) (i : I) : chart D Sc cutoff L Λ (ν ++ [i]) =
    eqToIso (value_append D Sc cutoff L Λ ν i) ≪≫
      (elvE D Sc cutoff N i Λ (PowerWordWeight.wordWeight_append D Λ ν i)).toFunctor.mapIso
        (chart D Sc cutoff L Λ ν) ≪≫ PowerWordWeight.weightAppendIso D Sc cutoff L Λ ν i := by
  simp only [chart, List.reverseRecOn_concat]

/-- The recursively selected word chart is even at every word. -/
theorem chart_even (ν : List I) : (chart D Sc cutoff L Λ ν).hom ∈ parity (R := k) _ _ 0 := by
  induction ν using List.reverseRecOn with
  | nil =>
      rw [chart_nil]
      exact eq_iso_even _
  | append_singleton ν i ih =>
      rw [chart_append]
      exact iso_even_comp _ _ (eq_iso_even _)
        (iso_even_comp _ _ (IsSuperfunctor.map_mem (F :=
          (elvE D Sc cutoff N i Λ (PowerWordWeight.wordWeight_append D Λ ν i)).toFunctor) ih)
          (PowerWordChartParity.weight_append_even D Sc cutoff L ν i Λ))

/-- The actual next E value chart, with the previous word chart whiskered
by the given E functor before the selected single-append comparison. -/
def appendChart (ν : List I) (i : I) :
    (elvE D Sc cutoff N i Λ (PowerWordWeight.wordWeight_append D Λ ν i)).obj
      (value D Sc cutoff L Λ ν) ≅
    PowerWordWeight.wordFamily D Sc cutoff L Λ (PowerWordWeight.wordWeight D Λ (ν ++ [i])) (ν ++ [i]) :=
  (elvE D Sc cutoff N i Λ (PowerWordWeight.wordWeight_append D Λ ν i)).toFunctor.mapIso
    (chart D Sc cutoff L Λ ν) ≪≫ PowerWordWeight.weightAppendIso D Sc cutoff L Λ ν i

/-- The given dot on the iterated E-word value is the signed old-Hom dot
under its recursively selected chart, on every coefficient vector. -/
theorem dot_append_value (ν : List I) (i : I) :
    (elvActionDot D Sc cutoff N i Λ (PowerWordWeight.wordWeight_append D Λ ν i)).app (D.parity i)
      (value D Sc cutoff L Λ ν) ≫ (appendChart D Sc cutoff L Λ ν i).hom =
    (appendChart D Sc cutoff L Λ ν i).hom ≫ PowerWordWeightDot.wordFamilyDot D Sc cutoff L Λ ν i := by
  exact square_comp
    ((elvE D Sc cutoff N i Λ (PowerWordWeight.wordWeight_append D Λ ν i)).toFunctor.mapIso
      (chart D Sc cutoff L Λ ν)) (PowerWordWeight.weightAppendIso D Sc cutoff L Λ ν i) _ _ _
    (natural_even _ _ (elvActionDot D Sc cutoff N i Λ (PowerWordWeight.wordWeight_append D Λ ν i))
      (chart D Sc cutoff L Λ ν) (chart_even D Sc cutoff L Λ ν) (D.parity i))
    (PowerWordWeightDot.weight_append_dot D Sc cutoff L Λ ν i)

/-- The actual pair E value chart, retaining the given successive weights. -/
def pairChart (ν : List I) (i j : I) {xj xu : X}
    (h₁ : PowerWordWeight.wordWeight D Λ ν + D.α j = xj) (h₂ : xj + D.α i = xu) :
    (elvEFunctor D Sc cutoff N j Λ h₁ ⋙ elvEFunctor D Sc cutoff N i Λ h₂).obj
      (value D Sc cutoff L Λ ν) ≅
    PowerWordWeight.wordFamily D Sc cutoff L Λ xu ((ν ++ [j]) ++ [i]) :=
  (elvEFunctor D Sc cutoff N j Λ h₁ ⋙ elvEFunctor D Sc cutoff N i Λ h₂).mapIso
    (chart D Sc cutoff L Λ ν) ≪≫ PowerWordWeightCross.recursivePairIso D Sc cutoff L Λ ν i j rfl h₁ h₂

/-- The given crossing on iterated E-word values agrees with the full signed
old-Hom operator in the same recursive charts. Both colours and all vectors
are included, with the actual intermediate weights retained. -/
theorem cross_pair_value (ν : List I) (i j : I) {xj xu xi : X}
    (h₁ : PowerWordWeight.wordWeight D Λ ν + D.α j = xj) (h₂ : xj + D.α i = xu)
    (h₃ : PowerWordWeight.wordWeight D Λ ν + D.α i = xi) (h₄ : xi + D.α j = xu) :
    (elvActionCross D Sc cutoff N i j Λ h₁ h₂ h₃ h₄).app (D.parity i * D.parity j)
      (value D Sc cutoff L Λ ν) ≫ (pairChart D Sc cutoff L Λ ν j i h₃ h₄).hom =
    (pairChart D Sc cutoff L Λ ν i j h₁ h₂).hom ≫
      PowerWordWeightCross.wordFamilyCross D Sc cutoff L Λ ν i j (xu := xu) := by
  exact cross_comp
    ((elvEFunctor D Sc cutoff N j Λ h₁ ⋙ elvEFunctor D Sc cutoff N i Λ h₂).mapIso
      (chart D Sc cutoff L Λ ν))
    ((elvEFunctor D Sc cutoff N i Λ h₃ ⋙ elvEFunctor D Sc cutoff N j Λ h₄).mapIso
      (chart D Sc cutoff L Λ ν))
    (PowerWordWeightCross.recursivePairIso D Sc cutoff L Λ ν i j rfl h₁ h₂)
    (PowerWordWeightCross.recursivePairIso D Sc cutoff L Λ ν j i rfl h₃ h₄) _ _ _
    (natural_even _ _ (elvActionCross D Sc cutoff N i j Λ h₁ h₂ h₃ h₄)
      (chart D Sc cutoff L Λ ν) (chart_even D Sc cutoff L Λ ν) (D.parity i * D.parity j))
    (PowerWordPairCoherence.recursive_pair_cross D Sc cutoff L Λ ν i j rfl h₁ h₂ h₃ h₄)
end OddMath.QuiverHecke.ELVOld.PowerWordEvaluation
