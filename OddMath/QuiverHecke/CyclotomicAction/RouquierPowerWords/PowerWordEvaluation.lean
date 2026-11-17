import Mathlib.Data.List.Induction
import OddMath.QuiverHecke.CyclotomicAction.PowerWordWhiskering.PowerWordWeightCross
import OddMath.QuiverHecke.SwappedAssembly.ReservoirWordFunctor

/-!
# Rouquier power words

Part of the categorical action of the quiver Hecke 2-supercategory on deformed
cyclotomic quotients. Each section below was a separate file; its docstring describes it.
-/

section

/-! # Iterated chosen E values in regular-power word coordinates

SwappedVacuumCoordinates §§4–6: evaluate the given E functors on the
regular-power vacuum and retain the selected recursive, even word chart.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELV.PowerWordEvaluation
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
end OddMath.QuiverHecke.ELV.PowerWordEvaluation
end

end

section

/-! # Chosen right contexts on the full-coefficient weight word family

SwappedVacuumCoordinates §§4–6: iterate the given E functors and existing
single-append charts on arbitrary full old-Hom arrows.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELV.PowerWordWeightContexts
open CyclotomicAction CyclotomicCrossingTensor
universe u
section Weight
variable {I X : Type u} [AddCommGroup X] (D : SKM.Datum I X)
/-- The literal successive target weights along a right context. -/
def contextWeight (x : X) : List I → X
  | [] => x
  | i :: η => contextWeight (x + D.α i) η
end Weight

private theorem comparison_step {C B E : Type*} [Category* C] [Category* B] [Category* E]
    (K : C ⥤ B) (H : B ⥤ E) {P Q : C} {V W : B} {S T : E}
    (e : K.obj P ≅ V) (f : K.obj Q ≅ W) (c : H.obj V ≅ S) (d : H.obj W ≅ T)
    (x : P ⟶ Q) (y : V ⟶ W) (z : S ⟶ T)
    (h₀ : K.map x ≫ f.hom = e.hom ≫ y) (h₁ : H.map y ≫ d.hom = c.hom ≫ z) :
    (K ⋙ H).map x ≫ (H.mapIso f ≪≫ d).hom = (H.mapIso e ≪≫ c).hom ≫ z := by
  simp only [Functor.comp_map, Iso.trans_hom, Functor.mapIso_hom, Category.assoc]
  rw [← Category.assoc, ← H.map_comp, h₀, H.map_comp, Category.assoc, h₁]

variable {I X k : Type u} [AddCommGroup X] [CommRing k] [Fintype I]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (L : I × ℕ → ℕ)
  (Λ : X)
local notation "N" => PowerWordContent.powerBound D cutoff L

/-- Actual successive E functors, at their actual successive weights. -/
def contextFunctor (x : X) : (η : List I) → ELVWeightProduct D Sc cutoff N Λ x ⥤
    ELVWeightProduct D Sc cutoff N Λ (contextWeight D x η)
  | [] => 𝟭 _
  | i :: η => elvEFunctor D Sc cutoff N i Λ (rfl : x + D.α i = x + D.α i) ⋙
      contextFunctor (x + D.α i) η

omit [Fintype I] in
private theorem append_weight (ν : List I) (i : I) (x : X)
    (hx : x = PowerWordWeight.wordWeight D Λ ν) :
    x + D.α i = PowerWordWeight.wordWeight D Λ (ν ++ [i]) :=
  (congrArg (fun y => y + D.α i) hx).trans (PowerWordWeight.wordWeight_append D Λ ν i)

/-- Only the existing whole append comparisons are composed. -/
def contextIso (ν : List I) (x : X) (hx : x = PowerWordWeight.wordWeight D Λ ν) :
    (η : List I) → (contextFunctor D Sc cutoff L Λ x η).obj (PowerWordWeight.wordFamily D Sc cutoff L Λ x ν) ≅
      PowerWordWeight.wordFamily D Sc cutoff L Λ (contextWeight D x η) (PowerWordContexts.extendedWord ν η)
  | [] => Iso.refl _
  | i :: η => (contextFunctor D Sc cutoff L Λ (x + D.α i) η).mapIso
      (PowerWordWeightCross.appendIsoAtWeights D Sc cutoff L Λ ν i x (x + D.α i) hx
        (append_weight D Λ ν i x hx) rfl) ≪≫
      contextIso (ν ++ [i]) (x + D.α i) (append_weight D Λ ν i x hx) η

private def contextEquation (s t η : List I) (x : X)
    (hs : x = PowerWordWeight.wordWeight D Λ s) (ht : x = PowerWordWeight.wordWeight D Λ t)
    (g : (OldCategory.mk t : OldCategory D Sc cutoff) ⟶ OldCategory.mk s) : Prop :=
  (contextFunctor D Sc cutoff L Λ x η).map (PowerWordWeightWhiskering.wordFamilyArrow D Sc cutoff L Λ x s t g) ≫
      (contextIso D Sc cutoff L Λ t x ht η).hom =
    (contextIso D Sc cutoff L Λ s x hs η).hom ≫
      PowerWordWeightWhiskering.wordFamilyArrow D Sc cutoff L Λ (contextWeight D x η)
        (PowerWordContexts.extendedWord s η) (PowerWordContexts.extendedWord t η)
        (PowerWordContexts.extendedArrow D Sc cutoff s t η g)

/-- Every chosen right context has the prescribed full old-Hom operator on
all content blocks and coefficient vectors. The weight equalities only
express the unchanged weights of the same-content words. -/
theorem context_family_arrow (s t η : List I) (x : X)
    (hs : x = PowerWordWeight.wordWeight D Λ s) (ht : x = PowerWordWeight.wordWeight D Λ t)
    (hst : (s : Multiset I) = (t : Multiset I))
    (g : (OldCategory.mk t : OldCategory D Sc cutoff) ⟶ OldCategory.mk s) :
    contextEquation D Sc cutoff L Λ s t η x hs ht g := by
  induction η generalizing s t x with
  | nil =>
      change (𝟭 _).map _ ≫ (Iso.refl _).hom = (Iso.refl _).hom ≫ _
      simp only [Functor.id_map, Iso.refl_hom, Category.comp_id, Category.id_comp]
      rfl
  | cons i η ih =>
      have hst' : ((s ++ [i] : List I) : Multiset I) = ((t ++ [i] : List I) : Multiset I) := by
        rw [← Multiset.coe_add, ← Multiset.coe_add, hst]
      exact comparison_step
        (elvEFunctor D Sc cutoff N i Λ (rfl : x + D.α i = x + D.α i))
        (contextFunctor D Sc cutoff L Λ (x + D.α i) η)
        (PowerWordWeightCross.appendIsoAtWeights D Sc cutoff L Λ s i x (x + D.α i) hs
          (append_weight D Λ s i x hs) rfl)
        (PowerWordWeightCross.appendIsoAtWeights D Sc cutoff L Λ t i x (x + D.α i) ht
          (append_weight D Λ t i x ht) rfl)
        (contextIso D Sc cutoff L Λ (s ++ [i]) (x + D.α i) (append_weight D Λ s i x hs) η)
        (contextIso D Sc cutoff L Λ (t ++ [i]) (x + D.α i) (append_weight D Λ t i x ht) η)
        (PowerWordWeightWhiskering.wordFamilyArrow D Sc cutoff L Λ x s t g)
        (PowerWordWeightWhiskering.wordFamilyArrow D Sc cutoff L Λ (x + D.α i) (s ++ [i]) (t ++ [i])
          ((append D Sc cutoff i).map g))
        (PowerWordWeightWhiskering.wordFamilyArrow D Sc cutoff L Λ (contextWeight D (x + D.α i) η)
          (PowerWordContexts.extendedWord (s ++ [i]) η) (PowerWordContexts.extendedWord (t ++ [i]) η)
          (PowerWordContexts.extendedArrow D Sc cutoff (s ++ [i]) (t ++ [i]) η ((append D Sc cutoff i).map g)))
        (PowerWordWeightWhiskering.append_family_arrow D Sc cutoff L Λ s t i x (x + D.α i)
          hs (append_weight D Λ s i x hs) ht (append_weight D Λ t i x ht) rfl hst g)
        (ih (s ++ [i]) (t ++ [i]) (x + D.α i) (append_weight D Λ s i x hs)
          (append_weight D Λ t i x ht) hst' ((append D Sc cutoff i).map g))

/-- Apply the given context to a selected chart, then use only the existing
recursive whole append comparisons. -/
def contextChart (ν η : List I) (x : X) (hx : x = PowerWordWeight.wordWeight D Λ ν)
    {A : ELVWeightProduct D Sc cutoff N Λ x}
    (e : A ≅ PowerWordWeight.wordFamily D Sc cutoff L Λ x ν) :
    (contextFunctor D Sc cutoff L Λ x η).obj A ≅
      PowerWordWeight.wordFamily D Sc cutoff L Λ (contextWeight D x η) (PowerWordContexts.extendedWord ν η) :=
  (contextFunctor D Sc cutoff L Λ x η).mapIso e ≪≫ contextIso D Sc cutoff L Λ ν x hx η

omit [Fintype I] in
private theorem pair_weight (ν : List I) (i j : I) {xj xu : X}
    (h₁ : PowerWordWeight.wordWeight D Λ ν + D.α j = xj) (h₂ : xj + D.α i = xu) :
    xu = PowerWordWeight.wordWeight D Λ ((ν ++ [j]) ++ [i]) :=
  h₂.symm.trans ((congrArg (fun x => x + D.α i)
    (h₁.symm.trans (PowerWordWeight.wordWeight_append D Λ ν j))).trans
      (PowerWordWeight.wordWeight_append D Λ (ν ++ [j]) i))

end OddMath.QuiverHecke.ELV.PowerWordWeightContexts
end

end

section

/-! # Hom coordinates of the chosen E-word value

SwappedVacuumCoordinates §§3–6: transfer the existing regular-power Yoneda
coordinates through the selected native E-word chart, retaining every
content block and the same-weight target word family.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELV.PowerWordHomCoordinates
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

end OddMath.QuiverHecke.ELV.PowerWordHomCoordinates
end

end
