import OddMath.QuiverHecke.CyclotomicAction.WeightPair
import OddMath.QuiverHecke.CyclotomicAction.GlobalWeightRouquier
import OddMath.Algebra.FiniteSupermoduleFunctor
import OddMath.QuiverHecke.CyclotomicAction.PowerWordWhiskering
import Mathlib.Data.List.Induction
import OddMath.QuiverHecke.SwappedAssembly.ReservoirWordFunctor
import OddMath.QuiverHecke.CyclotomicAction.GlobalInduction
import OddMath.SKM.RouquierMulticolour
import OddMath.QuiverHecke.CyclotomicAction.ContentMatrix
import OddMath.QuiverHecke.CyclotomicAction.CoefficientPowerSeries

/-!
# Rouquier power words

Part of the categorical action of the quiver Hecke 2-supercategory on deformed
cyclotomic quotients. Each section below was a separate file; its docstring describes it.
-/

section

/-! # Rouquier generator data on the full-coefficient weight categories

Brundan--Ellis Definition 1.5 and DeformedActionAssembly §6: assemble the
prescribed weight induction, dot and crossing in the actual PiSCat target.
The same-colour square is a native two-morphism equation. No local inverse
or complete factor-family assertion is supplied.
-/

noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld
universe u

section Total
variable {k : Type u} [CommRing k]
    {C B : Type*} [Category* C] [Category* B]
    [Preadditive C] [Linear k C] [Supercategory k C]
    [Preadditive B] [Linear k B] [Supercategory k B]

/-- Total components detect a supernatural map into any supercategory. -/
theorem supernatural_hom_ext_total {F G : Superfunctor k C B} {f g : F ⟶ G}
    (h : ∀ t, f.total t = g.total t) : f = g := by
  apply Superfunctor.hom_ext
  intro p t
  have hp (s : F ⟶ G) : proj k p (s.total t) = s.app p t := by
    rcases parity_eq_zero_or_one p with rfl | rfl
    · exact proj_eq_of_add rfl (s.app_mem 0 t) (s.app_mem 1 t)
    · exact proj_eq_of_add (add_comm _ _) (s.app_mem 1 t)
        (by simpa using s.app_mem 0 t)
  rw [← hp f, ← hp g, h t]

theorem supernatural_zero_total {F G : Superfunctor k C B} (t : C) :
    (0 : F ⟶ G).total t = 0 := by
  simp only [SuperNatTrans.total, Superfunctor.zero_app, zero_add]

theorem supernatural_total_of_mem {F G : Superfunctor k C B}
    {p : ZMod 2} {f : F ⟶ G} (hf : f ∈ parity (R := k) _ _ p) (t : C) :
    f.total t = f.app p t := by
  rcases parity_eq_zero_or_one p with rfl | rfl
  · rw [SuperNatTrans.total, Superfunctor.app_eq_zero_of_mem hf (q := 1) (by decide), add_zero]
  · rw [SuperNatTrans.total, Superfunctor.app_eq_zero_of_mem hf (q := 0) (by decide), zero_add]

theorem supernatural_square_zero_of_total {F : Superfunctor k C B} (f : F ⟶ F)
    (h : ∀ t, f.total t ≫ f.total t = 0) : f ≫ f = 0 := by
  apply supernatural_hom_ext_total
  intro t
  rw [Superfunctor.comp_total, supernatural_zero_total]
  exact h t
end Total

variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (bound : ℕ)

/-- The given action crossing, as a two-morphism, has square zero on every
weight category. The proof includes every absent predecessor component. -/
theorem elvActionCross_square (i : I) (Λ : X) {x₀ x₁ x₂ : X}
    (h₁ : x₀ + D.α i = x₁) (h₂ : x₁ + D.α i = x₂) :
    elvActionCross D Sc cutoff bound i i Λ h₁ h₂ h₁ h₂ ≫
      elvActionCross D Sc cutoff bound i i Λ h₁ h₂ h₁ h₂ = 0 := by
  apply supernatural_square_zero_of_total
  intro M
  simp only [supernatural_total_of_mem
    (elvActionCross_mem D Sc cutoff bound i i Λ h₁ h₂ h₁ h₂) M]
  funext ε
  change elvWeightCrossComponent D Sc cutoff bound i i Λ h₁ h₂ h₁ h₂
      (D.parity i * D.parity i) M ε ≫
    elvWeightCrossComponent D Sc cutoff bound i i Λ h₁ h₂ h₁ h₂
      (D.parity i * D.parity i) M ε = 0
  apply FiniteSupermodule.hom_ext_total
  intro w
  rw [Superfunctor.comp_total, supernatural_zero_total]
  exact elvWeightCrossComponent_square_total D Sc cutoff bound i Λ h₁ h₂ M ε w

/-- The prescribed upward generators on the original weight spaces.
This is generator data, not a complete relation-preserving factor action. -/
def elvRouquierData (Λ : X) :
    SKM.RouquierData (k := k) (B := PiSCat.{u, u, u + 1} k) D where
  obj x := elvWeightSpace D Sc cutoff bound Λ x
  E i _ _ h := elvE D Sc cutoff bound i Λ h
  dot i _ _ h := elvActionDot D Sc cutoff bound i Λ h
  dot_mem i _ _ h := elvActionDot_mem D Sc cutoff bound i Λ h
  cross i j _ _ _ _ h₁ h₂ h₃ h₄ := elvActionCross D Sc cutoff bound i j Λ h₁ h₂ h₃ h₄
  cross_mem i j _ _ _ _ h₁ h₂ h₃ h₄ := elvActionCross_mem D Sc cutoff bound i j Λ h₁ h₂ h₃ h₄

theorem elvRouquierData_square (i : I) (Λ : X) {x₀ x₁ x₂ : X}
    (h₁ : x₀ + D.α i = x₁) (h₂ : x₁ + D.α i = x₂) :
    (elvRouquierData D Sc cutoff bound Λ).cross i i h₁ h₂ h₁ h₂ ≫
      (elvRouquierData D Sc cutoff bound Λ).cross i i h₁ h₂ h₁ h₂ = 0 :=
  elvActionCross_square D Sc cutoff bound i Λ h₁ h₂

end OddMath.QuiverHecke.ELVOld
end

end

section

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
end

end

section

/-! # Chosen values of the reversed reservoir word

SwappedActionAssembly §6 and SwappedVacuumCoordinates §2: keep the exact
formal-content weight when comparing the surviving reservoir path with
the append-defined chosen E-word value. The word is reversed, while the
original weight group and all strand labels are retained.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld.ReservoirWordValue
open SwappedAssembly CyclotomicAction
universe u
variable {I X : Type u} [AddCommGroup X] (D : SKM.Datum I X) (Λ : X)

private theorem reversed_word_weight (l : List (SKM.Col I X)) :
    ReservoirWord.weight D Λ (SPath.wordContent l) =
      blockWeight D Λ ((l.map (fun a => a.l.2)).reverse : Multiset I) := by
  induction l with
  | nil => simp [ReservoirWord.weight, SPath.wordContent]
  | cons a l ih =>
    have hs : blockWeight D Λ (((a :: l).map (fun a => a.l.2)).reverse : Multiset I) =
        blockWeight D Λ ((l.map (fun a => a.l.2)).reverse : Multiset I) + D.α a.l.2 := by
      simpa only [List.map_cons, List.reverse_cons, ← Multiset.coe_add,
        Multiset.coe_singleton, add_comm] using
          (blockWeight_cons D Λ a.l.2 ((l.map (fun a => a.l.2)).reverse : Multiset I))
    rw [hs, ← ih]
    simp only [ReservoirWord.weight, SPath.wordContent, map_add, contentWeight,
      Finsupp.weight_single, one_nsmul]
    abel

private theorem path_weight (l : List (SKM.Col I X)) :
    ReservoirWord.weight D Λ (SPath.wordContent l + 0) =
      blockWeight D Λ ((l.map (fun a => a.l.2)).reverse : Multiset I) := by
  simpa only [add_zero] using reversed_word_weight D Λ l

section Modules
variable {k : Type u} [CommRing k] (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (N : ℕ)

end Modules

section ChosenValue
variable {k : Type u} [CommRing k] [Fintype I]
  (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (L : I × ℕ → ℕ)
local notation "N" => PowerWordContent.powerBound D cutoff L

/-- The actual regular-power empty-word family, at its formal-content weight. -/
def initialValue : ELVWeightProduct D Sc cutoff N Λ (ReservoirWord.weight D Λ 0) :=
  PowerWordWeight.wordFamily D Sc cutoff L Λ (ReservoirWord.weight D Λ 0) []

end ChosenValue

end OddMath.QuiverHecke.ELVOld.ReservoirWordValue
end

end

section

/-! # Evaluating polynomial endomorphisms of the weight action

DeformedActionAssembly §6 (9): total evaluation preserves the ordered
endomorphism algebra. This transports the component quadratic polynomial
to the native two-morphism relation without commuting odd operators.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld
universe u
variable {k : Type u} [CommRing k]
    {C B : Type*} [Category* C] [Category* B]
    [Preadditive C] [Linear k C] [Supercategory k C]
    [Preadditive B] [Linear k B] [Supercategory k B]

/-- Total evaluation is linear on arbitrary supernatural maps. -/
def supernaturalTotalLinearMap (F G : Superfunctor k C B) (M : C) :
    (F ⟶ G) →ₗ[k] (F.obj M ⟶ G.obj M) where
  toFun f := f.total M
  map_add' f g := by
    change (f.app 0 M + g.app 0 M) + (f.app 1 M + g.app 1 M) =
      (f.app 0 M + f.app 1 M) + (g.app 0 M + g.app 1 M)
    abel
  map_smul' r f := by
    change r • f.app 0 M + r • f.app 1 M = r • (f.app 0 M + f.app 1 M)
    exact (smul_add _ _ _).symm

/-- Total evaluation respects the ordered endomorphism algebra. -/
def supernaturalEndEvaluation (F : Superfunctor k C B) (M : C) :
    End F →ₐ[k] End (F.obj M) :=
  AlgHom.ofLinearMap (supernaturalTotalLinearMap F F M)
    (by change (𝟙 F : F ⟶ F).total M = 𝟙 (F.obj M); simp [SuperNatTrans.total])
    (fun f g => Superfunctor.comp_total g f M)
/-- Project a family endomorphism to one of its categories. -/
def piEndEvaluation {J : Type*} {A : J → Type*} [∀ j, Category (A j)]
    [∀ j, Preadditive (A j)] [∀ j, Linear k (A j)] (V : ∀ j, A j) (j : J) :
    End V →ₐ[k] End (V j) :=
  AlgHom.ofLinearMap
    { toFun := fun f => f j
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
    rfl (fun _ _ => rfl)

/-- Endomorphisms of a super vector space act as ordinary linear operators,
with the same multiplication order. -/
def svecEndEvaluation (V : SVec k) : End V →ₐ[k] Module.End k V :=
  AlgHom.ofLinearMap
    { toFun := fun f => f
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
    rfl (fun _ _ => rfl)
/-- Evaluate an endomorphism of a family of module-valued functors all the
way to its linear operator. -/
def moduleFamilyEndEvaluation {J : Type u} {A : J → Type u}
    [∀ j, Category.{u} (A j)] [∀ j, Preadditive (A j)]
    [∀ j, Linear k (A j)] [∀ j, Supercategory k (A j)]
    (F : Superfunctor k C (∀ j, Superfunctor k (A j) (SVec k)))
    (M : C) (j : J) (w : A j) :
    End F →ₐ[k] Module.End k ((F.obj M j).obj w) :=
  (((svecEndEvaluation ((F.obj M j).obj w)).comp
      (supernaturalEndEvaluation (F.obj M j) w)).comp
      (piEndEvaluation (F.obj M) j)).comp
      (supernaturalEndEvaluation F M)

theorem moduleFamilyEndEvaluation_ext {J : Type u} {A : J → Type u}
    [∀ j, Category.{u} (A j)] [∀ j, Preadditive (A j)]
    [∀ j, Linear k (A j)] [∀ j, Supercategory k (A j)]
    (F : Superfunctor k C (∀ j, Superfunctor k (A j) (SVec k)))
    (f g : End F) (h : ∀ M j w,
      moduleFamilyEndEvaluation F M j w f = moduleFamilyEndEvaluation F M j w g) : f = g := by
  apply supernatural_hom_ext_total
  intro M
  funext j
  apply FiniteSupermodule.hom_ext_total
  intro w
  exact h M j w

/-- Ordered operator polynomials commute with algebra homomorphisms;
this does not require the component evaluation to be invertible. -/
theorem orderedPairOperatorPolynomial_map_hom
    {I X : Type u} [AddCommGroup X] (D : SKM.Datum I X) (Sc : SKM.Scalars D k)
    {R S : Type*} [Ring R] [Algebra k R] [Ring S] [Algebra k S]
    (e : R →ₐ[k] S) (i j : I) (A B : R) :
    e (orderedPairOperatorPolynomial D Sc i j A B) =
      orderedPairOperatorPolynomial D Sc i j (e A) (e B) := by
  unfold orderedPairOperatorPolynomial
  split_ifs <;> simp only [map_smul, map_one, map_add, map_sum, map_mul, map_pow]
/-- Componentwise ordered quadratics give the equation of natural maps. -/
theorem moduleFamily_polynomial_of_components
    {I X : Type u} [AddCommGroup X] (D : SKM.Datum I X) (Sc : SKM.Scalars D k)
    {J : Type u} {A : J → Type u}
    [∀ j, Category.{u} (A j)] [∀ j, Preadditive (A j)]
    [∀ j, Linear k (A j)] [∀ j, Supercategory k (A j)]
    {F G : Superfunctor k C (∀ j, Superfunctor k (A j) (SVec k))}
    (c : F ⟶ G) (d : G ⟶ F) (a b : End F) (i j : I)
    (h : ∀ M t w, ((d.total M t).total w).comp ((c.total M t).total w) =
      orderedPairOperatorPolynomial (R := Module.End k ((F.obj M t).obj w)) D Sc i j ((a.total M t).total w) ((b.total M t).total w)) :
    c ≫ d = orderedPairOperatorPolynomial (R := End F) D Sc i j a b := by
  apply moduleFamilyEndEvaluation_ext
  intro M t w
  rw [orderedPairOperatorPolynomial_map_hom]
  change ((c ≫ d).total M t).total w =
    orderedPairOperatorPolynomial (R := Module.End k ((F.obj M t).obj w)) D Sc i j ((a.total M t).total w) ((b.total M t).total w)
  rw [Superfunctor.comp_total]
  change ((c.total M t) ≫ (d.total M t)).total w = _
  rw [Superfunctor.comp_total]
  exact h M t w
end OddMath.QuiverHecke.ELVOld
end

end

section

/-! # The uncorrected multicolour braid equation of Rouquier data

Brundan--Ellis (1.9). Capture the literal RouquierMulticolour.braid formula
before specializing large chosen action data.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory BicategoryStruct
namespace OddMath.QuiverHecke.ELVOld
universe u v w r
variable {k : Type r} [CommRing k] {B : Type u} [BicategoryStruct.{w,v} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear k (a ⟶ b)]
  [∀ a b : B, Supercategory k (a ⟶ b)]
  {I X : Type r} [AddCommGroup X] (D : SKM.Datum I X)
  (R : SKM.RouquierData (k := k) (B := B) D) (i j l : I)
  {a bl bj bi clj cli cji d : X}
  (hal : a + D.α l = bl) (haj : a + D.α j = bj) (hai : a + D.α i = bi)
  (hlj : bl + D.α j = clj) (hli : bl + D.α i = cli) (hjl : bj + D.α l = clj)
  (hji : bj + D.α i = cji) (hil : bi + D.α l = cli) (hij : bi + D.α j = cji)
  (hd₁ : clj + D.α i = d) (hd₂ : cli + D.α j = d) (hd₃ : cji + D.α l = d)

/-- Exactly the uncorrected multicolour braid field, with every chosen
crossing and associator retained. -/
def rouquierMulticolourBraidEquation : Prop :=
    R.E l hal ◁ R.cross i j hlj hd₁ hli hd₂ ≫
        (associator (R.E l hal) (R.E i hli) (R.E j hd₂)).inv ≫
        R.cross i l hal hli hai hil ▷ R.E j hd₂ ≫
        (associator (R.E i hai) (R.E l hil) (R.E j hd₂)).hom ≫
        R.E i hai ◁ R.cross j l hil hd₂ hij hd₃ =
      (associator (R.E l hal) (R.E j hlj) (R.E i hd₁)).inv ≫
        R.cross j l hal hlj haj hjl ▷ R.E i hd₁ ≫
        (associator (R.E j haj) (R.E l hjl) (R.E i hd₁)).hom ≫
        R.E j haj ◁ R.cross i l hjl hd₁ hji hd₃ ≫
        (associator (R.E j haj) (R.E i hji) (R.E l hd₃)).inv ≫
        R.cross i j haj hji hai hij ▷ R.E l hd₃ ≫
        (associator (R.E i hai) (R.E j hij) (R.E l hd₃)).hom

local notation "a₀" => R.E l hal ◁ R.cross i j hlj hd₁ hli hd₂
local notation "a₁" => Iso.inv (associator (R.E l hal) (R.E i hli) (R.E j hd₂)) ≫
  R.cross i l hal hli hai hil ▷ R.E j hd₂ ≫
  Iso.hom (associator (R.E i hai) (R.E l hil) (R.E j hd₂))
local notation "a₂" => R.E i hai ◁ R.cross j l hil hd₂ hij hd₃
local notation "b₀" => Iso.inv (associator (R.E l hal) (R.E j hlj) (R.E i hd₁)) ≫
  R.cross j l hal hlj haj hjl ▷ R.E i hd₁ ≫
  Iso.hom (associator (R.E j haj) (R.E l hjl) (R.E i hd₁))
local notation "b₁" => R.E j haj ◁ R.cross i l hjl hd₁ hji hd₃
local notation "b₂" => Iso.inv (associator (R.E j haj) (R.E i hji) (R.E l hd₃)) ≫
  R.cross i j haj hji hai hij ▷ R.E l hd₃ ≫
  Iso.hom (associator (R.E i hai) (R.E j hij) (R.E l hd₃))

/-- Reassociate the six given crossing paths to the literal data field,
before any chosen large action is substituted. -/
theorem rouquierMulticolourBraidEquation_of_paths
    (h : a₀ ≫ a₁ ≫ a₂ = b₀ ≫ b₁ ≫ b₂) :
    rouquierMulticolourBraidEquation D R i j l hal haj hai hlj hli hjl hji hil hij hd₁ hd₂ hd₃ := by
  simpa only [rouquierMulticolourBraidEquation, Category.assoc] using h

end OddMath.QuiverHecke.ELVOld
end

end

section

/-! # The dotted mixed braid equation of Rouquier data

Brundan--Ellis (1.9). Keep the exact RouquierMulticolour.braidEq formula
as one generic proposition before specializing large selected functors.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory BicategoryStruct
namespace OddMath.QuiverHecke.ELVOld
universe u v w r
variable {k : Type r} [CommRing k] {B : Type u} [BicategoryStruct.{w,v} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear k (a ⟶ b)]
  [∀ a b : B, Supercategory k (a ⟶ b)] [TwoSupercategory k B]
  {I X : Type r} [AddCommGroup X] (D : SKM.Datum I X) (Sc : SKM.Scalars D k)
  (R : SKM.RouquierData (k := k) (B := B) D) (i j : I) {a b c d e f : X}
  (hab : a + D.α i = b) (haf : a + D.α j = f) (hbc : b + D.α j = c)
  (hbe : b + D.α i = e) (hfc : f + D.α i = c) (hcd : c + D.α i = d)
  (hed : e + D.α j = d)

/-- Exactly the repeated-outer dotted equation in RouquierMulticolour,
with the prescribed associators, crossing maps and dot powers. -/
def rouquierMixedBraidEquation : Prop :=
    R.E i hab ◁ R.cross i j hbc hcd hbe hed ≫
        Iso.inv (associator (R.E i hab) (R.E i hbe) (R.E j hed)) ≫
        R.cross i i hab hbe hab hbe ▷ R.E j hed ≫
        Iso.hom (associator (R.E i hab) (R.E i hbe) (R.E j hed)) ≫
        R.E i hab ◁ R.cross j i hbe hed hbc hcd -
      (Iso.inv (associator (R.E i hab) (R.E j hbc) (R.E i hcd)) ≫
        R.cross j i hab hbc haf hfc ▷ R.E i hcd ≫
        Iso.hom (associator (R.E j haf) (R.E i hfc) (R.E i hcd)) ≫
        R.E j haf ◁ R.cross i i hfc hcd hfc hcd ≫
        Iso.inv (associator (R.E j haf) (R.E i hfc) (R.E i hcd)) ≫
        R.cross i j haf hfc hab hbc ▷ R.E i hcd ≫
        Iso.hom (associator (R.E i hab) (R.E j hbc) (R.E i hcd))) =
      ∑ s ∈ Finset.range (D.dn i j),
        (SKM.zsign k (D.parity i * (D.parity j + s)) * (Sc.t i j : k)) •
          (SKM.rouquierPower (R.dot i hab) s ▷ (R.E j hbc ≫ R.E i hcd) ≫
            R.E i hab ◁ R.E j hbc ◁ SKM.rouquierPower (R.dot i hcd) (D.dn i j - 1 - s)) +
      ∑ p ∈ Finset.range (D.dn i j), ∑ q ∈ Finset.range (D.dn j i), ∑ s ∈ Finset.range p,
        (SKM.zsign k (D.parity i * (D.parity j + s)) * Sc.s i j p q) •
          (SKM.rouquierPower (R.dot i hab) s ▷ (R.E j hbc ≫ R.E i hcd) ≫
            R.E i hab ◁ (SKM.rouquierPower (R.dot j hbc) q ▷ R.E i hcd) ≫
            R.E i hab ◁ R.E j hbc ◁ SKM.rouquierPower (R.dot i hcd) (p - 1 - s))

local notation "F₁" => R.E i hab
local notation "F₂" => R.E j hbc
local notation "F₃" => R.E i hcd
local notation "a₀" => R.E i hab ◁ R.cross i j hbc hcd hbe hed
local notation "a₁" => Iso.inv (associator (R.E i hab) (R.E i hbe) (R.E j hed)) ≫
  R.cross i i hab hbe hab hbe ▷ R.E j hed ≫
  Iso.hom (associator (R.E i hab) (R.E i hbe) (R.E j hed))
local notation "a₂" => R.E i hab ◁ R.cross j i hbe hed hbc hcd
local notation "b₀" => Iso.inv (associator (R.E i hab) (R.E j hbc) (R.E i hcd)) ≫
  R.cross j i hab hbc haf hfc ▷ R.E i hcd ≫
  Iso.hom (associator (R.E j haf) (R.E i hfc) (R.E i hcd))
local notation "b₁" => R.E j haf ◁ R.cross i i hfc hcd hfc hcd
local notation "b₂" => Iso.inv (associator (R.E j haf) (R.E i hfc) (R.E i hcd)) ≫
  R.cross i j haf hfc hab hbc ▷ R.E i hcd ≫
  Iso.hom (associator (R.E i hab) (R.E j hbc) (R.E i hcd))

/-- The ordered polynomial form implies the literal dotted braid field.
This conversion is made before any selected large action is substituted. -/
theorem rouquierMixedBraidEquation_of_polynomial
    (h : a₀ ≫ a₁ ≫ a₂ - b₀ ≫ b₁ ≫ b₂ =
      tripleDotCorrectionPolynomial (R := End (F₁ ≫ F₂ ≫ F₃)) D Sc i j
        (R.dot i hab ▷ (F₂ ≫ F₃)) (F₁ ◁ (R.dot j hbc ▷ F₃)) (F₁ ◁ F₂ ◁ R.dot i hcd)) :
    rouquierMixedBraidEquation D Sc R i j hab haf hbc hbe hfc hcd hed := by
  have hp := tripleDotCorrectionPolynomial_whiskers D Sc i j F₁ F₂ F₃
    (R.dot i hab) (R.dot j hbc) (R.dot i hcd)
  have hh := h.trans hp
  simpa only [rouquierMixedBraidEquation, Category.assoc] using hh

end OddMath.QuiverHecke.ELVOld
end

end

section

/-! # Chosen right contexts on the full-coefficient weight word family

SwappedVacuumCoordinates §§4–6: iterate the given E functors and existing
single-append charts on arbitrary full old-Hom arrows.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld.PowerWordWeightContexts
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

end OddMath.QuiverHecke.ELVOld.PowerWordWeightContexts
end

end

section

/-! # Coefficient insertion in signed word coordinates

SwappedVacuumCoordinates §§4–6: identify the genuine coefficient module
maps with the signed old-Hom operators before transporting chosen E values.
The full coefficient algebra and chronological multiplication are retained.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld.PowerWordCoefficients
open CyclotomicAction CyclotomicCrossingTensor
universe u
section Generic
variable {C : Type*} [Category* C]
private def conjugate {A B : C} (e : A ≅ B) (f : End B) : End A := e.hom ≫ f ≫ e.inv
private theorem conjugate_square {A B E : C} (e : A ≅ B) (f : B ≅ E)
    (x : End B) (y : End E) (h : x ≫ f.hom = f.hom ≫ y) :
    conjugate e x ≫ (e ≪≫ f).hom = (e ≪≫ f).hom ≫ y := by
  simp only [conjugate, Iso.trans_hom, Category.assoc, Iso.inv_hom_id_assoc]
  rw [h]
end Generic
private theorem mapped_square {C B : Type*} [Category* C] [Category* B]
    (F : C ⥤ B) {A P : C} {E : B} (e : A ≅ P) (f : F.obj P ≅ E)
    (x : End A) (y : End P) (z : End E)
    (hx : x ≫ e.hom = e.hom ≫ y) (hf : F.map y ≫ f.hom = f.hom ≫ z) :
    F.map x ≫ (F.mapIso e ≪≫ f).hom = (F.mapIso e ≪≫ f).hom ≫ z := by
  simp only [Iso.trans_hom, Functor.mapIso_hom, Category.assoc]
  rw [← Category.assoc, ← F.map_comp, hx, F.map_comp, Category.assoc, hf]

variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (L : I × ℕ → ℕ)

/-- The genuine full coefficient module action is the signed old-Hom
operator at every word, including inhomogeneous coefficients. -/
theorem coefficient_fromArrow (ν : List I)
    (a : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) :
    coefficientModuleAction D Sc cutoff (powerWordModule D Sc cutoff L ν) a =
      PowerWordMorphisms.fromArrow D Sc cutoff L ν ν (coefficientEndomorphism D Sc cutoff ν a) := by
  apply (PowerWordYoneda.homEquiv D Sc cutoff L ν (powerWordObject D Sc cutoff L ν)).injective
  change PowerWordYoneda.evaluate D Sc cutoff L ν (powerWordObject D Sc cutoff L ν)
      (coefficientModuleAction D Sc cutoff (powerWordModule D Sc cutoff L ν) a) =
    PowerWordYoneda.evaluate D Sc cutoff L ν (powerWordObject D Sc cutoff L ν)
      (PowerWordMorphisms.fromArrow D Sc cutoff L ν ν (coefficientEndomorphism D Sc cutoff ν a))
  rw [show PowerWordYoneda.evaluate D Sc cutoff L ν (powerWordObject D Sc cutoff L ν)
      (PowerWordMorphisms.fromArrow D Sc cutoff L ν ν (coefficientEndomorphism D Sc cutoff ν a)) =
    powerWordGenerator D Sc cutoff L ν (OldCategory.mk ν) (coefficientEndomorphism D Sc cutoff ν a) from
      PowerWordYoneda.evaluate_fromElement D Sc cutoff L ν (powerWordObject D Sc cutoff L ν) _]
  change (coefficientModuleAction D Sc cutoff (powerWordModule D Sc cutoff L ν) a).total (OldCategory.mk ν)
    (PowerWordYoneda.unitVector D Sc cutoff L ν) = _
  rw [coefficientModuleAction_total]
  change (powerWordModule D Sc cutoff L ν).map (coefficientEndomorphism D Sc cutoff ν a)
    (powerWordGenerator D Sc cutoff L ν (OldCategory.mk ν) (𝟙 _)) = _
  simpa only [Category.id_comp] using PowerWordYoneda.generator_naturality D Sc cutoff L ν
    (coefficientEndomorphism D Sc cutoff ν a) (𝟙 _)

section Weight
variable [Fintype I] (Λ : X)
local notation "N" => PowerWordContent.powerBound D cutoff L

end Weight
end OddMath.QuiverHecke.ELVOld.PowerWordCoefficients
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
end

end
