import Mathlib.Data.List.Induction
import OddMath.Algebra.FiniteSupermoduleFunctor
import OddMath.QuiverHecke.CyclotomicAction.WeightPair.WeightQuadratic
import OddMath.QuiverHecke.SwappedAssembly.ReservoirWordFunctor

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
namespace OddMath.QuiverHecke.ELV
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

end OddMath.QuiverHecke.ELV
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
namespace OddMath.QuiverHecke.ELV
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
end OddMath.QuiverHecke.ELV
end

end

section

/-! # The uncorrected multicolour braid equation of Rouquier data

Brundan--Ellis (1.9). Capture the literal RouquierMulticolour.braid formula
before specializing large chosen action data.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory BicategoryStruct
namespace OddMath.QuiverHecke.ELV
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

end OddMath.QuiverHecke.ELV
end

end

section

/-! # The dotted mixed braid equation of Rouquier data

Brundan--Ellis (1.9). Keep the exact RouquierMulticolour.braidEq formula
as one generic proposition before specializing large selected functors.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory BicategoryStruct
namespace OddMath.QuiverHecke.ELV
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

end OddMath.QuiverHecke.ELV
end

end
