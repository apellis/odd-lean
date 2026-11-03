import OddMath.QuiverHecke.CyclotomicAction.ELVProbeWeightTripleCrossCoordinates
import OddMath.QuiverHecke.CyclotomicAction.ELVProbeEvaluatedStoredBraid
import OddMath.QuiverHecke.CyclotomicAction.ELVRouquierBraidEquation

/-! # The general braid for the chosen probe weight crossings

Brundan–Ellis (1.9), outside the repeated-outer correction case. Six
chosen crossing coordinates are compared in one stored append cube;
absent source coordinates retain the actual zero-object argument.
-/
noncomputable section
open scoped Classical
open CategoryTheory StringDiagrams Supercategory BicategoryStruct
namespace OddMath.QuiverHecke
open ELVOld CyclotomicAction
universe u

private theorem conjugate_three_paths {C : Type*} [Category* C]
    {A B C₀ D A' B' C' D' : C}
    (ha : A = A') (hb : B = B') (hc : C₀ = C') (hd : D = D')
    (f : A' ⟶ B') (g : B' ⟶ C') (h : C' ⟶ D') :
    (eqToHom ha ≫ f ≫ eqToHom hb.symm) ≫
      (eqToHom hb ≫ g ≫ eqToHom hc.symm) ≫
      (eqToHom hc ≫ h ≫ eqToHom hd.symm) =
        eqToHom ha ≫ (f ≫ g ≫ h) ≫ eqToHom hd.symm := by
  cases ha
  cases hb
  cases hc
  cases hd
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]

private theorem conjugated_three_path_eq
    {k C : Type*} [CommRing k] [Category* C] [Preadditive C] [Linear k C]
    {A B C₀ D E F S T : C} (hs : S = A) (ht : T = D)
    (a b c : k) (f₀ : A ⟶ B) (f₁ : B ⟶ C₀) (f₂ : C₀ ⟶ D)
    (g₀ : A ⟶ E) (g₁ : E ⟶ F) (g₂ : F ⟶ D)
    (h : (a • f₀) ≫ (b • f₁) ≫ (c • f₂) =
      (c • g₀) ≫ (b • g₁) ≫ (a • g₂)) :
    eqToHom hs ≫ ((a • f₀) ≫ (b • f₁) ≫ (c • f₂)) ≫ eqToHom ht.symm =
      eqToHom hs ≫ ((c • g₀) ≫ (b • g₁) ≫ (a • g₂)) ≫ eqToHom ht.symm := by
  exact congrArg (fun z : A ⟶ D => eqToHom hs ≫ z ≫ eqToHom ht.symm) h

private theorem total_three {k : Type u} [CommRing k]
    {A B : PiSCat.{u,u,u+1} k} {F₀ F₁ F₂ F₃ : A ⟶ B}
    (f : F₀ ⟶ F₁) (g : F₁ ⟶ F₂) (h : F₂ ⟶ F₃) (M : A) :
    (f ≫ g ≫ h).total M = f.total M ≫ g.total M ≫ h.total M := by
  rw [Superfunctor.comp_total, Superfunctor.comp_total]

attribute [local irreducible] probeEvaluatedAppendTo probeAppendToCrossComponent

variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (m : I → ℕ)
  (i j l : I) (Λ : X) {a bl bj bi clj cli cji d : X}
  (hal : a + D.α l = bl) (haj : a + D.α j = bj) (hai : a + D.α i = bi)
  (hlj : bl + D.α j = clj) (hli : bl + D.α i = cli) (hjl : bj + D.α l = clj)
  (hji : bj + D.α i = cji) (hil : bi + D.α l = cli) (hij : bi + D.α j = cji)
  (hd₁ : clj + D.α i = d) (hd₂ : cli + D.α j = d) (hd₃ : cji + D.α l = d)
local notation "Sc'" => parameterTwist D Sc
local notation "a₀" => probeOldWeightCrossSuffix D Sc' m i j l Λ hal hlj hli hd₁ hd₂
local notation "a₁" => probeOldWeightCrossPrefix D Sc' m j i l Λ hal hai hli hil hd₂
local notation "a₂" => probeOldWeightCrossSuffix D Sc' m j l i Λ hai hil hij hd₂ hd₃
local notation "b₀" => probeOldWeightCrossPrefix D Sc' m i j l Λ hal haj hlj hjl hd₁
local notation "b₁" => probeOldWeightCrossSuffix D Sc' m i l j Λ haj hjl hji hd₁ hd₃
local notation "b₂" => probeOldWeightCrossPrefix D Sc' m l i j Λ haj hai hji hij hd₃

variable (β : WeightBlocks D Λ a)
local notation "δl" => blockSucc D Λ l hal β
local notation "δj" => blockSucc D Λ j haj β
local notation "δi" => blockSucc D Λ i hai β
local notation "δlj" => blockSucc D Λ j hlj δl
local notation "δli" => blockSucc D Λ i hli δl
local notation "δji" => blockSucc D Λ i hji δj
local notation "ε" => probeOldBlockSucc₃ D i j l Λ hal hlj hd₁ β

/-- The entire three-crossing equation at each occupied output block. -/
theorem probeOldWeightGeneralBraid_component (hb : ¬ (i = l ∧ i ≠ j))
    (M : ProbeOldWeightProduct D Sc' m Λ a) :
    (a₀).total M ε ≫ (a₁).total M ε ≫ (a₂).total M ε =
      (b₀).total M ε ≫ (b₁).total M ε ≫ (b₂).total M ε := by
  have hjl' : blockSucc D Λ l hjl δj = δlj := by
    apply Subtype.ext
    change {l} + ({j} + β.1) = {j} + ({l} + β.1)
    ac_rfl
  have hil' : blockSucc D Λ l hil δi = δli := by
    apply Subtype.ext
    change {l} + ({i} + β.1) = {i} + ({l} + β.1)
    ac_rfl
  have hij' : blockSucc D Λ j hij δi = δji := by
    apply Subtype.ext
    change {j} + ({i} + β.1) = {i} + ({j} + β.1)
    ac_rfl
  have htopj : blockSucc D Λ j hd₂ δli = ε := by
    apply Subtype.ext
    change {j} + ({i} + ({l} + β.1)) = {i} + ({j} + ({l} + β.1))
    ac_rfl
  have htopl : blockSucc D Λ l hd₃ δji = ε := by
    apply Subtype.ext
    change {l} + ({i} + ({j} + β.1)) = {i} + ({j} + ({l} + β.1))
    ac_rfl
  have ha₀ := probeOldWeightCrossSuffix_via_total D Sc' m i j l Λ hal hlj hli hd₁ hd₂
    β δl δlj δli ε rfl rfl rfl rfl htopj M
  have ha₁ := probeOldWeightCrossPrefix_via_total D Sc' m j i l Λ hal hai hli hil hd₂
    β δl δi δli ε rfl rfl rfl hil' htopj M
  have ha₂ := probeOldWeightCrossSuffix_via_total D Sc' m j l i Λ hai hil hij hd₂ hd₃
    β δi δli δji ε rfl hil' hij' htopj htopl M
  have hb₀ := probeOldWeightCrossPrefix_via_total D Sc' m i j l Λ hal haj hlj hjl hd₁
    β δl δj δlj ε rfl rfl rfl hjl' rfl M
  have hb₁ := probeOldWeightCrossSuffix_via_total D Sc' m i l j Λ haj hjl hji hd₁ hd₃
    β δj δlj δji ε rfl hjl' rfl rfl htopl M
  have hb₂ := probeOldWeightCrossPrefix_via_total D Sc' m l i j Λ haj hai hji hij hd₃
    β δj δi δji ε rfl rfl rfl hij' htopl M
  rw [ha₀, ha₁, ha₂, hb₀, hb₁, hb₂]
  rw [conjugate_three_paths, conjugate_three_paths]
  have hB := probeStoredBraid D Sc m β.1.toList i j l
    (probeOldBlockTarget_perm D i Λ hai β δi rfl)
    (probeOldBlockTarget_perm D j Λ haj β δj rfl)
    (probeOldBlockTarget_perm D l Λ hal β δl rfl)
    (probeOldBlockTarget_perm D j Λ hij δi δji hij')
    (probeOldBlockTarget_perm D i Λ hji δj δji rfl)
    (probeOldBlockTarget_perm D l Λ hil δi δli hil')
    (probeOldBlockTarget_perm D i Λ hli δl δli rfl)
    (probeOldBlockTarget_perm D l Λ hjl δj δlj hjl')
    (probeOldBlockTarget_perm D j Λ hlj δl δlj rfl)
    (probeOldBlockTarget_perm D l Λ hd₃ δji ε htopl)
    (probeOldBlockTarget_perm D j Λ hd₂ δli ε htopj)
    (probeOldBlockTarget_perm D i Λ hd₁ δlj ε rfl) hb (M β)
  simp only [probeStoredBraidLeft, probeStoredBraidRight, Functor.map_smul] at hB ⊢
  exact conjugated_three_path_eq
    (probeOldWeightTripleVia_obj_eq D Sc' m i j l Λ hal hlj hd₁ β δl δlj ε rfl rfl rfl M)
    (probeOldWeightTripleVia_obj_eq D Sc' m l j i Λ hai hij hd₃ β δi δji ε rfl hij' htopl M)
    (if i = j then (-1 : k) else 1) (if i = l then (-1 : k) else 1)
    (if j = l then (-1 : k) else 1) _ _ _ _ _ _ hB.symm

/-- The chosen whole-weight uncorrected braid, including absent output coordinates. -/
theorem probeOldActionCross_generalBraid (hb : ¬ (i = l ∧ i ≠ j)) :
    a₀ ≫ a₁ ≫ a₂ = b₀ ≫ b₁ ≫ b₂ := by
  apply HomogeneousSuperfunctorIso.total_ext
  intro M
  funext η
  have hL := congrFun (total_three a₀ a₁ a₂ M) η
  have hR := congrFun (total_three b₀ b₁ b₂ M) η
  by_cases hs : ∃ γ, probeOldBlockSucc₃ D i j l Λ hal hlj hd₁ γ = η
  · obtain ⟨γ, rfl⟩ := hs
    exact hL.trans ((probeOldWeightGeneralBraid_component D Sc m i j l Λ
      hal haj hai hlj hli hjl hji hil hij hd₁ hd₂ hd₃ γ hb M).trans hR.symm)
  · exact hL.trans (((probeOldEFunctor_comp₃_isZero D Sc' m i j l Λ
      hal hlj hd₁ η hs M).eq_of_src _ _).trans hR.symm)

/-- The exact general-braid field on the independently chosen probe generator data. -/
theorem probeOldRouquierData_generalBraid (hb : ¬ (i = l ∧ i ≠ j)) :
    rouquierMulticolourBraidEquation D (probeOldRouquierData D Sc' m Λ)
      i j l hal haj hai hlj hli hjl hji hil hij hd₁ hd₂ hd₃ := by
  have h := probeOldActionCross_generalBraid D Sc m i j l Λ
    hal haj hai hlj hli hjl hji hil hij hd₁ hd₂ hd₃ hb
  simpa only [rouquierMulticolourBraidEquation, probeOldRouquierData,
    probeOldWeightCrossPrefix, probeOldWeightCrossSuffix, Category.assoc] using h

end OddMath.QuiverHecke
