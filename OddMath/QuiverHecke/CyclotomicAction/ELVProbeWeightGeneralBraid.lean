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

private theorem conjugate_eq {C : Type*} [Category* C]
    {S T A B : C} (hs : S = A) (ht : T = B) {f g : A ⟶ B} (h : f = g) :
    eqToHom hs ≫ f ≫ eqToHom ht.symm = eqToHom hs ≫ g ≫ eqToHom ht.symm :=
  congrArg (fun z : A ⟶ B => eqToHom hs ≫ z ≫ eqToHom ht.symm) h

private theorem three_path_transfer {C : Type*} [Category* C]
    {S S₁ S₂ T A A₁ A₂ B : C}
    (hs : S = A) (ha : S₁ = A₁) (hb : S₂ = A₂) (ht : T = B)
    (x₀ : A ⟶ A₁) (x₁ : A₁ ⟶ A₂) (x₂ : A₂ ⟶ B)
    (u₀ : S ⟶ S₁) (u₁ : S₁ ⟶ S₂) (u₂ : S₂ ⟶ T)
    (hu₀ : u₀ = eqToHom hs ≫ x₀ ≫ eqToHom ha.symm)
    (hu₁ : u₁ = eqToHom ha ≫ x₁ ≫ eqToHom hb.symm)
    (hu₂ : u₂ = eqToHom hb ≫ x₂ ≫ eqToHom ht.symm) :
    u₀ ≫ u₁ ≫ u₂ = eqToHom hs ≫ (x₀ ≫ x₁ ≫ x₂) ≫ eqToHom ht.symm := by
  rw [hu₀, hu₁, hu₂]
  exact conjugate_three_paths hs ha hb ht x₀ x₁ x₂

private theorem middle_map_path_transfer
    {k C V : Type*} [CommRing k] [Category* C] [Preadditive C] [Linear k C]
    [Category* V] [Preadditive V] [Linear k V]
    (F : V ⥤ C) [F.Linear k]
    {S S₁ S₂ T A B : C} {A₁ A₂ : V}
    (hs : S = A) (ha : S₁ = F.obj A₁) (hb : S₂ = F.obj A₂) (ht : T = B)
    (x₀ : A ⟶ F.obj A₁) (x₁ : A₁ ⟶ A₂) (x₂ : F.obj A₂ ⟶ B) (c : k)
    (u₀ : S ⟶ S₁) (u₁ : S₁ ⟶ S₂) (u₂ : S₂ ⟶ T)
    (hu₀ : u₀ = eqToHom hs ≫ x₀ ≫ eqToHom ha.symm)
    (hu₁ : u₁ = eqToHom ha ≫ F.map (c • x₁) ≫ eqToHom hb.symm)
    (hu₂ : u₂ = eqToHom hb ≫ x₂ ≫ eqToHom ht.symm) :
    u₀ ≫ u₁ ≫ u₂ = eqToHom hs ≫ (x₀ ≫ (c • F.map x₁) ≫ x₂) ≫ eqToHom ht.symm := by
  rw [← Functor.map_smul]
  exact three_path_transfer hs ha hb ht x₀ (F.map (c • x₁)) x₂ u₀ u₁ u₂ hu₀ hu₁ hu₂

private theorem outer_map_path_transfer
    {k C V W : Type*} [CommRing k] [Category* C] [Preadditive C] [Linear k C]
    [Category* V] [Preadditive V] [Linear k V]
    [Category* W] [Preadditive W] [Linear k W]
    (F : V ⥤ C) [F.Linear k] (G : W ⥤ C) [G.Linear k]
    {S S₁ S₂ T : C} {A A₁ : V} {A₂ B : W}
    (hs : S = F.obj A) (ha : S₁ = F.obj A₁) (hb : S₂ = G.obj A₂) (ht : T = G.obj B)
    (x₀ : A ⟶ A₁) (x₁ : F.obj A₁ ⟶ G.obj A₂) (x₂ : A₂ ⟶ B) (c₀ c₂ : k)
    (u₀ : S ⟶ S₁) (u₁ : S₁ ⟶ S₂) (u₂ : S₂ ⟶ T)
    (hu₀ : u₀ = eqToHom hs ≫ F.map (c₀ • x₀) ≫ eqToHom ha.symm)
    (hu₁ : u₁ = eqToHom ha ≫ x₁ ≫ eqToHom hb.symm)
    (hu₂ : u₂ = eqToHom hb ≫ G.map (c₂ • x₂) ≫ eqToHom ht.symm) :
    u₀ ≫ u₁ ≫ u₂ = eqToHom hs ≫ ((c₀ • F.map x₀) ≫ x₁ ≫ (c₂ • G.map x₂)) ≫ eqToHom ht.symm := by
  rw [← Functor.map_smul, ← Functor.map_smul]
  exact three_path_transfer hs ha hb ht (F.map (c₀ • x₀)) x₁ (G.map (c₂ • x₂))
    u₀ u₁ u₂ hu₀ hu₁ hu₂

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

private theorem right_path_coordinates
    (hil' : blockSucc D Λ l hil δi = δli)
    (hij' : blockSucc D Λ j hij δi = δji)
    (htopj : blockSucc D Λ j hd₂ δli = ε)
    (htopl : blockSucc D Λ l hd₃ δji = ε)
    (M : ProbeOldWeightProduct D Sc' m Λ a) :
    (a₀).total M ε ≫ (a₁).total M ε ≫ (a₂).total M ε =
      eqToHom (probeOldWeightTripleVia_obj_eq D Sc' m i j l Λ hal hlj hd₁ β δl δlj ε rfl rfl rfl M) ≫
        probeStoredBraidRight D Sc m β.1.toList i j l
          (probeOldBlockTarget_perm D i Λ hai β δi rfl)
          (probeOldBlockTarget_perm D l Λ hal β δl rfl)
          (probeOldBlockTarget_perm D j Λ hij δi δji hij')
          (probeOldBlockTarget_perm D l Λ hil δi δli hil')
          (probeOldBlockTarget_perm D i Λ hli δl δli rfl)
          (probeOldBlockTarget_perm D j Λ hlj δl δlj rfl)
          (probeOldBlockTarget_perm D l Λ hd₃ δji ε htopl)
          (probeOldBlockTarget_perm D j Λ hd₂ δli ε htopj)
          (probeOldBlockTarget_perm D i Λ hd₁ δlj ε rfl) (M β) ≫ eqToHom (probeOldWeightTripleVia_obj_eq D Sc' m l j i Λ hai hij hd₃ β δi δji ε rfl hij' htopl M).symm := by
  have ha₀ := probeOldWeightCrossSuffix_via_total D Sc' m i j l Λ hal hlj hli hd₁ hd₂
    β δl δlj δli ε rfl rfl rfl rfl htopj M
  have ha₁ := probeOldWeightCrossPrefix_via_total D Sc' m j i l Λ hal hai hli hil hd₂
    β δl δi δli ε rfl rfl rfl hil' htopj M
  have ha₂ := probeOldWeightCrossSuffix_via_total D Sc' m j l i Λ hai hil hij hd₂ hd₃
    β δi δli δji ε rfl hil' hij' htopj htopl M
  dsimp only [probeOldBlockTripleVia, probeOldBlockPairVia, probeOldBlockIndTo] at ha₀ ha₁ ha₂
  have hS := probeOldWeightTripleVia_obj_eq D Sc' m i j l Λ hal hlj hd₁
    β δl δlj ε rfl rfl rfl M
  have hA₁ := probeOldWeightTripleVia_obj_eq D Sc' m j i l Λ hal hli hd₂
    β δl δli ε rfl rfl htopj M
  have hA₂ := probeOldWeightTripleVia_obj_eq D Sc' m j l i Λ hai hil hd₂
    β δi δli ε rfl hil' htopj M
  have hT := probeOldWeightTripleVia_obj_eq D Sc' m l j i Λ hai hij hd₃
    β δi δji ε rfl hij' htopl M
  exact middle_map_path_transfer
    (probeEvaluatedAppendTo D Sc' m δli.1.toList j ε.1.toList
      (probeOldBlockTarget_perm D j Λ hd₂ δli ε htopj))
    hS hA₁ hA₂ hT _ _ _ _ ((a₀).total M ε) ((a₁).total M ε) ((a₂).total M ε)
    ha₀ ha₁ ha₂

private theorem left_path_coordinates
    (hjl' : blockSucc D Λ l hjl δj = δlj)
    (hij' : blockSucc D Λ j hij δi = δji)
    (htopl : blockSucc D Λ l hd₃ δji = ε)
    (M : ProbeOldWeightProduct D Sc' m Λ a) :
    (b₀).total M ε ≫ (b₁).total M ε ≫ (b₂).total M ε =
      eqToHom (probeOldWeightTripleVia_obj_eq D Sc' m i j l Λ hal hlj hd₁ β δl δlj ε rfl rfl rfl M) ≫
        probeStoredBraidLeft D Sc m β.1.toList i j l
          (probeOldBlockTarget_perm D i Λ hai β δi rfl)
          (probeOldBlockTarget_perm D j Λ haj β δj rfl)
          (probeOldBlockTarget_perm D l Λ hal β δl rfl)
          (probeOldBlockTarget_perm D j Λ hij δi δji hij')
          (probeOldBlockTarget_perm D i Λ hji δj δji rfl)
          (probeOldBlockTarget_perm D l Λ hjl δj δlj hjl')
          (probeOldBlockTarget_perm D j Λ hlj δl δlj rfl)
          (probeOldBlockTarget_perm D l Λ hd₃ δji ε htopl)
          (probeOldBlockTarget_perm D i Λ hd₁ δlj ε rfl) (M β) ≫ eqToHom (probeOldWeightTripleVia_obj_eq D Sc' m l j i Λ hai hij hd₃ β δi δji ε rfl hij' htopl M).symm := by
  have hb₀ := probeOldWeightCrossPrefix_via_total D Sc' m i j l Λ hal haj hlj hjl hd₁
    β δl δj δlj ε rfl rfl rfl hjl' rfl M
  have hb₁ := probeOldWeightCrossSuffix_via_total D Sc' m i l j Λ haj hjl hji hd₁ hd₃
    β δj δlj δji ε rfl hjl' rfl rfl htopl M
  have hb₂ := probeOldWeightCrossPrefix_via_total D Sc' m l i j Λ haj hai hji hij hd₃
    β δj δi δji ε rfl rfl rfl hij' htopl M
  dsimp only [probeOldBlockTripleVia, probeOldBlockPairVia, probeOldBlockIndTo] at hb₀ hb₁ hb₂
  have hS := probeOldWeightTripleVia_obj_eq D Sc' m i j l Λ hal hlj hd₁
    β δl δlj ε rfl rfl rfl M
  have hB₁ := probeOldWeightTripleVia_obj_eq D Sc' m i l j Λ haj hjl hd₁
    β δj δlj ε rfl hjl' rfl M
  have hB₂ := probeOldWeightTripleVia_obj_eq D Sc' m l i j Λ haj hji hd₃
    β δj δji ε rfl rfl htopl M
  have hT := probeOldWeightTripleVia_obj_eq D Sc' m l j i Λ hai hij hd₃
    β δi δji ε rfl hij' htopl M
  exact outer_map_path_transfer
    (probeEvaluatedAppendTo D Sc' m δlj.1.toList i ε.1.toList
      (probeOldBlockTarget_perm D i Λ hd₁ δlj ε rfl))
    (probeEvaluatedAppendTo D Sc' m δji.1.toList l ε.1.toList
      (probeOldBlockTarget_perm D l Λ hd₃ δji ε htopl))
    hS hB₁ hB₂ hT _ _ _ _ _ ((b₀).total M ε) ((b₁).total M ε) ((b₂).total M ε)
    hb₀ hb₁ hb₂

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
  rw [right_path_coordinates D Sc m i j l Λ hal haj hai hlj hli hji hil hij
    hd₁ hd₂ hd₃ β hil' hij' htopj htopl M,
    left_path_coordinates D Sc m i j l Λ hal haj hai hlj hjl hji hij
      hd₁ hd₃ β hjl' hij' htopl M]
  exact conjugate_eq
    (probeOldWeightTripleVia_obj_eq D Sc' m i j l Λ hal hlj hd₁ β δl δlj ε rfl rfl rfl M)
    (probeOldWeightTripleVia_obj_eq D Sc' m l j i Λ hai hij hd₃ β δi δji ε rfl hij' htopl M)
    (probeStoredBraid D Sc m β.1.toList i j l

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
          (probeOldBlockTarget_perm D i Λ hd₁ δlj ε rfl) hb (M β)).symm

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
  dsimp only [probeOldWeightCrossPrefix, probeOldWeightCrossSuffix] at h
  exact rouquierMulticolourBraidEquation_of_paths D (probeOldRouquierData D Sc' m Λ)
    i j l hal haj hai hlj hli hjl hji hil hij hd₁ hd₂ hd₃ h

end OddMath.QuiverHecke
