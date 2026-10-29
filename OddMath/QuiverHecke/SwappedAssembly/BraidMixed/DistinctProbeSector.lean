/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.SwappedAssembly.BraidMixed.ProbePairSector

/-! # Three distinct colours with two probe strands

The two-probe sector of the non-correction braid relation, with the target
probe order reversed. Endpoint equalities are retained in the sector paths.
-/

noncomputable section
namespace OddMath.QuiverHecke.SwappedAssembly
open CategoryTheory StringDiagrams OddMath.SKM
universe u
variable {I X : Type u} [AddCommGroup X] {k : Type u} [CommRing k]
  {B : Type u} [BicategoryStruct.{u, u} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear k (a ⟶ b)]
  [∀ a b : B, Supercategory k (a ⟶ b)] [TwoSupercategory k B]
  [∀ a b : B, PiSupercategory k (a ⟶ b)]
  {D : Datum I X} {Sc : Scalars D k}
namespace SPath
/-- A three-letter sector path with an explicit terminal equality. -/
def three {c₁ c₂ c₃ : Col I X} {s t : Sector I} (a b c : Bool)
    (ha : StepValid c₁.l a s) (hb : StepValid c₂.l b (nextSector c₁.l a s))
    (hc : StepValid c₃.l c (nextSector c₂.l b (nextSector c₁.l a s)))
    (e : nextSector c₃.l c (nextSector c₂.l b (nextSector c₁.l a s)) = t) :
    SPath [c₁, c₂, c₃] s t :=
  .cons _ a s ha (.cons _ b _ hb (.cons _ c _ hc (e ▸ .nil _)))

omit [AddCommGroup X] in
theorem exists_eq_three {c₁ c₂ c₃ : Col I X} {s t : Sector I}
    (p : SPath [c₁, c₂, c₃] s t) :
    ∃ a b c ha hb hc e, p = three (c₁ := c₁) (c₂ := c₂) (c₃ := c₃) a b c ha hb hc e := by
  cases p with
  | cons _ a _ ha p =>
    cases p with
    | cons _ b _ hb p =>
      cases p with
      | cons _ c _ hc p =>
        cases p
        exact ⟨a, b, c, ha, hb, hc, rfl, rfl⟩
end SPath
namespace ProbeReservoir

omit [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear k (a ⟶ b)]
  [∀ a b : B, Supercategory k (a ⟶ b)] [TwoSupercategory k B]
  [∀ a b : B, PiSupercategory k (a ⟶ b)] in
/-- For three distinct colours every sector path is determined by its endpoints. -/
theorem path_eq_three_distinct {i j r : I} (hij : i ≠ j) (hir : i ≠ r) (hjr : j ≠ r)
    {ν : X} {s t : Sector I} (p q : SPath (wd D ν [up i, up j, up r]) s t) : p = q := by
  obtain ⟨a, b, c, ha, hb, hc, e, rfl⟩ := SPath.exists_eq_three p
  obtain ⟨a', b', c', ha', hb', hc', e', rfl⟩ := SPath.exists_eq_three q
  have h := e.trans e'.symm
  have hi := congrArg (fun x : Sector I => x.1 i) h
  have hj := congrArg (fun x : Sector I => x.1 j) h
  have hr := congrArg (fun x : Sector I => x.1 r) h
  cases a <;> cases b <;> cases c <;> cases a' <;> cases b' <;> cases c' <;>
    first | rfl | (exfalso; simp [nextSector, hij, hir, hjr, Ne.symm hij, Ne.symm hir,
      Ne.symm hjr] at hi hj hr)

open BicategoryStruct Supercategory in
/-- Transport the target leg of a mixed-interchange triangle along an equality
of its final object. All transport maps remain explicit. -/
theorem mixedInterchange_pair_transport {a b b' c c' d e : B}
    (hc : c = c') (E₁ : a ⟶ b) (E₂ : b ⟶ c)
    (E₁' : a ⟶ b') (E₂' : b' ⟶ c) (E₂'' : b' ⟶ c')
    (hE : HEq E₂' E₂'') (Z : c ⟶ d) (Z' : c' ⟶ d) (hZ : HEq Z Z')
    (F : d ⟶ e) (κ κ' τ τ' ρ : ZMod 2) (hκ : κ = κ')
    (S : c ⟶ e) (hS : HEq S ((homParityShift (k := k) κ').obj (Z' ≫ F)))
    (eS : E₂' ≫ S = E₂'' ≫ (homParityShift (k := k) κ').obj (Z' ≫ F))
    (eZ : E₂' ≫ Z = E₂'' ≫ Z')
    {p : ZMod 2} (η : E₁ ≫ E₂ ⟶ E₁' ≫ E₂')
    (hη : η ∈ parity (R := k) _ _ p)
    (hsgn : koszulSign p κ * koszulSign ρ p = 1) :
    HEq
      (((associator E₁ E₂ S).inv ≫ η ▷ S ≫ (associator E₁' E₂' S).hom ≫
          E₁' ◁ eqToHom eS) ≫
        E₁' ◁ (homMixedInterchange (k := k) E₂'' F κ' τ' Z').hom ≫
        (homMixedInterchange (k := k) E₁' F τ' ρ (E₂'' ≫ Z')).hom)
      (E₁ ◁ (homMixedInterchange (k := k) E₂ F κ τ Z).hom ≫
        (homMixedInterchange (k := k) E₁ F τ ρ (E₂ ≫ Z)).hom ≫
        (homParityShift (k := k) ρ).map
          (((associator E₁ E₂ Z).inv ≫ η ▷ Z ≫ (associator E₁' E₂' Z).hom ≫
            E₁' ◁ eqToHom eZ) ▷ F)) := by
  subst hc
  cases hE
  cases hZ
  subst hκ
  cases hS
  simp only [eqToHom_refl, TwoSupercategory.whiskerLeft_id (R := k), Category.comp_id]
  apply heq_of_eq
  rw [homMixedInterchange_pair_cross _ _ _ _ _ _ _ _ _ _ hη, hsgn, one_smul]

variable (P : ProbeReservoir k B D Sc)

/-- The unequal-colour probe crossing passes through the two mixed interchanges.
The heterogeneous statement keeps the terminal sector transport explicit. -/
theorem preCrossNe_mixedJ_pair_heq (i j r : I) (s : Sector I)
    (hR : StepValid (true, r) false s)
    (hs : nextSector (true, j) true (nextSector (true, i) true s) =
      nextSector (true, i) true (nextSector (true, j) true s))
    (hsR : nextSector (true, j) true (nextSector (true, i) true (nextSector (true, r) false s)) =
      nextSector (true, i) true (nextSector (true, j) true (nextSector (true, r) false s)))
    (Z : P.H (nextSector (true, i) true (nextSector (true, j) true (nextSector (true, r) false s)))) :
    HEq
      (P.preCrossNe i j s hs ((P.step (true, r) false
          (nextSector (true, i) true (nextSector (true, j) true s)) hR).obj Z) ≫
        (P.step (true, j) true s trivial).map
          (P.mixedJ i r (nextSector (true, j) true s) hR Z).hom ≫
        (P.mixedJ j r s hR ((P.step (true, i) true _ trivial).obj Z)).hom)
      ((P.step (true, i) true s trivial).map
          (P.mixedJ j r (nextSector (true, i) true s) hR (hsR ▸ Z)).hom ≫
        (P.mixedJ i r s hR ((P.step (true, j) true _ trivial).obj (hsR ▸ Z))).hom ≫
        (P.step (true, r) false s hR).map
          (P.preCrossNe i j (nextSector (true, r) false s) hsR Z)) := by
  simp only [preCrossNe, mixedJ, step, homContentPreE, homContentPostE,
    Functor.comp_map, homPre, homPost, Functor.comp_obj]
  apply mixedInterchange_pair_transport
  · exact congrArg (fun t => P.T.obj (-P.muP t)) hs
  · exact P.probeE_heq i (congrArg (fun t => -P.muP t) hs) _ _
  · exact P.sector_heq hsR Z
  · exact congrArg (homContentShift D r) (congrArg Prod.fst hs)
  · exact P.sector_heq hs _
  · exact P.T.cross_mem j i _ _ _ _
  · exact homContentShift_pair_cross_sign j i r s.1

section Paths
variable (ν : X) (i j r : I) (s : Sector I) (hR : StepValid (true, r) false s)
  {t : Sector I}
  (e : nextSector (true, r) false (nextSector (true, j) true (nextSector (true, i) true s)) = t)

/-- The path `PᵢPⱼRᵣ`. -/
def distinctProbeSource : SPath (wd D ν [up i, up j, up r]) s t :=
  SPath.three true true false trivial trivial hR e
/-- The path `PᵢRᵣPⱼ`. -/
def distinctProbeMiddle : SPath (wd D ν [up i, up r, up j]) s t :=
  SPath.three true false true trivial hR trivial e
/-- The path `RᵣPᵢPⱼ`; exchange `i,j` for the braid target. -/
def distinctProbeTarget : SPath (wd D ν [up r, up i, up j]) s t :=
  SPath.three false true true hR trivial trivial e

variable (c : P.CrossCoeff Sc) (L : P.LeftwardData) (Z : P.H t)

/-- Move the reservoir through a probe pair without exchanging the probes. -/
theorem distinctProbe_move_heq (hir : i ≠ r) (hjr : j ≠ r) :
    HEq
      (crossEntry (P.swappedGens c L) ν [up i] j r []
          (distinctProbeSource ν i j r s hR e) (distinctProbeMiddle ν i j r s hR e) Z ≫
        crossEntry (P.swappedGens c L) ν [] i r [up j]
          (distinctProbeMiddle ν i j r s hR e) (distinctProbeTarget ν i j r s hR e) Z)
      ((P.step (true, i) true s trivial).map
          (P.mixedJ j r (nextSector (true, i) true s) hR (e ▸ Z)).hom ≫
        (P.mixedJ i r s hR ((P.step (true, j) true _ trivial).obj (e ▸ Z))).hom) := by
  subst e
  apply heq_of_eq
  apply congrArg₂ (· ≫ ·)
  · refine (crossEntry_right (P.swappedGens c L) ν i j r true trivial
      (.cons _ true _ trivial (.cons _ false _ hR (.nil _)))
      (.cons _ false _ hR (.cons _ true _ trivial (.nil _))) Z).trans ?_
    dsimp only [swappedGens]
    rw [P.crossImage_ne c hjr]
    rfl
  · refine (crossEntry_left (P.swappedGens c L) ν i r j
      (.cons _ true s trivial (.cons _ false _ hR (.nil _)))
      (.cons _ false s hR (.cons _ true _ trivial (.nil _)))
      (.cons _ true _ trivial (.nil _)) Z).trans ?_
    simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
    dsimp only [swappedGens]
    rw [P.crossImage_ne c hir]
    rfl

/-- The source path functor evaluated with its explicit terminal transport. -/
theorem distinctProbeSource_obj :
    (P.pathFunctor (distinctProbeSource (D := D) ν i j r s hR e)).obj Z =
      (P.step (true, i) true s trivial).obj
        ((P.step (true, j) true (nextSector (true, i) true s) trivial).obj
          ((P.step (true, r) false (nextSector (true, j) true (nextSector (true, i) true s)) hR).obj (e ▸ Z))) := by
  subst e
  rfl

/-- The target path functor evaluated with its explicit terminal transport. -/
theorem distinctProbeTarget_obj :
    (P.pathFunctor (distinctProbeTarget (D := D) ν i j r s hR e)).obj Z =
      (P.step (true, r) false s hR).obj
        ((P.step (true, i) true _ trivial).obj
          ((P.step (true, j) true _ trivial).obj (e ▸ Z))) := by
  subst e
  rfl
end Paths

section Transport
variable {C : Type*} [Category C]
/-- Equality transports around a morphism are heterogeneously trivial. -/
theorem sandwich_heq {A A' B B' : C} (hA : A = A') (hB : B = B') (f : A' ⟶ B) :
    HEq (eqToHom hA ≫ f ≫ eqToHom hB) f := by
  subst hA hB
  simp

/-- A functor preserves a heterogeneously equal morphism after its endpoints are aligned. -/
theorem map_of_heq {E : Type*} [Category E] (F : C ⥤ E) {A A' B B' : C}
    (hA : A = A') (hB : B = B') {f : A ⟶ B} {g : A' ⟶ B'} (h : HEq f g) :
    HEq (F.map f) (F.map g) := by
  subst hA hB
  cases h
  rfl

/-- An interchange rectangle transports along equalities of its four vertices.
Its two raw source vertices need only be equal to the common sector object. -/
theorem rectangle_of_heq {A B C₀ D₀ A₁ A₂ B₁ C₁ D₁ : C}
    (hA₁ : A = A₁) (hA₂ : A = A₂) (hB : B = B₁) (hC : C₀ = C₁) (hD : D₀ = D₁)
    {f : A ⟶ B} {g : B ⟶ D₀} {h : A ⟶ C₀} {l : C₀ ⟶ D₀}
    {f' : A₁ ⟶ B₁} {g' : B₁ ⟶ D₁} {h' : A₂ ⟶ C₁} {l' : C₁ ⟶ D₁}
    (hf : HEq f f') (hg : HEq g g') (hh : HEq h h') (hl : HEq l l')
    (hsq : HEq (f' ≫ g') (h' ≫ l')) : f ≫ g = h ≫ l := by
  subst hA₁ hA₂ hB hC hD
  cases hf
  cases hg
  cases hh
  cases hl
  exact eq_of_heq hsq
end Transport

section ProbeEdges
variable (ν : X) (i j r : I) (s : Sector I) (hR : StepValid (true, r) false s)
  (hs : nextSector (true, j) true (nextSector (true, i) true s) =
    nextSector (true, i) true (nextSector (true, j) true s))
  (hsR : nextSector (true, r) false (nextSector (true, j) true (nextSector (true, i) true s)) =
    nextSector (true, r) false (nextSector (true, i) true (nextSector (true, j) true s)))
  (c : P.CrossCoeff Sc) (L : P.LeftwardData)
  (Z : P.H (nextSector (true, r) false (nextSector (true, i) true (nextSector (true, j) true s))))

/-- The left probe crossing, including its source-object transport. -/
theorem distinctProbe_left (hij : i ≠ j) (hir : i ≠ r) (hjr : j ≠ r) :
    (P.pathFunctor (distinctProbeSource (D := D) ν i j r s hR hsR)).obj Z =
        (P.step (true, i) true s trivial).obj
          ((P.step (true, j) true (nextSector (true, i) true s) trivial).obj
            (hs ▸ (P.step (true, r) false
              (nextSector (true, i) true (nextSector (true, j) true s)) hR).obj Z)) ∧
    HEq (crossEntry (P.swappedGens c L) ν [] i j [up r]
      (distinctProbeSource ν i j r s hR hsR) (distinctProbeSource ν j i r s hR rfl) Z)
      (P.preCrossNe i j s hs ((P.step (true, r) false
        (nextSector (true, i) true (nextSector (true, j) true s)) hR).obj Z)) := by
  let pg : SPath (wd D (SKM.wt D ν [up r]) [up i, up j]) s
      (nextSector (true, i) true (nextSector (true, j) true s)) :=
    SPath.two true true trivial trivial hs
  let qg : SPath (wd D (SKM.wt D ν [up r]) [up j, up i]) s
      (nextSector (true, i) true (nextSector (true, j) true s)) :=
    SPath.two true true trivial trivial rfl
  let pv : SPath (wd D ν [up r])
      (nextSector (true, i) true (nextSector (true, j) true s))
      (nextSector (true, r) false (nextSector (true, i) true (nextSector (true, j) true s))) :=
    .cons _ false _ hR (.nil _)
  have hp : distinctProbeSource (D := D) ν i j r s hR hsR = pg.append pv :=
    path_eq_three_distinct hij hir hjr _ _
  have hq : distinctProbeSource (D := D) ν j i r s hR rfl = qg.append pv := rfl
  rw [hp, hq]
  constructor
  · rw [P.pathFunctor_append]
    exact P.pathFunctor_two_obj
      (c₁ := ⟨up i, SKM.wt D (SKM.wt D ν [up r]) [up j]⟩)
      (c₂ := ⟨up j, SKM.wt D (SKM.wt D ν [up r]) []⟩)
      true true trivial trivial hs _ _ (P.sector_heq hs _)
  · rw [crossEntry_left]
    refine (sandwich_heq _ _ _).trans ?_
    dsimp only [swappedGens]
    rw [P.crossImage_ne c hij]
    exact P.twoTwo_two_heq
      ⟨up i, SKM.wt D (SKM.wt D ν [up r]) [up j]⟩ ⟨up j, SKM.wt D ν [up r]⟩
      ⟨up j, SKM.wt D (SKM.wt D ν [up r]) [up i]⟩ ⟨up i, SKM.wt D ν [up r]⟩
      (P.crossNeEntry i j _ _ _ _) (t := s) true true true true
      trivial trivial trivial trivial hs rfl rfl _ _ HEq.rfl

/-- The right probe crossing with the reservoir as spectator. -/
theorem distinctProbe_right (hij : i ≠ j) :
    HEq (crossEntry (P.swappedGens c L) ν [up r] i j []
      (distinctProbeTarget ν i j r s hR hsR) (distinctProbeTarget ν j i r s hR rfl) Z)
      ((P.step (true, r) false s hR).map
        (P.preCrossNe i j (nextSector (true, r) false s) hsR Z)) := by
  dsimp only [distinctProbeTarget, SPath.three]
  rw [crossEntry_right]
  apply map_of_heq _ (P.pathFunctor_two_obj
    (c₁ := ⟨up i, SKM.wt D ν [up j]⟩) (c₂ := ⟨up j, SKM.wt D ν []⟩)
    (t := nextSector (true, r) false s)
    true true trivial trivial hsR Z _ (P.sector_heq hsR Z)) rfl
  dsimp only [swappedGens]
  rw [P.crossImage_ne c hij]
  exact P.twoTwo_two_heq
    ⟨up i, SKM.wt D ν [up j]⟩ ⟨up j, ν⟩
    ⟨up j, SKM.wt D ν [up i]⟩ ⟨up i, ν⟩
    (P.crossNeEntry i j _ _ _ _) (t := nextSector (true, r) false s)
    true true true true trivial trivial trivial trivial hsR rfl rfl Z Z HEq.rfl
end ProbeEdges

/-- The sector `PᵢPⱼRᵣ → RᵣPⱼPᵢ` of `CrossBraid.braid` for three distinct colours.
No crossing, mixed parameter polynomial, or factor braid is assumed invertible. -/
theorem distinctProbe_braid (ν : X) (i j r : I) (s : Sector I)
    (hR : StepValid (true, r) false s) (c : P.CrossCoeff Sc) (L : P.LeftwardData)
    (hij : i ≠ j) (hir : i ≠ r) (hjr : j ≠ r)
    (hsR : nextSector (true, r) false (nextSector (true, j) true (nextSector (true, i) true s)) =
      nextSector (true, r) false (nextSector (true, i) true (nextSector (true, j) true s)))
    (Z : P.H (nextSector (true, r) false (nextSector (true, i) true (nextSector (true, j) true s)))) :
    braidLeft (P.swappedGens c L) i j r ν
      (distinctProbeSource ν i j r s hR hsR) (distinctProbeTarget ν j i r s hR rfl) Z =
    braidRight (P.swappedGens c L) i j r ν
      (distinctProbeSource ν i j r s hR hsR) (distinctProbeTarget ν j i r s hR rfl) Z := by
  classical
  have hs : nextSector (true, j) true (nextSector (true, i) true s) =
      nextSector (true, i) true (nextSector (true, j) true s) := by
    simp only [nextSector, add_right_comm]
  let t := nextSector (true, r) false (nextSector (true, i) true (nextSector (true, j) true s))
  let : Subsingleton (SPath (wd D ν [up j, up i, up r]) s t) :=
    ⟨path_eq_three_distinct hij.symm hjr hir⟩
  let : Subsingleton (SPath (wd D ν [up j, up r, up i]) s t) :=
    ⟨path_eq_three_distinct hjr hij.symm hir.symm⟩
  let : Subsingleton (SPath (wd D ν [up i, up r, up j]) s t) :=
    ⟨path_eq_three_distinct hir hij hjr.symm⟩
  let : Subsingleton (SPath (wd D ν [up r, up i, up j]) s t) :=
    ⟨path_eq_three_distinct hir.symm hjr.symm hij⟩
  let := Fintype.ofFinite (SPath (wd D ν [up j, up i, up r]) s t)
  let := Fintype.ofFinite (SPath (wd D ν [up j, up r, up i]) s t)
  let := Fintype.ofFinite (SPath (wd D ν [up i, up r, up j]) s t)
  let := Fintype.ofFinite (SPath (wd D ν [up r, up i, up j]) s t)
  unfold braidLeft braidRight
  rw [Fintype.sum_subsingleton _ (distinctProbeMiddle (D := D) ν j i r s hR rfl),
    Fintype.sum_subsingleton _ (distinctProbeSource (D := D) ν j i r s hR rfl),
    Fintype.sum_subsingleton _ (distinctProbeTarget (D := D) ν i j r s hR hsR),
    Fintype.sum_subsingleton _ (distinctProbeMiddle (D := D) ν i j r s hR hsR)]
  rw [Category.assoc]
  obtain ⟨hA, hf⟩ := P.distinctProbe_left ν i j r s hR hs hsR c L Z hij hir hjr
  exact rectangle_of_heq hA (P.distinctProbeSource_obj ν i j r s hR hsR Z) rfl
    (P.distinctProbeTarget_obj ν i j r s hR hsR Z) rfl hf
    (P.distinctProbe_move_heq ν j i r s hR rfl c L Z hjr hir)
    (P.distinctProbe_move_heq ν i j r s hR hsR c L Z hir hjr)
    (P.distinctProbe_right ν i j r s hR hsR c L Z hij)
    (by simpa only [Category.assoc] using P.preCrossNe_mixedJ_pair_heq i j r s hR hs hsR Z)

end ProbeReservoir
end OddMath.QuiverHecke.SwappedAssembly
