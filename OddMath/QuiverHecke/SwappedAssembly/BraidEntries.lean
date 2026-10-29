/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.SwappedAssembly.CrossEntries

/-! # Entries of the whiskered crossings of a three-letter word

The braid relation (1.9) of Brundan–Ellis, *Super Kac–Moody 2-categories*, arXiv:1701.04133v2,
Definition 1.5, is evaluated in the swapped layer representation through the entries
`crossEntry` of a crossing on two adjacent strands of a three-letter word (`braidLeft`,
`braidRight`). This file reduces those entries to the crossing image:

* a crossing on the left two strands, `crossEntry ν [] i j [up k]`, is the crossing image of
  the left two summands applied at the object of the third summand, and vanishes unless the
  two paths have the same third summand (`crossEntry_left`, `crossEntry_left_eq_zero`);
* a crossing on the right two strands, `crossEntry ν [up a] i j []`, is the image under the
  step functor of the first summand of the crossing image of the right two summands, and
  vanishes unless the two paths have the same first summand (`crossEntry_right`,
  `crossEntry_right_eq_zero`).
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

namespace ProbeReservoir

variable {P : ProbeReservoir k B D Sc}

/-- **A crossing on the left two strands** of a three-letter word: the crossing image of the
left two summands, applied at the object of the third summand. -/
theorem crossEntry_left (gens : P.Generators) (ν : X) (i j k' : I) {s y t : Sector I}
    (pg : SPath (wd D (SKM.wt D ν [up k']) [up i, up j]) s y)
    (qg : SPath (wd D (SKM.wt D ν [up k']) [up j, up i]) s y)
    (pv : SPath (wd D ν [up k']) y t) (Z : P.H t) :
    crossEntry gens ν [] i j [up k'] (pg.append pv) (qg.append pv) Z =
      eqToHom (by rw [P.pathFunctor_append]; rfl) ≫
        gens.cross i j (SKM.wt D ν [up k']) pg qg ((P.pathFunctor pv).obj Z) ≫
        eqToHom (by rw [P.pathFunctor_append]; rfl) := by
  unfold crossEntry
  show compList gens (a := SKM.ob D ν [up i, up j, up k']) (b := SKM.ob D ν [up j, up i, up k'])
    [SKM.lay D ν [] (SKM.Shape.cross i j) [up k']] _ _ _ Z = _
  erw [compList_one]
  simp only [SPath.cast_self, eqToHom_refl, Category.id_comp, Category.comp_id]
  refine (compLayer_eq_of_path gens (SKM.lay D ν [] (SKM.Shape.cross i j) [up k']) (.nil s)
    pg qg pv _ _ rfl rfl Z).trans ?_
  rfl

/-- The entry of a layer vanishes at any two paths whose decompositions have different outer
parts. -/
theorem compLayer_eq_zero_of_path (gens : P.Generators) (L : Layer (SKM.sig D))
    {s t : Sector I} (d : SPath.Dec L.left ((SKM.sig D).dom L.gen) L.right s t)
    (e : SPath.Dec L.left ((SKM.sig D).cod L.gen) L.right s t) (hne : d.outer ≠ e.outer)
    (p : SPath L.dom.word s t) (q : SPath L.cod.word s t) (hp : d.path = p) (hq : e.path = q)
    (Z : P.H t) : compLayer gens L p q Z = 0 := by
  subst hp hq
  exact compLayer_eq_zero gens L d e hne Z

omit [AddCommGroup X] in
/-- Two paths that differ only in the weight label of their first letter, when the labels are
equal. -/
theorem SPath.heq_cons_col {a : Letter I} {x y : X} {w : List (Col I X)} {s t : Sector I}
    (σ : Bool) (hv : StepValid a σ s) (p : SPath w (nextSector a σ s) t) (h : x = y) :
    HEq (SPath.cons ⟨a, x⟩ σ s hv p) (SPath.cons ⟨a, y⟩ σ s hv p) := by
  subst h; rfl

/-- The entry of a layer at transported paths given by a decomposition. -/
theorem compLayer_cast_eq_of_path (gens : P.Generators) (L : Layer (SKM.sig D))
    {w₁ w₂ : List (Col I X)} (h₁ : w₁ = L.dom.word) (h₂ : w₂ = L.cod.word)
    {s x y t : Sector I} (pu : SPath L.left s x) (pg : SPath ((SKM.sig D).dom L.gen) x y)
    (qg : SPath ((SKM.sig D).cod L.gen) x y) (pv : SPath L.right y t)
    (p : SPath w₁ s t) (q : SPath w₂ s t) (hp : HEq ((pu.append pg).append pv) p)
    (hq : HEq ((pu.append qg).append pv) q) (Z : P.H t) :
    compLayer gens L (p.cast h₁) (q.cast h₂) Z =
      eqToHom (by subst h₁; rw [SPath.cast_rfl, ← eq_of_heq hp,
          P.pathFunctor_append_append_obj]) ≫
        (P.pathFunctor pu).map (gens.image L.gen pg qg ((P.pathFunctor pv).obj Z)) ≫
        eqToHom (by subst h₂; rw [SPath.cast_rfl, ← eq_of_heq hq,
          P.pathFunctor_append_append_obj]) := by
  subst h₁ h₂
  obtain rfl := eq_of_heq hp
  obtain rfl := eq_of_heq hq
  exact compLayer_eq gens L pu pg qg pv Z

/-- The entry of a layer vanishes at transported paths given by decompositions with different
outer parts. -/
theorem compLayer_cast_eq_zero_of_path (gens : P.Generators) (L : Layer (SKM.sig D))
    {w₁ w₂ : List (Col I X)} (h₁ : w₁ = L.dom.word) (h₂ : w₂ = L.cod.word) {s t : Sector I}
    (d : SPath.Dec L.left ((SKM.sig D).dom L.gen) L.right s t)
    (e : SPath.Dec L.left ((SKM.sig D).cod L.gen) L.right s t) (hne : d.outer ≠ e.outer)
    (p : SPath w₁ s t) (q : SPath w₂ s t) (hp : HEq d.path p) (hq : HEq e.path q)
    (Z : P.H t) : compLayer gens L (p.cast h₁) (q.cast h₂) Z = 0 := by
  subst h₁ h₂
  obtain rfl := eq_of_heq hp
  obtain rfl := eq_of_heq hq
  exact compLayer_eq_zero gens L d e hne Z

/-- A crossing on the left two strands vanishes between paths with different third
summands. -/
theorem crossEntry_left_eq_zero (gens : P.Generators) (ν : X) (i j k' : I) {s y y' t : Sector I}
    (pg : SPath (wd D (SKM.wt D ν [up k']) [up i, up j]) s y)
    (qg : SPath (wd D (SKM.wt D ν [up k']) [up j, up i]) s y')
    (pv : SPath (wd D ν [up k']) y t) (pv' : SPath (wd D ν [up k']) y' t)
    (hne : (⟨y, pv⟩ : Σ z, SPath (wd D ν [up k']) z t) ≠ ⟨y', pv'⟩) (Z : P.H t) :
    crossEntry gens ν [] i j [up k'] (pg.append pv) (qg.append pv') Z = 0 := by
  unfold crossEntry
  show compList gens (a := SKM.ob D ν [up i, up j, up k']) (b := SKM.ob D ν [up j, up i, up k'])
    [SKM.lay D ν [] (SKM.Shape.cross i j) [up k']] _ _ _ Z = _
  erw [compList_one]
  simp only [SPath.cast_self, eqToHom_refl, Category.id_comp, Category.comp_id]
  exact compLayer_eq_zero_of_path gens (SKM.lay D ν [] (SKM.Shape.cross i j) [up k'])
    ⟨(s, y), .nil s, pg, pv⟩ ⟨(s, y'), .nil s, qg, pv'⟩
    (fun h => hne (congrArg Prod.snd h)) _ _ rfl rfl Z

/-- **A crossing on the right two strands** of a three-letter word: the image under the step
functor of the first summand of the crossing image of the right two summands. -/
theorem crossEntry_right (gens : P.Generators) (ν : X) (a i j : I) {s t : Sector I} (σ : Bool)
    (hv : StepValid (true, a) σ s)
    (pg : SPath (wd D ν [up i, up j]) (nextSector (true, a) σ s) t)
    (qg : SPath (wd D ν [up j, up i]) (nextSector (true, a) σ s) t) (Z : P.H t) :
    crossEntry gens ν [up a] i j [] (.cons ⟨up a, SKM.wt D ν [up i, up j]⟩ σ s hv pg)
        (.cons ⟨up a, SKM.wt D ν [up j, up i]⟩ σ s hv qg) Z =
      (P.step (true, a) σ s hv).map (gens.cross i j ν pg qg Z) := by
  unfold crossEntry
  show compList gens (a := SKM.ob D ν [up a, up i, up j]) (b := SKM.ob D ν [up a, up j, up i])
    [SKM.lay D ν [up a] (SKM.Shape.cross i j) []] _ _ _ Z = _
  erw [compList_one]
  rw [compLayer_cast_eq_of_path gens (SKM.lay D ν [up a] (SKM.Shape.cross i j) []) _ _
    (.cons ⟨up a, SKM.wt D ν [up i, up j]⟩ σ s hv (.nil _)) pg qg (.nil t) _ _
    (heq_of_eq (congrArg (SPath.cons _ σ s hv) (SPath.append_nil_pair pg)))
    ((heq_of_eq (congrArg (SPath.cons _ σ s hv) (SPath.append_nil_pair qg))).trans
      (SPath.heq_cons_col σ hv qg (by simp [add_left_comm]))) Z]
  simp only [Category.assoc, eqToHom_trans, eqToHom_refl, Category.id_comp, Category.comp_id]
  rfl

/-- A crossing on the right two strands vanishes between paths with different first
summands. -/
theorem crossEntry_right_eq_zero (gens : P.Generators) (ν : X) (a i j : I) {s t : Sector I}
    (σ τ : Bool) (hστ : σ ≠ τ) (hv : StepValid (true, a) σ s) (hw : StepValid (true, a) τ s)
    (pg : SPath (wd D ν [up i, up j]) (nextSector (true, a) σ s) t)
    (qg : SPath (wd D ν [up j, up i]) (nextSector (true, a) τ s) t) (Z : P.H t) :
    crossEntry gens ν [up a] i j [] (.cons ⟨up a, SKM.wt D ν [up i, up j]⟩ σ s hv pg)
        (.cons ⟨up a, SKM.wt D ν [up j, up i]⟩ τ s hw qg) Z = 0 := by
  unfold crossEntry
  show compList gens (a := SKM.ob D ν [up a, up i, up j]) (b := SKM.ob D ν [up a, up j, up i])
    [SKM.lay D ν [up a] (SKM.Shape.cross i j) []] _ _ _ Z = _
  erw [compList_one]
  rw [compLayer_cast_eq_zero_of_path gens (SKM.lay D ν [up a] (SKM.Shape.cross i j) []) _ _
    ⟨(_, t), .cons ⟨up a, SKM.wt D ν [up i, up j]⟩ σ s hv (.nil _), pg, .nil t⟩
    ⟨(_, t), .cons ⟨up a, SKM.wt D ν [up i, up j]⟩ τ s hw (.nil _), qg, .nil t⟩
    (fun h => hστ (by
      have h1 := congrArg Prod.fst h
      simp only [SPath.Dec.outer] at h1
      obtain ⟨h2, h3⟩ := Sigma.mk.inj_iff.mp h1
      cases σ <;> cases τ <;> simp_all)) _ _
    (heq_of_eq (congrArg (SPath.cons _ σ s hv) (SPath.append_nil_pair pg)))
    ((heq_of_eq (congrArg (SPath.cons _ τ s hw) (SPath.append_nil_pair qg))).trans
      (SPath.heq_cons_col τ hw qg (by simp [add_left_comm]))) Z]
  simp

end ProbeReservoir

end OddMath.QuiverHecke.SwappedAssembly
