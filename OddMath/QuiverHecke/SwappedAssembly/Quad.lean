/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.SwappedAssembly.Zigzag

/-! # The quadratic relations in the swapped layer representation

The relations `quadEq`, `quadZero` and `quadNe` of `OddMath.SKM.Presentation` are (1.7) of
Brundan–Ellis, *Super Kac–Moody 2-categories*, arXiv:1701.04133v2, Definition 1.5: the square
of the upward crossing `τ : Eᵢ Eⱼ → Eⱼ Eᵢ` followed by `τ : Eⱼ Eᵢ → Eᵢ Eⱼ` is `0` for `i = j`,
`t_ij` for `d_ij = 0`, and the parameter polynomial `Q_ij` in the dots otherwise.

In the swapped layer representation each relation is one matrix identity per pair of
summand paths `p`, `q` of the word `Eᵢ Eⱼ` and object `Z`. The entry of the two-crossing
diagram is the matrix product `crossCross`: the sum over the summand paths `m` of `Eⱼ Eᵢ` of the
two crossing entries (`compList_crossCross`). The entries of the dots on one strand of a
two-letter word are the dot image on that strand, conjugated by the comparison of the path
functor of the word with the composite of the path functors of its letters (`leftDot`,
`rightDot`, `compDiag_leftDots`, `compDiag_rightDots`).

`CrossQuad gens` states the three matrix identities; `quadRelations` derives
`QuadRelations` from it.

Main declarations: `ProbeReservoir.compLayer_eq_of_path`, `ProbeReservoir.crossCross`,
`ProbeReservoir.CrossQuad`, `ProbeReservoir.quadRelations`.
-/

noncomputable section

namespace OddMath.QuiverHecke.SwappedAssembly

open CategoryTheory StringDiagrams OddMath.SKM

universe u uB v w

variable {I X : Type u}

namespace SPath

/-- Appending the empty path to a path of a two-letter word. -/
theorem append_nil_pair {c₁ c₂ : Col I X} {s t : Sector I} (p : SPath [c₁, c₂] s t) :
    p.append (.nil t) = p := by
  cases p with
  | cons _ _ _ _ p =>
    cases p with
    | cons _ _ _ _ p =>
      cases p
      rfl

end SPath

variable [AddCommGroup X] {k : Type u} [CommRing k]
  {B : Type uB} [BicategoryStruct.{w, v} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear k (a ⟶ b)]
  [∀ a b : B, Supercategory k (a ⟶ b)] [TwoSupercategory k B]
  [∀ a b : B, PiSupercategory k (a ⟶ b)]
  {D : Datum I X} {Sc : Scalars D k}

namespace ProbeReservoir

variable {P : ProbeReservoir k B D Sc}

/-- **The entry of a layer at paths with given decompositions**: the image of the generator
in the middle, conjugated by the comparisons of the path functors. -/
theorem compLayer_eq_of_path (gens : P.Generators) (L : Layer (SKM.sig D))
    {s x y t : Sector I} (pu : SPath L.left s x) (pg : SPath ((SKM.sig D).dom L.gen) x y)
    (qg : SPath ((SKM.sig D).cod L.gen) x y) (pv : SPath L.right y t)
    (p : SPath L.dom.word s t) (q : SPath L.cod.word s t) (hp : (pu.append pg).append pv = p)
    (hq : (pu.append qg).append pv = q) (Z : P.H t) :
    compLayer gens L p q Z =
      eqToHom (by rw [← hp, P.pathFunctor_append_append_obj]) ≫
        (P.pathFunctor pu).map (gens.image L.gen pg qg ((P.pathFunctor pv).obj Z)) ≫
        eqToHom (by rw [← hq, P.pathFunctor_append_append_obj]) := by
  subst hp hq
  exact compLayer_eq gens L pu pg qg pv Z

open Classical in
/-- **The entry of a composite chain** is the matrix product of the entries of its parts. -/
theorem compList_append (gens : P.Generators) (ls ms : List (Layer (SKM.sig D)))
    {a b c : Obj (SKM.sig D)} (h₁ : Chain a ls b) (h₂ : Chain b ms c) (h : Chain a (ls ++ ms) c)
    {s t : Sector I} (p : SPath a.word s t) (q : SPath c.word s t) (Z : P.H t) :
    letI := Fintype.ofFinite (SPath b.word s t)
    compList gens (ls ++ ms) h p q Z =
      ∑ m, compList gens ls h₁ p m Z ≫ compList gens ms h₂ m q Z := by
  induction ls generalizing a with
  | nil =>
    obtain rfl : a = b := h₁
    simp only [compList.eq_1, SPath.cast_self, dite_comp, Limits.zero_comp,
      Finset.sum_dite_eq, Finset.mem_univ, ↓reduceIte, eqToHom_refl, Category.id_comp]
    rfl
  | cons L ls ih =>
    obtain ⟨hv, rfl, hc⟩ := h₁
    erw [compList_cons gens L (ls ++ ms) hv (hc.append h₂)]
    simp only [compList.eq_2, SPath.cast_self, eqToHom_refl, Category.id_comp,
      Preadditive.sum_comp, Category.assoc]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun pm _ => ?_
    rw [ih hc (hc.append h₂) pm, Preadditive.comp_sum]

/-- The entry of a dot layer vanishes off the diagonal. -/
theorem compLayer_dot_eq_zero (gens : P.Generators) (μ : X) (u : List (Letter I)) (i : I)
    (v : List (Letter I)) {s t : Sector I}
    (p q : SPath (SKM.lay D μ u (SKM.Shape.dot i) v).dom.word s t) (hpq : p ≠ q) (Z : P.H t) :
    compLayer gens (SKM.lay D μ u (SKM.Shape.dot i) v) p q Z = 0 := by
  obtain ⟨d, rfl⟩ : ∃ d, SPath.Dec.path d = p := ⟨_, SPath.path_decOf _ _ p⟩
  obtain ⟨e, rfl⟩ : ∃ e, SPath.Dec.path
      (m := (SKM.sig D).cod (SKM.lay D μ u (SKM.Shape.dot i) v).gen) e = q :=
    ⟨_, SPath.path_decOf _ _ q⟩
  refine compLayer_eq_zero gens _ d e (fun ho => hpq ?_) Z
  obtain ⟨⟨x, y⟩, pu, pg, pv⟩ := d
  obtain ⟨⟨x', y'⟩, qu, qg, qv⟩ := e
  simp only [SPath.Dec.outer, Prod.mk.injEq, Sigma.mk.injEq] at ho
  obtain ⟨⟨rfl, hu⟩, ⟨rfl, hv⟩⟩ := ho
  obtain rfl := eq_of_heq hu
  obtain rfl := eq_of_heq hv
  simp only [SPath.Dec.path]
  rw [SPath.eq_of_single pg qg]

/-- The `n`-fold composite of an endomorphism. -/
def compPow {C : Type*} [Category C] {Y : C} (f : Y ⟶ Y) : ℕ → (Y ⟶ Y)
  | 0 => 𝟙 Y
  | n + 1 => f ≫ compPow f n

/-- The entry of the dot on the left strand of `Eᵢ Eⱼ 1_ν` at a summand path. -/
def leftDot (gens : P.Generators) (i j : I) (ν : X) {s t : Sector I}
    (p : SPath (wd D ν [up i, up j]) s t) (Z : P.H t) :
    (P.pathFunctor p).obj Z ⟶ (P.pathFunctor p).obj Z :=
  compLayer gens (SKM.lay D ν [] (SKM.Shape.dot i) [up j]) p p Z

/-- The entry of the dot on the right strand of `Eᵢ Eⱼ 1_ν` at a summand path. -/
def rightDot (gens : P.Generators) (i j : I) (ν : X) {s t : Sector I}
    (p : SPath (wd D ν [up i, up j]) s t) (Z : P.H t) :
    (P.pathFunctor p).obj Z ⟶ (P.pathFunctor p).obj Z :=
  compLayer gens (SKM.lay D ν [up i] (SKM.Shape.dot j) []) p p Z

open Classical in
/-- **The entry of `n` dots on one strand** is diagonal, with diagonal entry the `n`-th power
of the entry of one dot. -/
theorem compList_dotsL (gens : P.Generators) (μ : X) (u : List (Letter I)) (i : I)
    (v : List (Letter I)) (n : ℕ)
    (h : Chain (SKM.lay D μ u (SKM.Shape.dot i) v).dom
      (SKM.layList D μ (SKM.dotsL u i v n)) (SKM.lay D μ u (SKM.Shape.dot i) v).dom)
    {s t : Sector I} (p q : SPath (SKM.lay D μ u (SKM.Shape.dot i) v).dom.word s t)
    (Z : P.H t) :
    compList gens _ h p q Z =
      if hpq : p = q then
        compPow (compLayer gens (SKM.lay D μ u (SKM.Shape.dot i) v) p p Z) n ≫
          eqToHom (congrArg (fun r => (P.pathFunctor r).obj Z) hpq)
      else 0 := by
  induction n generalizing p with
  | zero =>
    erw [compList_nil]
    split_ifs with hpq
    · subst hpq; simp [compPow]
    · rfl
  | succ n ih =>
    obtain ⟨hv, h₁, hc⟩ := h
    erw [compList_cons gens _ _ hv hc]
    refine (Finset.sum_eq_single p (fun m _ hm => ?_) (by simp)).trans ?_
    · erw [compLayer_dot_eq_zero gens μ u i v p m (Ne.symm hm) Z, Limits.zero_comp]
    erw [ih hc p]
    split_ifs with hpq
    · subst hpq
      simp only [eqToHom_refl, Category.comp_id, compPow]
    · simp

/-! ### Linearity of the entries of linear combinations -/

theorem compEval_sub (gens : P.Generators) {a b : Obj (SKM.sig D)} (x y : LinDiagram k a b)
    {s t : Sector I} (p : SPath a.word s t) (q : SPath b.word s t) (Z : P.H t) :
    compEval gens (x - y) p q Z = compEval gens x p q Z - compEval gens y p q Z :=
  Finsupp.sum_sub_index fun _ _ _ => sub_smul _ _ _

theorem _root_.Finsupp.sum_smul_smul {α M : Type*} [AddCommGroup M] [Module k M] (c : k)
    (x : α →₀ k) (f : α → M) :
    (c • x).sum (fun d r => r • f d) = c • x.sum (fun d r => r • f d) := by
  rw [Finsupp.sum_smul_index' (by simp), Finsupp.smul_sum]
  simp [mul_smul]

theorem _root_.Finsupp.sum_finset_sum_smul {α ι M : Type*} [AddCommGroup M] [Module k M]
    (S : Finset ι) (x : ι → α →₀ k) (f : α → M) :
    (∑ n ∈ S, x n).sum (fun d r => r • f d) = ∑ n ∈ S, (x n).sum (fun d r => r • f d) :=
  (Finsupp.sum_finsetSum_index (by simp) fun _ _ _ => add_smul _ _ _).symm

theorem compEval_smul (gens : P.Generators) {a b : Obj (SKM.sig D)} (c : k)
    (x : LinDiagram k a b) {s t : Sector I} (p : SPath a.word s t) (q : SPath b.word s t)
    (Z : P.H t) : compEval gens (c • x) p q Z = c • compEval gens x p q Z :=
  Finsupp.sum_smul_smul c x fun d => compDiag gens d p q Z

theorem compEval_sum (gens : P.Generators) {a b : Obj (SKM.sig D)} {ι : Type*} (S : Finset ι)
    (x : ι → LinDiagram k a b) {s t : Sector I} (p : SPath a.word s t) (q : SPath b.word s t)
    (Z : P.H t) : compEval gens (∑ n ∈ S, x n) p q Z = ∑ n ∈ S, compEval gens (x n) p q Z :=
  Finsupp.sum_finset_sum_smul S x fun d => compDiag gens d p q Z

theorem compEval_of (gens : P.Generators) {a b : Obj (SKM.sig D)} (d : a ⟶ b) {s t : Sector I}
    (p : SPath a.word s t) (q : SPath b.word s t) (Z : P.H t) :
    compEval gens (LinDiagram.of (R := k) d) p q Z = compDiag gens d p q Z :=
  (Finsupp.sum_single_index (h := fun d (r : k) => r • compDiag gens d p q Z)
    (zero_smul _ _)).trans (one_smul _ _)

/-- The entry of a crossing layer without strands on either side is the crossing image. -/
theorem compLayer_cross (gens : P.Generators) (i j : I) (ν : X) {s t : Sector I}
    (p : SPath (wd D ν [up i, up j]) s t) (q : SPath (wd D ν [up j, up i]) s t) (Z : P.H t) :
    compLayer gens (SKM.lay D ν [] (SKM.Shape.cross i j) []) p q Z = gens.cross i j ν p q Z := by
  rw [compLayer_eq_of_path gens (SKM.lay D ν [] (SKM.Shape.cross i j) []) (.nil s) p q (.nil t)
    p q (SPath.append_nil_pair p)
    (SPath.append_nil_pair q) Z]
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  rfl

open Classical in
/-- **The entry of two crossings** `τ : Eᵢ Eⱼ → Eⱼ Eᵢ`, then `τ : Eⱼ Eᵢ → Eᵢ Eⱼ`: the matrix
product of the two crossing images. -/
def crossCross (gens : P.Generators) (i j : I) (ν : X) {s t : Sector I}
    (p q : SPath (wd D ν [up i, up j]) s t) (Z : P.H t) :
    (P.pathFunctor p).obj Z ⟶ (P.pathFunctor q).obj Z :=
  letI : Fintype (SPath (wd D ν (SKM.Shape.cross i j).cod) s t) := Fintype.ofFinite _
  ∑ m, gens.cross i j ν p m Z ≫ gens.cross j i ν m q Z

theorem compList_crossCross (gens : P.Generators) (i j : I) (ν : X)
    (h : Chain (SKM.ob D ν [up i, up j])
      (SKM.layList D ν (SKM.crossL [] i j [] ++ SKM.crossL [] j i []))
      (SKM.ob D ν [up i, up j]))
    {s t : Sector I} (p q : SPath (wd D ν [up i, up j]) s t) (Z : P.H t) :
    compList gens _ h p q Z = crossCross gens i j ν p q Z := by
  classical
  obtain ⟨hv, h₁, hc⟩ := h
  erw [compList.eq_2]
  simp only [SKM.crossL, List.append, List.map_cons,
    List.map_nil, compList_one, SPath.cast_self, eqToHom_refl, Category.id_comp,
    Category.comp_id]
  unfold crossCross
  refine Finset.sum_congr (by congr) fun m _ => ?_
  rw [compLayer_cross, compLayer_cross]

open Classical in
/-- The entry of a composite diagram is the matrix product of the entries. -/
theorem compDiag_comp (gens : P.Generators) {a b c : Obj (SKM.sig D)} (d : a ⟶ b) (e : b ⟶ c)
    {s t : Sector I} (p : SPath a.word s t) (q : SPath c.word s t) (Z : P.H t) :
    letI := Fintype.ofFinite (SPath b.word s t)
    compDiag gens (d ≫ e) p q Z = ∑ m, compDiag gens d p m Z ≫ compDiag gens e m q Z :=
  compList_append gens _ _ d.2 e.2 _ p q Z

/-- The entry of the composite of two crossings of `Eᵢ Eⱼ 1_ν`. -/
theorem compDiag_crossCross (gens : P.Generators) (i j : I) (ν : X)
    (h : SKM.SChain [up i, up j] (SKM.crossL [] i j [] ++ SKM.crossL [] j i []) [up i, up j])
    {s t : Sector I} (p q : SPath (wd D ν [up i, up j]) s t) (Z : P.H t) :
    compDiag gens (SKM.mkD D ν _ h) p q Z = crossCross gens i j ν p q Z :=
  compList_crossCross gens i j ν _ p q Z

open Classical in
/-- The entry of `n` dots on the left strand of `Eᵢ Eⱼ 1_ν`. -/
theorem compDiag_leftDots (gens : P.Generators) (i j : I) (ν : X) (n : ℕ) {s t : Sector I}
    (p q : SPath (wd D ν [up i, up j]) s t) (Z : P.H t) :
    compDiag gens (SKM.mkD D ν (SKM.dotsL [] i [up j] n) (SKM.sChain_dotsL [] i [up j] n)) p q Z =
      if hpq : p = q then compPow (leftDot gens i j ν p Z) n ≫
        eqToHom (congrArg (fun r => (P.pathFunctor r).obj Z) hpq) else 0 :=
  compList_dotsL gens ν [] i [up j] n _ p q Z

open Classical in
/-- The entry of `n` dots on the right strand of `Eᵢ Eⱼ 1_ν`. -/
theorem compDiag_rightDots (gens : P.Generators) (i j : I) (ν : X) (n : ℕ) {s t : Sector I}
    (p q : SPath (wd D ν [up i, up j]) s t) (Z : P.H t) :
    compDiag gens (SKM.mkD D ν (SKM.dotsL [up i] j [] n) (SKM.sChain_dotsL [up i] j [] n)) p q Z =
      if hpq : p = q then compPow (rightDot gens i j ν p Z) n ≫
        eqToHom (congrArg (fun r => (P.pathFunctor r).obj Z) hpq) else 0 :=
  compList_dotsL gens ν [up i] j [] n _ p q Z

open Classical in
/-- The entry of `b` dots on the right strand followed by `a` dots on the left strand. -/
theorem compDiag_rightDots_leftDots (gens : P.Generators) (i j : I) (ν : X) (a b : ℕ)
    {s t : Sector I} (p q : SPath (wd D ν [up i, up j]) s t) (Z : P.H t) :
    compDiag gens (SKM.mkD D ν (SKM.dotsL [up i] j [] b) (SKM.sChain_dotsL [up i] j [] b) ≫
        SKM.mkD D ν (SKM.dotsL [] i [up j] a) (SKM.sChain_dotsL [] i [up j] a)) p q Z =
      if hpq : p = q then (compPow (rightDot gens i j ν p Z) b ≫
        compPow (leftDot gens i j ν p Z) a) ≫
        eqToHom (congrArg (fun r => (P.pathFunctor r).obj Z) hpq) else 0 := by
  refine (compDiag_comp gens
    (SKM.mkD D ν (SKM.dotsL [up i] j [] b) (SKM.sChain_dotsL [up i] j [] b))
    (SKM.mkD D ν (SKM.dotsL [] i [up j] a) (SKM.sChain_dotsL [] i [up j] a)) p q Z).trans ?_
  refine (Finset.sum_eq_single p (fun m _ hm => ?_) (by simp)).trans ?_
  · erw [compDiag_rightDots gens i j ν b p m Z]
    simp [Ne.symm hm]
  erw [compDiag_rightDots gens i j ν b p p Z, compDiag_leftDots gens i j ν a p q Z]
  by_cases hpq : p = q
  · subst hpq
    simp
  · simp [hpq]

open Classical in
/-- **The quadratic relations (1.7) for the crossing and dot images**, entry by entry. The
entry `crossCross` of two crossings vanishes for `i = j` and off the diagonal; on the diagonal
it is `t_ij` for `d_ij = 0`, and `Q_ij` evaluated at the dot entries of the two strands
otherwise. -/
structure CrossQuad (gens : P.Generators) : Prop where
  /-- `τ² = 0` on `Eᵢ Eᵢ`. -/
  quadEq : ∀ (i : I) (ν : X) {s t : Sector I} (p q : SPath (wd D ν [up i, up i]) s t)
    (Z : P.H t), crossCross gens i i ν p q Z = 0
  /-- The entries of `τ²` on `Eᵢ Eⱼ` vanish off the diagonal for `i ≠ j`. -/
  offDiag : ∀ (i j : I) (ν : X), i ≠ j → ∀ {s t : Sector I}
    (p q : SPath (wd D ν [up i, up j]) s t) (Z : P.H t), p ≠ q →
      crossCross gens i j ν p q Z = 0
  /-- `τ² = t_ij` on `Eᵢ Eⱼ` for `i ≠ j` and `d_ij = 0`. -/
  quadZero : ∀ (i j : I) (ν : X), i ≠ j → D.d i j = 0 → ∀ {s t : Sector I}
    (p : SPath (wd D ν [up i, up j]) s t) (Z : P.H t),
    crossCross gens i j ν p p Z = (Sc.t i j : k) • 𝟙 _
  /-- `τ² = Q_ij(x₁, x₂)` on `Eᵢ Eⱼ` for `i ≠ j` and `d_ij ≠ 0`. -/
  quadNe : ∀ (i j : I) (ν : X), i ≠ j → D.d i j ≠ 0 → ∀ {s t : Sector I}
    (p : SPath (wd D ν [up i, up j]) s t) (Z : P.H t),
    crossCross gens i j ν p p Z =
      (Sc.t i j : k) • compPow (leftDot gens i j ν p Z) (D.dn i j) +
        (Sc.t j i : k) • compPow (rightDot gens i j ν p Z) (D.dn j i) +
        ∑ a ∈ Finset.Ioo 0 (D.dn i j), ∑ b ∈ Finset.Ioo 0 (D.dn j i),
          Sc.s i j a b • (compPow (rightDot gens i j ν p Z) b ≫
            compPow (leftDot gens i j ν p Z) a)

variable {Gs Ys : ∀ s, P.H s}

/-- **`QuadRelations` for the swapped layer representation**: the quadratic relations (1.7)
hold, whiskered arbitrarily, as soon as the crossing and dot images satisfy `CrossQuad`. -/
theorem quadRelations {gens : P.Generators} (hq : CrossQuad gens) :
    QuadRelations Sc (P.layerRep Gs Ys gens) := by
  classical
  intro r hr
  cases r with
  | quadNe i j ν hij hd =>
    refine relHolds_of_compEval gens _ fun p q Z => ?_
    show compEval gens (a := SKM.ob D ν [up i, up j]) (b := SKM.ob D ν [up i, up j])
      (SKM.relation D Sc (.quadNe i j ν hij hd)) p q Z = 0
    simp only [SKM.relation]
    rw [compEval_sub, compEval_sub, compEval_sub, compEval_smul, compEval_smul, compEval_sum]
    simp only [compEval_of]
    have hm : ∀ a b : ℕ, compEval gens (Sc.s i j a b • SKM.dg D ν
        (SKM.dotsL [up i] j [] b ++ SKM.dotsL [] i [up j] a)
        ((SKM.sChain_dotsL [up i] j [] b).append (SKM.sChain_dotsL [] i [up j] a))) p q Z =
        Sc.s i j a b • compDiag gens (SKM.mkD D ν (SKM.dotsL [up i] j [] b)
          (SKM.sChain_dotsL [up i] j [] b) ≫ SKM.mkD D ν (SKM.dotsL [] i [up j] a)
          (SKM.sChain_dotsL [] i [up j] a)) p q Z := by
      intro a b
      rw [compEval_smul, compEval_of, SKM.mkD_comp]
    rw [Finset.sum_congr rfl fun n _ => (compEval_sum gens _ _ p q Z).trans
      (Finset.sum_congr rfl fun m _ => (hm n m).trans
        (congrArg _ (compDiag_rightDots_leftDots gens i j ν n m p q Z)))]
    erw [compDiag_crossCross gens i j ν _ p q Z, compDiag_leftDots gens i j ν _ p q Z,
      compDiag_rightDots gens i j ν _ p q Z]
    by_cases hpq : p = q
    · subst hpq
      simp only [dite_true, eqToHom_refl, Category.comp_id]
      rw [hq.quadNe i j ν hij hd p Z]
      abel
    · rw [hq.offDiag i j ν hij p q Z hpq]
      simp [hpq]
  | quadEq i ν =>
    refine relHolds_of_compEval gens _ fun p q Z => ?_
    show compEval gens (a := SKM.ob D ν [up i, up i]) (b := SKM.ob D ν [up i, up i])
      (SKM.relation D Sc (.quadEq i ν)) p q Z = 0
    simp only [SKM.relation]
    rw [compEval_of]
    erw [compDiag_crossCross gens i i ν _ p q Z]
    exact hq.quadEq i ν p q Z
  | quadZero i j ν hij hd =>
    refine relHolds_of_compEval gens _ fun p q Z => ?_
    show compEval gens (a := SKM.ob D ν [up i, up j]) (b := SKM.ob D ν [up i, up j])
      (SKM.relation D Sc (.quadZero i j ν hij hd)) p q Z = 0
    simp only [SKM.relation]
    rw [compEval_sub, compEval_smul, compEval_of, compEval_of]
    erw [compDiag_crossCross gens i j ν _ p q Z, compDiag_id gens p q Z]
    by_cases hpq : p = q
    · subst hpq
      rw [hq.quadZero i j ν hij hd p Z]
      simp
    · rw [hq.offDiag i j ν hij p q Z hpq]
      simp [hpq]
  | _ => simp [relGroup] at hr

end ProbeReservoir

end OddMath.QuiverHecke.SwappedAssembly
