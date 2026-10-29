/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.SKM.RouquierData
import OddMath.SKM.Grading
import StringDiagrams.Super.Graded

/-!
# Integer gradings of Rouquier families

An integer grading of the 2-morphisms between the objects of a `RouquierFamily`, with the
generator degrees of Brundan–Ellis, arXiv:1701.04133v2, §1 "Gradings" (the table after
(1.31), as in `SKM.gdeg`): dot `2dᵢ`, crossing `dᵢdᵢⱼ`, unit `dᵢ(1+⟨hᵢ,x⟩)` at its source
weight `x`, counit `dᵢ(1-⟨hᵢ,y⟩)` at its target weight `y`.

The grading lives only on the Hom categories `W.obj μ ⟶ W.obj ν`; no grading is imposed on
the ambient 2-supercategory, so a family sharing its ambient with ungraded data (the probe of
a `ProbeReservoir`) can carry one.

## Main results

* `SuperSumInvTo.f'_mem_degree`, `SuperSumInvTo.g'_mem_degree` and their
  `SuperSumInvFrom` versions: in a graded supercategory, the inverse matrix of a matrix with
  homogeneous entries has homogeneous entries of the negated degrees. This is the
  homogeneous-inverse step (G8) of `docs/Nondegeneracy/DeformedGradedAction.md`.
* `RouquierGrading.mate_mem`: the mate of the Rouquier crossing has degree `0`.
* `RouquierGrading.invPos_f'_mem`, `invPos_g'_mem`, `invNeg_f'_mem`,
  `invNeg_g'_mem`: the inverse entries of `SuperRouquierLoc` are homogeneous of the
  degrees of the leftward crossing and the dotted cups and caps.
* `RouquierGrading.closure_mem`: the contracted closure `b_(s,r)` has degree
  `2dᵢ(r+s+1)`; `boundaryPos_mem`, `boundaryNeg_mem`: the boundary
  contractions have degrees `2dᵢ(n-m)`, `2dᵢ(m-n)`.
* `RouquierGrading.BoundedAbove.exists_foldr_eq_zero`: when every `End(𝟙_μ)` is bounded above in
  degree, a composite of more than the bound of positive-degree endomorphisms vanishes.

These are the inputs (N) and (J) of `docs/Nondegeneracy/SwappedHomInversion.md` §4 at the
reservoir; see `docs/Nondegeneracy/ReservoirGradingRoute.md`.
-/

noncomputable section
namespace OddMath.SKM
open CategoryTheory StringDiagrams BicategoryStruct Supercategory GradedSupercategory

universe u v w r
variable {k : Type r} [CommRing k]

section Generic

variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear k C] [Supercategory k C]
  [GradedSupercategory k C]

theorem mem_degree_congr {X Y : C} {f : X ⟶ Y} {m n : ℤ}
    (hf : f ∈ degree (R := k) X Y m) (e : m = n) : f ∈ degree (R := k) X Y n := e ▸ hf

/-- Post-composition with a homogeneous morphism shifts the degree projections. -/
theorem dproj_comp_of_mem {A B Z : C} {a : ℤ} {f : B ⟶ Z} (hf : f ∈ degree (R := k) B Z a)
    (e : ℤ) (x : A ⟶ B) : dproj k e x ≫ f = dproj k (e + a) (x ≫ f) := by
  refine induction_on_degree (R := k) x (by simp) (fun j g hg => ?_) (fun g h hg hh => ?_)
  · by_cases hj : j = e
    · subst hj; rw [dproj_of_mem hg, dproj_of_mem (comp_mem_degree hg hf)]
    · rw [dproj_of_mem_ne hg hj, Limits.zero_comp,
        dproj_of_mem_ne (comp_mem_degree hg hf) (fun h => hj (add_right_cancel h))]
  · rw [map_add, Preadditive.add_comp, hg, hh, Preadditive.add_comp, map_add]

/-- Pre-composition with a homogeneous morphism shifts the degree projections. -/
theorem comp_dproj_of_mem {Z A B : C} {a : ℤ} {f : Z ⟶ A} (hf : f ∈ degree (R := k) Z A a)
    (e : ℤ) (x : A ⟶ B) : f ≫ dproj k e x = dproj k (a + e) (f ≫ x) := by
  refine induction_on_degree (R := k) x (by simp) (fun j g hg => ?_) (fun g h hg hh => ?_)
  · by_cases hj : j = e
    · subst hj; rw [dproj_of_mem hg, dproj_of_mem (comp_mem_degree hf hg)]
    · rw [dproj_of_mem_ne hg hj, Limits.comp_zero,
        dproj_of_mem_ne (comp_mem_degree hf hg) (fun h => hj (add_left_cancel h))]
  · rw [map_add, Preadditive.comp_add, hg, hh, Preadditive.comp_add, map_add]

namespace SuperSumInvTo

variable {A B Z : C} {f : A ⟶ B} {g : ℕ → (A ⟶ Z)} {p : ZMod 2} {q : ℕ → ZMod 2} {n : ℕ}
  (S : SuperSumInvTo (k := k) f g p q n)
include S

omit [GradedSupercategory k C] in
/-- A morphism `y : W ⟶ A` killed by `f` and by all `g m` vanishes. -/
theorem eq_zero_of_comp {W : C} (y : W ⟶ A) (h₁ : y ≫ f = 0)
    (h₂ : ∀ m, m < n → y ≫ g m = 0) : y = 0 := by
  have := congrArg (y ≫ ·) S.total
  simp only [Preadditive.comp_add, Preadditive.comp_sum, Category.comp_id] at this
  rw [← this, ← Category.assoc, h₁, Limits.zero_comp, zero_add]
  refine Finset.sum_eq_zero fun m hm => ?_
  rw [← Category.assoc, h₂ m (Finset.mem_range.1 hm), Limits.zero_comp]

variable {a : ℤ} {b : ℕ → ℤ} (hf : f ∈ degree (R := k) A B a)
  (hg : ∀ m, m < n → g m ∈ degree (R := k) A Z (b m))
include hf hg

/-- (G8) for a row inverse: `f'` is homogeneous of degree `-a`. -/
theorem f'_mem_degree : S.f' ∈ degree (R := k) B A (-a) := by
  refine mem_degree_of_dproj fun e he => ?_
  refine S.eq_zero_of_comp _ ?_ fun m hm => ?_
  · rw [dproj_comp_of_mem hf, S.ff, dproj_of_mem_ne (id_mem_degree B)]; omega
  · rw [dproj_comp_of_mem (hg m hm), S.fg m hm, map_zero]

/-- (G8) for a row inverse: `g' m` is homogeneous of degree `-b m`. -/
theorem g'_mem_degree (m : ℕ) (hm : m < n) : S.g' m ∈ degree (R := k) Z A (-b m) := by
  refine mem_degree_of_dproj fun e he => ?_
  refine S.eq_zero_of_comp _ ?_ fun l hl => ?_
  · rw [dproj_comp_of_mem hf, S.gf m hm, map_zero]
  · rw [dproj_comp_of_mem (hg l hl), S.gg m l hm hl]
    split_ifs with hml
    · subst hml; rw [dproj_of_mem_ne (id_mem_degree Z)]; omega
    · exact map_zero _

end SuperSumInvTo

namespace SuperSumInvFrom

variable {A B Z : C} {f : B ⟶ A} {g : ℕ → (Z ⟶ A)} {p : ZMod 2} {q : ℕ → ZMod 2} {n : ℕ}
  (S : SuperSumInvFrom (k := k) f g p q n)
include S

omit [GradedSupercategory k C] in
/-- A morphism `y : A ⟶ W` killed by `f` and by all `g m` vanishes. -/
theorem eq_zero_of_comp {W : C} (y : A ⟶ W) (h₁ : f ≫ y = 0)
    (h₂ : ∀ m, m < n → g m ≫ y = 0) : y = 0 := by
  have := congrArg (· ≫ y) S.total
  simp only [Preadditive.add_comp, Preadditive.sum_comp, Category.id_comp] at this
  rw [← this, Category.assoc, h₁, Limits.comp_zero, zero_add]
  refine Finset.sum_eq_zero fun m hm => ?_
  rw [Category.assoc, h₂ m (Finset.mem_range.1 hm), Limits.comp_zero]

variable {a : ℤ} {b : ℕ → ℤ} (hf : f ∈ degree (R := k) B A a)
  (hg : ∀ m, m < n → g m ∈ degree (R := k) Z A (b m))
include hf hg

/-- (G8) for a column inverse: `f'` is homogeneous of degree `-a`. -/
theorem f'_mem_degree : S.f' ∈ degree (R := k) A B (-a) := by
  refine mem_degree_of_dproj fun e he => ?_
  refine S.eq_zero_of_comp _ ?_ fun m hm => ?_
  · rw [comp_dproj_of_mem hf, S.ff, dproj_of_mem_ne (id_mem_degree B)]; omega
  · rw [comp_dproj_of_mem (hg m hm), S.gf m hm, map_zero]

/-- (G8) for a column inverse: `g' m` is homogeneous of degree `-b m`. -/
theorem g'_mem_degree (m : ℕ) (hm : m < n) : S.g' m ∈ degree (R := k) A Z (-b m) := by
  refine mem_degree_of_dproj fun e he => ?_
  refine S.eq_zero_of_comp _ ?_ fun l hl => ?_
  · rw [comp_dproj_of_mem hf, S.fg m hm, map_zero]
  · rw [comp_dproj_of_mem (hg l hl), S.gg l m hl hm]
    split_ifs with hml
    · subst hml; rw [dproj_of_mem_ne (id_mem_degree Z)]; omega
    · exact map_zero _

end SuperSumInvFrom

end Generic

section Family

variable {B : Type u} [BicategoryStruct.{w,v} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear k (a ⟶ b)]
  [∀ a b : B, Supercategory k (a ⟶ b)]
variable {I X : Type*} [AddCommGroup X] {D : Datum I X}

/-- An integer grading of the 2-morphisms between the objects of a Rouquier family, with
the generator degrees of Brundan–Ellis, arXiv:1701.04133v2, §1 (`SKM.gdeg`): each Hom
category `W.obj μ ⟶ W.obj ν` is a graded supercategory, whiskering preserves degrees,
associators and unitors have degree `0`, the dot has degree `2dᵢ`, the crossing `dᵢdᵢⱼ`,
the unit `dᵢ(1+⟨hᵢ,x⟩)` at its source `x` and the counit `dᵢ(1-⟨hᵢ,y⟩)` at its target
`y`. -/
structure RouquierGrading (W : RouquierFamily (k := k) (B := B) D) (sy : Symmetrizer D) where
  /-- The grading of each Hom category between objects of the family. -/
  graded : ∀ μ ν : X, GradedSupercategory k (W.obj μ ⟶ W.obj ν)
  whiskerLeft_mem : ∀ {μ ν ρ : X} (f : W.obj μ ⟶ W.obj ν) {g h : W.obj ν ⟶ W.obj ρ}
    {n : ℤ} {η : g ⟶ h}, η ∈ degree (self := graded ν ρ) (R := k) g h n →
      f ◁ η ∈ degree (self := graded μ ρ) (R := k) (f ≫ g) (f ≫ h) n
  whiskerRight_mem : ∀ {μ ν ρ : X} {f g : W.obj μ ⟶ W.obj ν} (h : W.obj ν ⟶ W.obj ρ)
    {n : ℤ} {η : f ⟶ g}, η ∈ degree (self := graded μ ν) (R := k) f g n →
      η ▷ h ∈ degree (self := graded μ ρ) (R := k) (f ≫ h) (g ≫ h) n
  associator_mem : ∀ {μ ν ρ σ : X} (f : W.obj μ ⟶ W.obj ν) (g : W.obj ν ⟶ W.obj ρ)
    (h : W.obj ρ ⟶ W.obj σ),
      (associator f g h).hom ∈ degree (self := graded μ σ) (R := k) _ _ 0
  leftUnitor_mem : ∀ {μ ν : X} (f : W.obj μ ⟶ W.obj ν),
    (leftUnitor f).hom ∈ degree (self := graded μ ν) (R := k) _ _ 0
  rightUnitor_mem : ∀ {μ ν : X} (f : W.obj μ ⟶ W.obj ν),
    (rightUnitor f).hom ∈ degree (self := graded μ ν) (R := k) _ _ 0
  dot_mem : ∀ (i : I) {x y : X} (h : x + D.α i = y),
    W.dot i h ∈ degree (self := graded x y) (R := k) _ _ (2 * sy.d i)
  cross_mem : ∀ (i j : I) {a b c d : X} (h₁ : a + D.α j = b) (h₂ : b + D.α i = d)
    (h₃ : a + D.α i = c) (h₄ : c + D.α j = d),
      W.cross i j h₁ h₂ h₃ h₄ ∈ degree (self := graded a d) (R := k) _ _ (sy.d i * D.d i j)
  unit_mem : ∀ (i : I) {x y : X} (h : x + D.α i = y),
    (W.adj i h).unit ∈ degree (self := graded x x) (R := k) _ _ (sy.d i * (1 + D.h i x))
  counit_mem : ∀ (i : I) {x y : X} (h : x + D.α i = y),
    (W.adj i h).counit ∈ degree (self := graded y y) (R := k) _ _ (sy.d i * (1 - D.h i y))

namespace RouquierGrading

variable {W : RouquierFamily (k := k) (B := B) D} {sy : Symmetrizer D}
  (G : RouquierGrading W sy)

/-- Degree-`n` 2-morphisms between `f, g : W.obj μ ⟶ W.obj ν`. -/
abbrev deg {μ ν : X} (f g : W.obj μ ⟶ W.obj ν) (n : ℤ) : Submodule k (f ⟶ g) :=
  degree (self := G.graded μ ν) (R := k) f g n

theorem comp_mem {μ ν : X} {f g h : W.obj μ ⟶ W.obj ν} {m n : ℤ} {α : f ⟶ g} {β : g ⟶ h}
    (hα : α ∈ G.deg f g m) (hβ : β ∈ G.deg g h n) : α ≫ β ∈ G.deg f h (m + n) :=
  let _ := G.graded μ ν; comp_mem_degree hα hβ

theorem comp_mem' {μ ν : X} {f g h : W.obj μ ⟶ W.obj ν} {m n l : ℤ} {α : f ⟶ g}
    {β : g ⟶ h} (hα : α ∈ G.deg f g m) (hβ : β ∈ G.deg g h n) (e : m + n = l) :
    α ≫ β ∈ G.deg f h l := e ▸ G.comp_mem hα hβ

theorem associator_inv_mem {μ ν ρ σ : X} (f : W.obj μ ⟶ W.obj ν) (g : W.obj ν ⟶ W.obj ρ)
    (h : W.obj ρ ⟶ W.obj σ) : (associator f g h).inv ∈ G.deg _ _ 0 := by
  let _ := G.graded μ σ
  simpa using inv_mem_degree (R := k) (associator f g h) (G.associator_mem f g h)

theorem leftUnitor_inv_mem {μ ν : X} (f : W.obj μ ⟶ W.obj ν) :
    (leftUnitor f).inv ∈ G.deg _ _ 0 := by
  let _ := G.graded μ ν
  simpa using inv_mem_degree (R := k) (leftUnitor f) (G.leftUnitor_mem f)

theorem rightUnitor_inv_mem {μ ν : X} (f : W.obj μ ⟶ W.obj ν) :
    (rightUnitor f).inv ∈ G.deg _ _ 0 := by
  let _ := G.graded μ ν
  simpa using inv_mem_degree (R := k) (rightUnitor f) (G.rightUnitor_mem f)

theorem power_mem (i : I) {x y : X} (h : x + D.α i = y) (n : ℕ) :
    rouquierPower (W.dot i h) n ∈ G.deg _ _ (2 * sy.d i * n) := by
  induction n with
  | zero => simpa [rouquierPower] using (let _ := G.graded x y; id_mem_degree (R := k) (W.E i h))
  | succ n ih =>
    exact G.comp_mem' ih (G.dot_mem i h) (by push_cast; ring)

/-- The dotted cap `F ◁ xⁿ ≫ ε` has degree `dᵢ(1-⟨hᵢ,y⟩+2n)` (the `e_n` of (G6)). -/
theorem dotCap_mem (i : I) {x y : X} (h : x + D.α i = y) (n : ℕ) :
    W.F i h ◁ rouquierPower (W.dot i h) n ≫ (W.adj i h).counit ∈
      G.deg _ _ (sy.d i * (1 - D.h i y + 2 * n)) :=
  G.comp_mem' (G.whiskerLeft_mem _ (G.power_mem i h n)) (G.counit_mem i h) (by ring)

/-- The dotted cup `η ≫ xⁿ ▷ F` has degree `dᵢ(1+⟨hᵢ,x⟩+2n)` (the `c_n` of (G6)). -/
theorem dotCup_mem (i : I) {x y : X} (h : x + D.α i = y) (n : ℕ) :
    (W.adj i h).unit ≫ rouquierPower (W.dot i h) n ▷ W.F i h ∈
      G.deg _ _ (sy.d i * (1 + D.h i x + 2 * n)) :=
  G.comp_mem' (G.unit_mem i h) (G.whiskerRight_mem _ (G.power_mem i h n)) (by ring)

/-- The mate of the same-colour crossing has degree `0`. -/
theorem mate_mem (i : I) {a b c : X} (h₁ : a + D.α i = b) (h₂ : b + D.α i = c) :
    rouquierMate (W.adj i h₁) (W.adj i h₂) (W.cross i i h₁ h₂ h₁ h₂) ∈ G.deg _ _ 0 := by
  unfold rouquierMate
  have hc := G.cross_mem i i h₁ h₂ h₁ h₂
  rw [D.d_self] at hc
  refine G.comp_mem' (n := 0) (G.rightUnitor_inv_mem _) ?_ (add_zero 0)
  refine G.comp_mem' (n := sy.d i * (-2 + (1 - D.h i b)))
    (G.whiskerLeft_mem _ (G.unit_mem i h₂)) ?_ (by ring)
  refine G.comp_mem' (n := sy.d i * (-2 + (1 - D.h i b))) (G.associator_mem _ _ _) ?_
    (zero_add _)
  refine G.comp_mem' (n := sy.d i * (-2 + (1 - D.h i b)))
    (G.whiskerLeft_mem _ (G.associator_inv_mem _ _ _)) ?_ (zero_add _)
  refine G.comp_mem' (n := sy.d i * (1 - D.h i b))
    (G.whiskerLeft_mem _ (G.whiskerRight_mem _ hc)) ?_ (by ring)
  refine G.comp_mem' (n := sy.d i * (1 - D.h i b)) (G.associator_inv_mem _ _ _) ?_
    (zero_add _)
  refine G.comp_mem' (n := sy.d i * (1 - D.h i b))
    (G.whiskerRight_mem _ (G.associator_inv_mem _ _ _)) ?_ (zero_add _)
  exact G.comp_mem' (G.whiskerRight_mem _ (G.whiskerRight_mem _ (G.counit_mem i h₁)))
    (G.whiskerRight_mem _ (G.leftUnitor_mem _)) (add_zero _)

variable (i : I) {a b c : X} (h₁ : a + D.α i = b) (h₂ : b + D.α i = c)

/-- (G8) at positive height: the inverse of the mate has degree `0`. -/
theorem invPos_f'_mem (hh : 0 ≤ D.h i b) :
    ((W.loc i h₁ h₂).invPos hh).f' ∈ G.deg _ _ 0 := by
  let _ := G.graded b b
  simpa using ((W.loc i h₁ h₂).invPos hh).f'_mem_degree (G.mate_mem i h₁ h₂)
    (fun m _ => G.dotCap_mem i h₁ m)

/-- (G8) at positive height: the `m`-th extra row has degree `dᵢ(⟨hᵢ,b⟩-1-2m)`, the degree
of the dotted leftward cup `dcup i m`. -/
theorem invPos_g'_mem (hh : 0 ≤ D.h i b) (m : ℕ) (hm : m < (D.h i b).toNat) :
    ((W.loc i h₁ h₂).invPos hh).g' m ∈ G.deg _ _ (sy.d i * (D.h i b - 1 - 2 * m)) := by
  let _ := G.graded b b
  exact mem_degree_congr (((W.loc i h₁ h₂).invPos hh).g'_mem_degree (G.mate_mem i h₁ h₂)
    (fun m _ => G.dotCap_mem i h₁ m) m hm) (by ring)

/-- (G8) at negative height: the inverse of the mate has degree `0`. -/
theorem invNeg_f'_mem (hh : D.h i b ≤ 0) :
    ((W.loc i h₁ h₂).invNeg hh).f' ∈ G.deg _ _ 0 := by
  let _ := G.graded b b
  simpa using ((W.loc i h₁ h₂).invNeg hh).f'_mem_degree (G.mate_mem i h₁ h₂)
    (fun m _ => G.dotCup_mem i h₂ m)

/-- (G8) at negative height: the `m`-th extra column has degree `-dᵢ(⟨hᵢ,b⟩+1+2m)`, the
degree of the dotted leftward cap `dcap i m`. -/
theorem invNeg_g'_mem (hh : D.h i b ≤ 0) (m : ℕ) (hm : m < (-D.h i b).toNat) :
    ((W.loc i h₁ h₂).invNeg hh).g' m ∈ G.deg _ _ (-(sy.d i * (D.h i b + 1 + 2 * m))) := by
  let _ := G.graded b b
  exact mem_degree_congr (((W.loc i h₁ h₂).invNeg hh).g'_mem_degree (G.mate_mem i h₁ h₂)
    (fun m _ => G.dotCup_mem i h₂ m) m hm) (by ring)

/-- The contracted closure `b_(s,r) = cupD(r) ; y ; capD(s)` of a degree-`0` 2-morphism
`y : E₂F₂ ⟶ F₁E₁` (for instance the inverse of the mate) has degree `2dᵢ(r+s+1)`. -/
theorem closure_mem {y : W.E i h₂ ≫ W.F i h₂ ⟶ W.F i h₁ ≫ W.E i h₁}
    (hy : y ∈ G.deg _ _ 0) (r s : ℕ) :
    ((W.adj i h₂).unit ≫ rouquierPower (W.dot i h₂) r ▷ W.F i h₂) ≫ y ≫
        (W.F i h₁ ◁ rouquierPower (W.dot i h₁) s ≫ (W.adj i h₁).counit) ∈
      G.deg _ _ (2 * sy.d i * (r + s + 1)) :=
  G.comp_mem' (G.dotCup_mem i h₂ r) (G.comp_mem' hy (G.dotCap_mem i h₁ s) rfl) (by ring)

/-- The positive-height boundary contraction `(m, n)` has degree `2dᵢ(n-m)`. -/
theorem boundaryPos_mem (hh : 0 ≤ D.h i b) (m n : ℕ) (hm : m < (D.h i b).toNat) :
    (W.loc i h₁ h₂).boundaryPos hh m n ∈ G.deg _ _ (2 * sy.d i * (n - m)) :=
  G.comp_mem' (G.invPos_g'_mem i h₁ h₂ hh m hm) (G.dotCap_mem i h₁ n) (by ring)

/-- The negative-height boundary contraction `(m, n)` has degree `2dᵢ(m-n)`. -/
theorem boundaryNeg_mem (hh : D.h i b ≤ 0) (m n : ℕ) (hn : n < (-D.h i b).toNat) :
    (W.loc i h₁ h₂).boundaryNeg hh m n ∈ G.deg _ _ (2 * sy.d i * (m - n)) :=
  G.comp_mem' (G.dotCup_mem i h₂ m) (G.invNeg_g'_mem i h₁ h₂ hh n hn) (by ring)

/-- Every `End(𝟙_μ)` is bounded above in degree: the finite homogeneous truncation of the
reservoir (`SwappedHomInversion.md` §1). -/
def BoundedAbove : Prop :=
  ∀ μ : X, ∃ M : ℤ, ∀ n : ℤ, M < n → ∀ f, f ∈ G.deg (𝟙 (W.obj μ)) (𝟙 (W.obj μ)) n → f = 0

theorem foldr_mem {μ : X} (l : List (𝟙 (W.obj μ) ⟶ 𝟙 (W.obj μ)))
    (hl : ∀ f ∈ l, ∃ n : ℤ, 0 < n ∧ f ∈ G.deg _ _ n) :
    ∃ N : ℤ, (l.length : ℤ) ≤ N ∧ l.foldr (· ≫ ·) (𝟙 _) ∈ G.deg _ _ N := by
  induction l with
  | nil => exact ⟨0, le_rfl, let _ := G.graded μ μ; id_mem_degree (R := k) _⟩
  | cons f l ih =>
    obtain ⟨n, hn, hf⟩ := hl f (List.mem_cons_self ..)
    obtain ⟨N, hN, hmem⟩ := ih fun g hg => hl g (List.mem_cons_of_mem _ hg)
    exact ⟨n + N, by simp; omega, G.comp_mem hf hmem⟩

/-- (N) at the reservoir: under `BoundedAbove`, a composite of more than the bound of
positive-degree elements of `End(𝟙_μ)` vanishes. -/
theorem BoundedAbove.exists_foldr_eq_zero (hG : G.BoundedAbove) (μ : X) :
    ∃ M : ℕ, ∀ l : List (𝟙 (W.obj μ) ⟶ 𝟙 (W.obj μ)), M < l.length →
      (∀ f ∈ l, ∃ n : ℤ, 0 < n ∧ f ∈ G.deg _ _ n) → l.foldr (· ≫ ·) (𝟙 _) = 0 := by
  obtain ⟨M, hM⟩ := hG μ
  refine ⟨M.toNat, fun l hl hpos => ?_⟩
  obtain ⟨N, hN, hmem⟩ := G.foldr_mem l hpos
  exact hM N (by omega) _ hmem

end RouquierGrading

end Family

end OddMath.SKM
