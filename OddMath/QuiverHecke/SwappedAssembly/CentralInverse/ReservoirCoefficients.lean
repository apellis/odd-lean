/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.SwappedAssembly.CentralInverse.CoefficientIdeal
import OddMath.QuiverHecke.SwappedAssembly.Sectors
import OddMath.SKM.RouquierGrading

/-! # The reservoir coefficient ideal on a Hom sector

`docs/Nondegeneracy/SwappedHomInversion.md` §4 works modulo the two-sided ideal `J` generated
by the positive-degree closed reservoir coefficients, acting on the Hom-sector objects
`Z : T(-μP) ⟶ W(μM)` by post-whiskering. Its two inputs are (N), joint nilpotence of `J`, and
(J), membership of the positive-degree contractions (the closures `b_(s,r)` of (8) and the
`r > j` window contractions of (7)) in `J`. At the reservoir both are proved in
`OddMath/SKM/RouquierGrading.lean`. This file transports them to the Hom sector and packages
the result as the `ProbeWindow.CoefficientIdeal` consumed by
`ProbeWindow.CoefficientIdeal.isIso_of_sub_mem`.

Let `b` be an object with a coefficient grading (`CoeffGrading`): a `ℤ`-filtration of
`End(𝟙 b)` with `𝟙` in degree `0`, additive degrees and parity-stable degrees. Only the
coefficients are graded, not the whole category `b ⟶ b`; `CoeffGrading.ofGraded` builds one
from a graded supercategory structure on `b ⟶ b`, as `SKM.RouquierGrading` provides. A coefficient
`c : 𝟙 b ⟶ 𝟙 b` acts on every `Z : a ⟶ b` by `postCoeff Z c = ρ⁻¹ ≫ Z ◁ c ≫ ρ`. The `n`-th
power of the ideal, `coeffIdeal n Z Y`, is the span of the `postCoeff Z c ≫ h` with `c`
homogeneous of degree at least `n`. No grading of `a ⟶ b` is used: every 2-morphism
`h : Z ⟶ Y`, in particular every probe word, super-commutes with `postCoeff` by the super
interchange law (`comp_postCoeff`), with its Koszul sign. This is the step "move only reservoir
coefficients past probe words by supernaturality" of §4 there; it needs no grading of the
probe.

## Main definitions and results

* `ProbeWindow.CoeffGrading`, `CoeffGrading.ofGraded`: the grading of the coefficients used.
* `ProbeWindow.postCoeff`: the post-whiskering action of `End(𝟙 b)` on `Z : a ⟶ b`;
  multiplicative (`postCoeff_comp`), unital (`postCoeff_id`), additive.
* `ProbeWindow.comp_postCoeff`: `h ≫ postCoeff Y c = (-1)^{|h||c|} (postCoeff Z c ≫ h)` for
  parity-homogeneous `h`, `c`.
* `ProbeWindow.coeffIdeal`: the filtration; `coeffIdeal_comp_mem` (`Jₘ ≫ Jₙ ⊆ Jₘ₊ₙ`),
  `eq_zero_of_mem_coeffIdeal` (vanishing above an upper degree bound of `End(𝟙 b)`).
* `ProbeWindow.reservoirCoefficientIdeal`: the `ProbeWindow.CoefficientIdeal` it defines, for
  any predicate on the objects of `a ⟶ b`.
* `ProbeReservoir.homCoefficientIdeal`: for a `ProbeReservoir` whose reservoir carries a
  `SKM.RouquierGrading` with `BoundedAbove`, the coefficient ideal on the Hom sector `P.H t` of
  every sector `t`. This discharges the coefficient-ideal hypothesis of the central inversion.
* (J) and (N) on the Hom sector: `ProbeReservoir.closure_mem_homCoefficientIdeal` (the
  contracted closures (8)), `boundaryPos_mem_homCoefficientIdeal`,
  `boundaryNeg_mem_homCoefficientIdeal` (the `r > j` contractions of (7)) lie in `J₁`, also with
  arbitrary Hom-sector morphisms on either side (`comp_postCoeff_comp_mem`).
-/

noncomputable section

namespace OddMath.QuiverHecke.SwappedAssembly

open CategoryTheory StringDiagrams BicategoryStruct Supercategory GradedSupercategory

universe u v w r

namespace ProbeWindow

variable {k : Type r} [CommRing k] {B : Type u} [BicategoryStruct.{w, v} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear k (a ⟶ b)]
  [∀ a b : B, Supercategory k (a ⟶ b)] [TwoSupercategory k B]

section Action

variable {a b : B}

/-- The action of a coefficient `c : 𝟙 b ⟶ 𝟙 b` on `Z : a ⟶ b` by post-whiskering. -/
def postCoeff (Z : a ⟶ b) (c : 𝟙 b ⟶ 𝟙 b) : Z ⟶ Z :=
  (rightUnitor Z).inv ≫ Z ◁ c ≫ (rightUnitor Z).hom

include k in
theorem postCoeff_id (Z : a ⟶ b) : postCoeff Z (𝟙 (𝟙 b)) = 𝟙 Z := by
  simp [postCoeff, TwoSupercategory.whiskerLeft_id (R := k)]

include k in
theorem postCoeff_comp (Z : a ⟶ b) (c c' : 𝟙 b ⟶ 𝟙 b) :
    postCoeff Z (c ≫ c') = postCoeff Z c ≫ postCoeff Z c' := by
  simp [postCoeff, TwoSupercategory.whiskerLeft_comp (R := k)]

include k in
theorem postCoeff_add (Z : a ⟶ b) (c c' : 𝟙 b ⟶ 𝟙 b) :
    postCoeff Z (c + c') = postCoeff Z c + postCoeff Z c' := by
  simp [postCoeff, TwoSupercategory.whiskerLeft_add (R := k), Preadditive.add_comp,
    Preadditive.comp_add]

include k in
theorem postCoeff_zero (Z : a ⟶ b) : postCoeff Z (0 : 𝟙 b ⟶ 𝟙 b) = 0 := by
  have h := postCoeff_add (k := k) Z 0 0
  rw [add_zero] at h
  simpa using h.symm

/-- **Reservoir coefficients super-commute with every Hom-sector morphism**, by the super
interchange law: `h ≫ postCoeff Y c = (-1)^{pq} (postCoeff Z c ≫ h)` for `h` of parity `p` and
`c` of parity `q`. -/
theorem comp_postCoeff {Z Y : a ⟶ b} {p q : ZMod 2} {h : Z ⟶ Y} {c : 𝟙 b ⟶ 𝟙 b}
    (hh : h ∈ parity (R := k) Z Y p) (hc : c ∈ parity (R := k) (𝟙 b) (𝟙 b) q) :
    h ≫ postCoeff Y c = koszulSign p q • (postCoeff Z c ≫ h) := by
  have hρ : h ≫ (rightUnitor Y).inv = (rightUnitor Z).inv ≫ h ▷ 𝟙 b := by
    rw [TwoSupercategory.whiskerRight_id (R := k)]; simp
  have hρ' : h ▷ 𝟙 b ≫ (rightUnitor Y).hom = (rightUnitor Z).hom ≫ h := by
    rw [TwoSupercategory.whiskerRight_id (R := k)]; simp
  have hx := TwoSupercategory.super_interchange (R := k) hh hc
  unfold postCoeff
  calc h ≫ (rightUnitor Y).inv ≫ Y ◁ c ≫ (rightUnitor Y).hom
      = (rightUnitor Z).inv ≫ (h ▷ 𝟙 b ≫ Y ◁ c) ≫ (rightUnitor Y).hom := by
        rw [← Category.assoc, hρ]; simp
    _ = koszulSign p q • ((rightUnitor Z).inv ≫ Z ◁ c ≫ h ▷ 𝟙 b ≫ (rightUnitor Y).hom) := by
        rw [hx, Preadditive.zsmul_comp, Preadditive.comp_zsmul]; simp
    _ = koszulSign p q • (((rightUnitor Z).inv ≫ Z ◁ c ≫ (rightUnitor Z).hom) ≫ h) := by
        rw [hρ']; simp

end Action

section Grading

variable (k) in
/-- A **coefficient grading** of `b`: a `ℤ`-filtration of `End(𝟙 b)` by subsets, with the
identity in degree `0`, degrees additive under composition, and each degree stable under the
parity projections. This is all the transport uses; it is what a grading of the reservoir
coefficients alone provides, without a grading of the whole category `b ⟶ b`. -/
structure CoeffGrading (b : B) where
  /-- The coefficients of degree `m`. -/
  deg : ℤ → Set (𝟙 b ⟶ 𝟙 b)
  id_mem : 𝟙 (𝟙 b) ∈ deg 0
  comp_mem {m n : ℤ} {c c' : 𝟙 b ⟶ 𝟙 b} : c ∈ deg m → c' ∈ deg n → c ≫ c' ∈ deg (m + n)
  proj_mem {m : ℤ} (q : ZMod 2) {c : 𝟙 b ⟶ 𝟙 b} : c ∈ deg m → proj k q c ∈ deg m

omit [TwoSupercategory k B] in
variable (k) in
/-- The coefficient grading of `b` given by a graded supercategory structure on `b ⟶ b`. -/
def CoeffGrading.ofGraded (b : B) [GradedSupercategory k (b ⟶ b)] : CoeffGrading k b where
  deg m := (degree (R := k) (𝟙 b) (𝟙 b) m : Set (𝟙 b ⟶ 𝟙 b))
  id_mem := id_mem_degree (R := k) (𝟙 b)
  comp_mem hc hc' := comp_mem_degree hc hc'
  proj_mem q := fun h => proj_mem_degree (R := k) q h

end Grading

section Ideal

variable {a b : B} (Gr : CoeffGrading k b)

/-- Generators of the `n`-th power of the reservoir coefficient ideal: `postCoeff Z c ≫ h` with
`c` homogeneous of degree at least `n`. -/
def coeffGen (n : ℕ) (Z Y : a ⟶ b) : Set (Z ⟶ Y) :=
  {f | ∃ m : ℤ, (n : ℤ) ≤ m ∧ ∃ c ∈ Gr.deg m, ∃ h : Z ⟶ Y,
    f = postCoeff Z c ≫ h}

/-- The `n`-th power of the reservoir coefficient ideal on morphisms `Z ⟶ Y` of `a ⟶ b`
(`SwappedHomInversion.md` §4). -/
def coeffIdeal (n : ℕ) (Z Y : a ⟶ b) : Submodule k (Z ⟶ Y) :=
  Submodule.span k (coeffGen Gr n Z Y)

variable {Gr}

omit [TwoSupercategory k B] in
theorem postCoeff_comp_mem {n : ℕ} {m : ℤ} (hm : (n : ℤ) ≤ m) {Z Y : a ⟶ b}
    {c : 𝟙 b ⟶ 𝟙 b} (hc : c ∈ Gr.deg m) (h : Z ⟶ Y) :
    postCoeff Z c ≫ h ∈ coeffIdeal Gr n Z Y :=
  Submodule.subset_span ⟨m, hm, c, hc, h, rfl⟩

omit [TwoSupercategory k B] in
theorem postCoeff_mem {n : ℕ} {m : ℤ} (hm : (n : ℤ) ≤ m) (Z : a ⟶ b)
    {c : 𝟙 b ⟶ 𝟙 b} (hc : c ∈ Gr.deg m) :
    postCoeff Z c ∈ coeffIdeal Gr n Z Z := by
  simpa using postCoeff_comp_mem hm hc (𝟙 Z)

/-- Every morphism lies in the zeroth power. -/
theorem mem_coeffIdeal_zero {Z Y : a ⟶ b} (f : Z ⟶ Y) : f ∈ coeffIdeal Gr 0 Z Y := by
  simpa [postCoeff_id (k := k)] using postCoeff_comp_mem (k := k) (le_refl (0 : ℤ))
    Gr.id_mem f

omit [TwoSupercategory k B] in
/-- `coeffIdeal` is a right ideal. -/
theorem coeffIdeal_comp_right {n : ℕ} {Z Y V : a ⟶ b} {f : Z ⟶ Y}
    (hf : f ∈ coeffIdeal Gr n Z Y) (g : Y ⟶ V) : f ≫ g ∈ coeffIdeal Gr n Z V := by
  refine (Submodule.span_le (p := (coeffIdeal Gr n Z V).comap (Linear.rightComp k Z g))).2
    ?_ hf
  rintro _ ⟨m, hm, c, hc, h, rfl⟩
  simpa using postCoeff_comp_mem hm hc (h ≫ g)

/-- A homogeneous coefficient of degree `≥ n` composed after any morphism lies in `Jₙ`. -/
theorem comp_postCoeff_mem {n : ℕ} {m : ℤ} (hm : (n : ℤ) ≤ m) {Z Y : a ⟶ b}
    {c : 𝟙 b ⟶ 𝟙 b} (hc : c ∈ Gr.deg m) (h : Z ⟶ Y) :
    h ≫ postCoeff Y c ∈ coeffIdeal Gr n Z Y := by
  have hc' : ∀ q, proj k q c ∈ Gr.deg m :=
    fun q => Gr.proj_mem q hc
  refine Supercategory.induction_on (R := k) h (by simp) (fun p g hg => ?_)
    (fun g g' hg hg' => by rw [Preadditive.add_comp]; exact Submodule.add_mem _ hg hg')
  rw [← proj_add_proj (R := k) c, postCoeff_add (k := k), Preadditive.comp_add,
    comp_postCoeff hg (proj_mem 0 c), comp_postCoeff hg (proj_mem 1 c)]
  exact Submodule.add_mem _ (Submodule.smul_of_tower_mem _ _ (postCoeff_comp_mem hm (hc' 0) g))
    (Submodule.smul_of_tower_mem _ _ (postCoeff_comp_mem hm (hc' 1) g))

/-- `coeffIdeal` is a left ideal: reservoir coefficients pass every Hom-sector morphism. -/
theorem coeffIdeal_comp_left {n : ℕ} {V Z Y : a ⟶ b} (g : V ⟶ Z) {f : Z ⟶ Y}
    (hf : f ∈ coeffIdeal Gr n Z Y) : g ≫ f ∈ coeffIdeal Gr n V Y := by
  refine (Submodule.span_le (p := (coeffIdeal Gr n V Y).comap (Linear.leftComp k Y g))).2
    ?_ hf
  rintro _ ⟨m, hm, c, hc, h, rfl⟩
  change g ≫ postCoeff Z c ≫ h ∈ coeffIdeal Gr n V Y
  rw [← Category.assoc]
  exact coeffIdeal_comp_right (comp_postCoeff_mem hm hc g) h

/-- Two-sided form: `h ≫ postCoeff c ≫ h'` lies in `Jₙ` when `c` has degree `≥ n`. -/
theorem comp_postCoeff_comp_mem {n : ℕ} {m : ℤ} (hm : (n : ℤ) ≤ m) {V Z Y : a ⟶ b}
    {c : 𝟙 b ⟶ 𝟙 b} (hc : c ∈ Gr.deg m) (h : V ⟶ Z) (h' : Z ⟶ Y) :
    h ≫ postCoeff Z c ≫ h' ∈ coeffIdeal Gr n V Y :=
  coeffIdeal_comp_left h (postCoeff_comp_mem hm hc h')

theorem postCoeff_comp_mem_add {n₁ n₂ : ℕ} {m : ℤ} (hm : (n₁ : ℤ) ≤ m) {Z Y : a ⟶ b}
    {c : 𝟙 b ⟶ 𝟙 b} (hc : c ∈ Gr.deg m) {g : Z ⟶ Y}
    (hg : g ∈ coeffIdeal Gr n₂ Z Y) : postCoeff Z c ≫ g ∈ coeffIdeal Gr (n₁ + n₂) Z Y := by
  refine (Submodule.span_le
    (p := (coeffIdeal Gr (n₁ + n₂) Z Y).comap (Linear.leftComp k Y (postCoeff Z c)))).2 ?_ hg
  rintro _ ⟨m', hm', c', hc', h, rfl⟩
  change postCoeff Z c ≫ postCoeff Z c' ≫ h ∈ coeffIdeal Gr (n₁ + n₂) Z Y
  rw [← Category.assoc, ← postCoeff_comp (k := k)]
  exact postCoeff_comp_mem (by push_cast; omega) (Gr.comp_mem hc hc') h

/-- **Multiplicativity**: `Jₘ ≫ Jₙ ⊆ Jₘ₊ₙ`. -/
theorem coeffIdeal_comp_mem {n₁ n₂ : ℕ} {Z Y V : a ⟶ b} {f : Z ⟶ Y} {g : Y ⟶ V}
    (hf : f ∈ coeffIdeal Gr n₁ Z Y) (hg : g ∈ coeffIdeal Gr n₂ Y V) :
    f ≫ g ∈ coeffIdeal Gr (n₁ + n₂) Z V := by
  refine (Submodule.span_le
    (p := (coeffIdeal Gr (n₁ + n₂) Z V).comap (Linear.rightComp k Z g))).2 ?_ hf
  rintro _ ⟨m, hm, c, hc, h, rfl⟩
  change (postCoeff Z c ≫ h) ≫ g ∈ coeffIdeal Gr (n₁ + n₂) Z V
  rw [Category.assoc]
  exact postCoeff_comp_mem_add hm hc (coeffIdeal_comp_left h hg)

/-- **Nilpotence**: if `End(𝟙 b)` vanishes in degrees `≥ M`, then `J_M = 0`. -/
theorem eq_zero_of_mem_coeffIdeal {M : ℕ}
    (hM : ∀ m : ℤ, (M : ℤ) ≤ m → ∀ c ∈ Gr.deg m, c = 0)
    {Z Y : a ⟶ b} {f : Z ⟶ Y} (hf : f ∈ coeffIdeal Gr M Z Y) : f = 0 := by
  have : coeffIdeal Gr M Z Y ≤ ⊥ := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨m, hm, c, hc, h, rfl⟩
    rw [hM m hm c hc, postCoeff_zero (k := k), Limits.zero_comp]
    exact Submodule.zero_mem _
  simpa using this hf

variable (a Gr) in
/-- **The reservoir coefficient ideal** (`SwappedHomInversion.md` §4) as a
`ProbeWindow.CoefficientIdeal` on `a ⟶ b`, for any predicate `Pr` on its objects, when
`End(𝟙 b)` vanishes in degrees `≥ M`. -/
def reservoirCoefficientIdeal (M : ℕ)
    (hM : ∀ m : ℤ, (M : ℤ) ≤ m → ∀ c ∈ Gr.deg m, c = 0)
    (Pr : (a ⟶ b) → Prop) : CoefficientIdeal Pr where
  mem n _ _ f := f ∈ coeffIdeal Gr n _ _
  zero_mem _ := Submodule.zero_mem _
  add_mem := Submodule.add_mem _
  neg_mem := Submodule.neg_mem _
  mem_zero f _ _ := mem_coeffIdeal_zero f
  comp_mem := coeffIdeal_comp_mem
  bound := M
  eq_zero := eq_zero_of_mem_coeffIdeal hM

@[simp] theorem reservoirCoefficientIdeal_mem (M : ℕ)
    (hM : ∀ m : ℤ, (M : ℤ) ≤ m → ∀ c ∈ Gr.deg m, c = 0)
    (Pr : (a ⟶ b) → Prop) (n : ℕ) {Z Y : a ⟶ b} (f : Z ⟶ Y) :
    (reservoirCoefficientIdeal a Gr M hM Pr).mem n f ↔ f ∈ coeffIdeal Gr n Z Y := Iff.rfl

end Ideal

end ProbeWindow

section Reservoir

open OddMath.SKM ProbeWindow

variable {I X : Type u} [AddCommGroup X] {k : Type u} [CommRing k]
  {B : Type u} [BicategoryStruct.{u, u} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear k (a ⟶ b)]
  [∀ a b : B, Supercategory k (a ⟶ b)] [TwoSupercategory k B]
  {D : Datum I X} {Sc : Scalars D k}

namespace ProbeReservoir

variable (P : ProbeReservoir k B D Sc) {sy : Symmetrizer D}
  (G : RouquierGrading P.W sy)

omit [TwoSupercategory k B] in
/-- The vanishing degree of `End(𝟙)` at the reservoir weight `μ`, from `BoundedAbove`. -/
theorem exists_degree_eq_zero (hG : G.BoundedAbove) (μ : X) :
    ∃ M : ℕ, ∀ m : ℤ, (M : ℤ) ≤ m → ∀ c, c ∈ G.deg (𝟙 (P.W.obj μ)) (𝟙 (P.W.obj μ)) m →
      c = 0 := by
  obtain ⟨M, hM⟩ := hG μ
  exact ⟨M.toNat + 1, fun m hm c hc => hM m (by omega) c hc⟩

omit [TwoSupercategory k B] in
/-- The coefficient grading of the reservoir object `W(μ)` given by `G`. -/
def coeffGrading (μ : X) : CoeffGrading k (P.W.obj μ) :=
  letI := G.graded μ μ
  CoeffGrading.ofGraded k (P.W.obj μ)

omit [TwoSupercategory k B] in
theorem mem_coeffGrading_deg {μ : X} {m : ℤ} {c : 𝟙 (P.W.obj μ) ⟶ 𝟙 (P.W.obj μ)} :
    c ∈ (P.coeffGrading G μ).deg m ↔ c ∈ G.deg _ _ m := by
  unfold coeffGrading CoeffGrading.ofGraded
  exact Iff.rfl

/-- **The coefficient ideal on the Hom sector `P.H t`**: post-whiskering by the
positive-degree reservoir coefficients at `P.muM t`, filtered by degree, with nilpotence bound
from `BoundedAbove`. This is the `ProbeWindow.CoefficientIdeal` hypothesis of the central
inversion (`SwappedHomInversion.md` §4), for any predicate `Pr` on the Hom-sector objects. -/
def homCoefficientIdeal (hG : G.BoundedAbove) (t : Sector I) (Pr : P.H t → Prop) :
    CoefficientIdeal Pr :=
  reservoirCoefficientIdeal (P.T.obj (-P.muP t)) (P.coeffGrading G (P.muM t))
    (P.exists_degree_eq_zero G hG (P.muM t)).choose
    (P.exists_degree_eq_zero G hG (P.muM t)).choose_spec Pr

theorem homCoefficientIdeal_mem (hG : G.BoundedAbove) (t : Sector I) (Pr : P.H t → Prop)
    (n : ℕ) {Z Y : P.H t} (f : Z ⟶ Y) :
    (P.homCoefficientIdeal G hG t Pr).mem n f ↔
      f ∈ coeffIdeal (P.coeffGrading G (P.muM t)) n Z Y := Iff.rfl

/-- **Positive-degree reservoir coefficients lie in `J₁`** on the Hom sector, with arbitrary
Hom-sector morphisms (probe words included) on either side. -/
theorem comp_postCoeff_comp_mem_homCoefficientIdeal (hG : G.BoundedAbove) (t : Sector I)
    (Pr : P.H t → Prop) {m : ℤ} (hm : 0 < m)
    {c : 𝟙 (P.W.obj (P.muM t)) ⟶ 𝟙 (P.W.obj (P.muM t))}
    (hc : c ∈ G.deg _ _ m) {V Z Y : P.H t} (h : V ⟶ Z) (h' : Z ⟶ Y) :
    (P.homCoefficientIdeal G hG t Pr).mem 1 (h ≫ ProbeWindow.postCoeff Z c ≫ h') :=
  ProbeWindow.comp_postCoeff_comp_mem (Gr := P.coeffGrading G (P.muM t)) (n := 1)
    (by omega) hc h h'

/-- **(N) on the Hom sector**: the contracted reservoir closure `b_(s,r)` of
`SwappedHomInversion.md` (8), of degree `2dᵢ(r+s+1) > 0`, acts on every Hom-sector object by
an element of `J₁`; hence products of more than the bound of them vanish
(`CoefficientIdeal.isNilpotent`). -/
theorem closure_mem_homCoefficientIdeal (hG : G.BoundedAbove) (t : Sector I) (Pr : P.H t → Prop)
    (i : I) {a c : X}
    (h₁ : a + D.α i = P.muM t) (h₂ : P.muM t + D.α i = c)
    {y : P.W.E i h₂ ≫ P.W.F i h₂ ⟶ P.W.F i h₁ ≫ P.W.E i h₁} (hy : y ∈ G.deg _ _ 0) (r s : ℕ)
    {V Z Y : P.H t} (h : V ⟶ Z) (h' : Z ⟶ Y) :
    (P.homCoefficientIdeal G hG t Pr).mem 1 (h ≫ ProbeWindow.postCoeff Z
      (((P.W.adj i h₂).unit ≫ rouquierPower (P.W.dot i h₂) r ▷ P.W.F i h₂) ≫ y ≫
        (P.W.F i h₁ ◁ rouquierPower (P.W.dot i h₁) s ≫ (P.W.adj i h₁).counit)) ≫ h') := by
  refine P.comp_postCoeff_comp_mem_homCoefficientIdeal G hG t Pr ?_
    (G.closure_mem i h₁ h₂ hy r s) h h'
  have := sy.pos i
  positivity

/-- **(J) on the Hom sector, positive height**: the boundary contraction `(m, n)` with `n > m`
(the `r > j` contractions `v_R(r) a_R,j` of `SwappedHomInversion.md` (7)), of degree
`2dᵢ(n-m) > 0`, acts by an element of `J₁`. -/
theorem boundaryPos_mem_homCoefficientIdeal (hG : G.BoundedAbove) (t : Sector I) (Pr : P.H t → Prop)
    (i : I)
    {a c : X} (h₁ : a + D.α i = P.muM t) (h₂ : P.muM t + D.α i = c)
    (hh : 0 ≤ D.h i (P.muM t)) {m n : ℕ} (hm : m < (D.h i (P.muM t)).toNat) (hmn : m < n)
    {V Z Y : P.H t} (h : V ⟶ Z) (h' : Z ⟶ Y) :
    (P.homCoefficientIdeal G hG t Pr).mem 1
      (h ≫ ProbeWindow.postCoeff Z ((P.W.loc i h₁ h₂).boundaryPos hh m n) ≫ h') := by
  refine P.comp_postCoeff_comp_mem_homCoefficientIdeal G hG t Pr ?_
    (G.boundaryPos_mem i h₁ h₂ hh m n hm) h h'
  have := sy.pos i
  have : (0 : ℤ) < n - m := by omega
  positivity

/-- **(J) on the Hom sector, negative height**: the boundary contraction `(m, n)` with `m > n`
(the `r > j` contractions `b_R,j u_R(r)` of `SwappedHomInversion.md` (7)), of degree
`2dᵢ(m-n) > 0`, acts by an element of `J₁`. -/
theorem boundaryNeg_mem_homCoefficientIdeal (hG : G.BoundedAbove) (t : Sector I) (Pr : P.H t → Prop)
    (i : I)
    {a c : X} (h₁ : a + D.α i = P.muM t) (h₂ : P.muM t + D.α i = c)
    (hh : D.h i (P.muM t) ≤ 0) {m n : ℕ} (hn : n < (-D.h i (P.muM t)).toNat) (hmn : n < m)
    {V Z Y : P.H t} (h : V ⟶ Z) (h' : Z ⟶ Y) :
    (P.homCoefficientIdeal G hG t Pr).mem 1
      (h ≫ ProbeWindow.postCoeff Z ((P.W.loc i h₁ h₂).boundaryNeg hh m n) ≫ h') := by
  refine P.comp_postCoeff_comp_mem_homCoefficientIdeal G hG t Pr ?_
    (G.boundaryNeg_mem i h₁ h₂ hh m n hn) h h'
  have := sy.pos i
  have : (0 : ℤ) < m - n := by omega
  positivity

end ProbeReservoir

end Reservoir

end OddMath.QuiverHecke.SwappedAssembly
