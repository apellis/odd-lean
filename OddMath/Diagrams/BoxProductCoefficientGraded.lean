/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.Diagrams.GradedTensor
import OddMath.Diagrams.RestrictScalars
import StringDiagrams.Super.BoxProductGraded

/-!
# The product `C ⊠ D` over a graded ground ring

J. Brundan, A. P. Ellis, *Monoidal supercategories*, arXiv:1603.05928v3, §6 (after
Definition 6.1), with a graded ground ring. Let `R` be a commutative `K`-algebra graded by
`K`-submodules `𝒜 : ℤ → Submodule K R`, and let `C`, `D` be supercategories over `R` that are
graded supercategories over `K` (for the restricted scalars), with `𝒜 a • Hom_n ⊆ Hom_{a+n}`.
Then `C ⊠ D`, formed over `R`, is a graded supercategory over `K`: the morphisms of degree `n`
are the `K`-spans of the `f ⊗ g` with `deg f + deg g = n`
(`BoxProdCoefficient.gradedSupercategory`). The grading of the tensor products of Hom modules
over `R` is `GradedTensor.isInternal_part`.

For `R = K` with the trivial grading this is the grading `BoxProd.instGradedSupercategory`.
This grades the ELV box product over the truncated Rees ring
(`docs/Nondegeneracy/Phase2Plan.md`, step 2, item 4).
-/

noncomputable section

namespace OddMath.Diagrams.BoxProdCoefficient

open CategoryTheory StringDiagrams Supercategory GradedSupercategory BoxProd DirectSum
  TensorProduct

universe u w₁ w₂

variable {K : Type u} [CommRing K] {R : Type u} [CommRing R] [Algebra K R]

/-- Two families with the same members: one is an internal direct sum if the other is. -/
theorem isInternal_of_mem_iff {ι M S T : Type*} [DecidableEq ι] [AddCommMonoid M]
    [SetLike S M] [AddSubmonoidClass S M] [SetLike T M] [AddSubmonoidClass T M]
    {A : ι → S} {B : ι → T} (hAB : ∀ i x, x ∈ A i ↔ x ∈ B i) (h : DirectSum.IsInternal A) :
    DirectSum.IsInternal B := by
  let e : (⨁ i, A i) ≃+ (⨁ i, B i) :=
    DFinsupp.mapRange.addEquiv fun i =>
      { toFun := fun x => ⟨x, (hAB i x).1 x.2⟩
        invFun := fun x => ⟨x, (hAB i x).2 x.2⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl
        map_add' := fun _ _ => rfl }
  have he : (DirectSum.coeAddMonoidHom B).comp e.toAddMonoidHom = DirectSum.coeAddMonoidHom A := by
    ext i x
    simp only [AddMonoidHom.coe_comp, Function.comp_apply, AddEquiv.coe_toAddMonoidHom, e,
      DirectSum.of]
    rfl
  have : ⇑(DirectSum.coeAddMonoidHom B) = DirectSum.coeAddMonoidHom A ∘ e.symm := by
    funext y
    rw [← he]
    simp
  unfold DirectSum.IsInternal at h ⊢
  rw [this]
  exact h.comp e.symm.bijective

section Parity

variable {E : Type w₁} [Category.{u} E] [Preadditive E] [Linear R E] [Supercategory R E]
  [Linear K E] [Supercategory K E]

omit [Algebra K R] in
/-- If the parity submodules over `K` and over `R` have the same elements, the parity
projections agree. -/
theorem proj_eq_proj (hpar : ∀ (X Y : E) (p : ZMod 2) (f : X ⟶ Y),
    f ∈ parity (R := K) X Y p ↔ f ∈ parity (R := R) X Y p)
    {X Y : E} (p : ZMod 2) (f : X ⟶ Y) : proj K p f = proj R p f := by
  refine proj_eq_of_add (R := K) (p := p) (proj_add_proj_add_one (R := R) p f).symm ?_ ?_
  · exact (hpar X Y p _).2 (proj_mem (R := R) p f)
  · exact (hpar X Y (p + 1) _).2 (proj_mem (R := R) (p + 1) f)

variable [GradedSupercategory K E]
  (hpar : ∀ (X Y : E) (p : ZMod 2) (f : X ⟶ Y),
    f ∈ parity (R := K) X Y p ↔ f ∈ parity (R := R) X Y p)

include hpar in
omit [Algebra K R] in
theorem projR_mem_degree {X Y : E} {n : ℤ} (p : ZMod 2) {f : X ⟶ Y}
    (hf : f ∈ degree (R := K) X Y n) : proj R p f ∈ degree (R := K) X Y n := by
  rw [← proj_eq_proj hpar]
  exact proj_mem_degree p hf

include hpar in
omit [Algebra K R] in
theorem twistR_mem_degree {X Y : E} {n : ℤ} (p : ZMod 2) {f : X ⟶ Y}
    (hf : f ∈ degree (R := K) X Y n) : twist R p f ∈ degree (R := K) X Y n := by
  rw [twist_apply]
  refine add_mem (projR_mem_degree hpar 0 hf) ?_
  rcases parity_eq_zero_or_one p with rfl | rfl
  · rw [sign_zero, one_smul]
    exact projR_mem_degree hpar 1 hf
  · rw [sign_one, neg_one_smul]
    exact neg_mem (projR_mem_degree hpar 1 hf)

end Parity

variable (𝒜 : ℤ → Submodule K R) [Decomposition 𝒜]
  {C : Type w₁} [Category.{u} C] [Preadditive C] [Linear R C] [Supercategory R C]
  [Linear K C] [∀ X Y : C, IsScalarTower K R (X ⟶ Y)] [Supercategory K C]
  [GradedSupercategory K C]
  {D : Type w₂} [Category.{u} D] [Preadditive D] [Linear R D] [Supercategory R D]
  [Linear K D] [Supercategory K D]
  [GradedSupercategory K D]

/-- The degree-`n` part of `Hom_{C ⊠ D}(X, Y) = Hom_C(X₁, Y₁) ⊗_R Hom_D(X₂, Y₂)`: the `K`-span
of the `f ⊗ g` with `deg f + deg g = n`, as an additive subgroup. -/
def homPart (X Y : BoxProd R C D) (n : ℤ) : AddSubgroup (X ⟶ Y) :=
  (GradedTensor.part (R := R) (degree (R := K) X.fst Y.fst) (degree (R := K) X.snd Y.snd)
    n).toAddSubgroup

/-- A morphism of `C ⊠ D` as an element of the tensor product of Hom modules over `R`. -/
abbrev toTensor {X Y : BoxProd R C D} (y : X ⟶ Y) : (X.fst ⟶ Y.fst) ⊗[R] (X.snd ⟶ Y.snd) := y

/-- The degree-`n` part of `Hom_{C ⊠ D}(X, Y)` as a `K`-submodule for the scalars restricted
from `R`. -/
def homDegree (X Y : BoxProd R C D) (n : ℤ) :
    letI := Linear.restrictScalars K R (BoxProd R C D)
    Submodule K (X ⟶ Y) :=
  letI := Linear.restrictScalars K R (BoxProd R C D)
  { homPart X Y n with
    smul_mem' := fun c y hy => by
      change toTensor (algebraMap K R c • y) ∈
        GradedTensor.part (R := R) (degree (R := K) X.fst Y.fst) (degree (R := K) X.snd Y.snd) n
      have e : toTensor (algebraMap K R c • y) = c • toTensor y :=
        algebraMap_smul R c (toTensor y)
      rw [e]
      exact Submodule.smul_mem _ c hy }

theorem mem_homDegree {X Y : BoxProd R C D} {n : ℤ} {y : X ⟶ Y} :
    y ∈ homDegree (K := K) X Y n ↔ toTensor y ∈
      GradedTensor.part (R := R) (degree (R := K) X.fst Y.fst) (degree (R := K) X.snd Y.snd) n :=
  Iff.rfl

/-- Induction on the degree-`n` part of a Hom module of `C ⊠ D`: it is generated by the
`f ⊗ g` with `deg f + deg g = n` under sums and the `K`-action. -/
theorem homDegree_induction {X Y : BoxProd R C D} {n : ℤ} {motive : (X ⟶ Y) → Prop}
    (zero : motive 0) (add : ∀ y y', motive y → motive y' → motive (y + y'))
    (smul : ∀ (c : K) y, motive y → motive (algebraMap K R c • y))
    (tmul : ∀ p q : ℤ, p + q = n → ∀ f ∈ degree (R := K) X.fst Y.fst p,
      ∀ g ∈ degree (R := K) X.snd Y.snd q, motive (tmulHom f g))
    {y : X ⟶ Y} (hy : y ∈ homDegree (K := K) X Y n) : motive y := by
  suffices H : ∀ z ∈ GradedTensor.part (R := R) (degree (R := K) X.fst Y.fst)
      (degree (R := K) X.snd Y.snd) n, motive z from H _ (mem_homDegree.1 hy)
  intro z hz
  induction hz using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨p, q, hpq, f, hf, g, hg, rfl⟩ := hz
    exact tmul p q hpq f hf g hg
  | zero => exact zero
  | add z z' _ _ hz hz' => exact add z z' hz hz'
  | smul c z _ hz =>
    have e : (c • z : (X.fst ⟶ Y.fst) ⊗[R] (X.snd ⟶ Y.snd)) = toTensor (algebraMap K R c • z) :=
      (algebraMap_smul R c z).symm
    rw [e]
    exact smul c z hz

/-- `f ⊗ g` has degree `deg f + deg g`. -/
theorem tmulHom_mem_homDegree {X Y : BoxProd R C D} {p q : ℤ} {f : X.fst ⟶ Y.fst}
    {g : X.snd ⟶ Y.snd} (hf : f ∈ degree (R := K) X.fst Y.fst p)
    (hg : g ∈ degree (R := K) X.snd Y.snd q) : tmulHom f g ∈ homDegree (K := K) X Y (p + q) :=
  mem_homDegree.2 (GradedTensor.tmul_mem_part hf hg)

/-- The degree parts are closed under the `K`-action restricted from `R`. -/
theorem algebraMap_smul_mem_homDegree {X Y : BoxProd R C D} {n : ℤ} (c : K) {y : X ⟶ Y}
    (hy : y ∈ homDegree (K := K) X Y n) : algebraMap K R c • y ∈ homDegree (K := K) X Y n :=
  letI := Linear.restrictScalars K R (BoxProd R C D)
  (homDegree (K := K) X Y n).smul_mem c hy

variable {𝒜}
  (hC : ∀ {X Y : C} {a n : ℤ} {r : R} {f : X ⟶ Y}, r ∈ 𝒜 a → f ∈ degree (R := K) X Y n →
    r • f ∈ degree (R := K) X Y (a + n))
  (hD : ∀ {X Y : D} {a n : ℤ} {r : R} {f : X ⟶ Y}, r ∈ 𝒜 a → f ∈ degree (R := K) X Y n →
    r • f ∈ degree (R := K) X Y (a + n))

include hC hD in
/-- The degree parts form an internal direct sum decomposition of each Hom module. -/
theorem isInternal_homDegree (X Y : BoxProd R C D) :
    letI := Linear.restrictScalars K R (BoxProd R C D)
    DirectSum.IsInternal (homDegree (K := K) X Y) := by
  let := (isInternal_degree (R := K) X.fst Y.fst).chooseDecomposition
  let := (isInternal_degree (R := K) X.snd Y.snd).chooseDecomposition
  exact isInternal_of_mem_iff (fun _ _ => mem_homDegree.symm)
    (GradedTensor.isInternal_part 𝒜 _ _ hC hD)

variable
  (hpC : ∀ (X Y : C) (p : ZMod 2) (f : X ⟶ Y),
    f ∈ parity (R := K) X Y p ↔ f ∈ parity (R := R) X Y p)
  (hpD : ∀ (X Y : D) (p : ZMod 2) (f : X ⟶ Y),
    f ∈ parity (R := K) X Y p ↔ f ∈ parity (R := R) X Y p)

include hpC hpD in
/-- The parity components of a morphism of degree `n` have degree `n`. -/
theorem projR_mem_homDegree {X Y : BoxProd R C D} {n : ℤ} (p : ZMod 2) {y : X ⟶ Y}
    (hy : y ∈ homDegree (K := K) X Y n) : proj R p y ∈ homDegree (K := K) X Y n := by
  refine homDegree_induction (motive := fun y => proj R p y ∈ homDegree (K := K) X Y n)
    ?_ (fun y y' hy hy' => ?_) (fun c y hy => ?_) (fun a b hab f hf g hg => ?_) hy
  · rw [map_zero]; exact zero_mem _
  · rw [map_add]; exact add_mem hy hy'
  · rw [LinearMap.map_smul]; exact algebraMap_smul_mem_homDegree c hy
  ·
    rw [proj_eq_homObj_proj, ← hab]
    change (SVec.tensorObj (homSVec R C X.fst Y.fst) (homSVec R D X.snd Y.snd)).proj p
      (f ⊗ₜ[R] g) ∈ _
    rw [SVec.tensorObj_proj_tmul, homSVec_proj, homSVec_proj, homSVec_proj, homSVec_proj]
    exact add_mem
      (tmulHom_mem_homDegree (projR_mem_degree hpC 0 hf) (projR_mem_degree hpD p hg))
      (tmulHom_mem_homDegree (projR_mem_degree hpC 1 hf) (projR_mem_degree hpD (1 + p) hg))

include hpC hpD in
/-- Composition in `C ⊠ D` adds degrees. -/
theorem comp_mem_homDegree {X Y Z : BoxProd R C D} {m n : ℤ} {x : X ⟶ Y} {y : Y ⟶ Z}
    (hx : x ∈ homDegree (K := K) X Y m) (hy : y ∈ homDegree (K := K) Y Z n) :
    x ≫ y ∈ homDegree (K := K) X Z (m + n) := by
  refine homDegree_induction (motive := fun x => x ≫ y ∈ homDegree (K := K) X Z (m + n))
    ?_ (fun x x' hx hx' => ?_) (fun c x hx => ?_) (fun a b hab f hf g hg => ?_) hx
  · rw [Limits.zero_comp]; exact zero_mem _
  · rw [Preadditive.add_comp]; exact add_mem hx hx'
  · rw [Linear.smul_comp]; exact algebraMap_smul_mem_homDegree c hx
  refine homDegree_induction
    (motive := fun y => tmulHom f g ≫ y ∈ homDegree (K := K) X Z (m + n))
    ?_ (fun y y' hy hy' => ?_) (fun c y hy => ?_) (fun a' b' hab' h hh l hl => ?_) hy
  · rw [Limits.comp_zero]; exact zero_mem _
  · rw [Preadditive.comp_add]; exact add_mem hy hy'
  · rw [Linear.comp_smul]; exact algebraMap_smul_mem_homDegree c hy
  rw [tmulHom_comp_tmulHom_eq, show m + n = (a + a') + (b + b') by omega]
  exact add_mem
    (tmulHom_mem_homDegree (comp_mem_degree (projR_mem_degree hpC 0 hf) hh)
      (comp_mem_degree hg hl))
    (tmulHom_mem_homDegree (comp_mem_degree (projR_mem_degree hpC 1 hf) hh)
      (comp_mem_degree hg (twistR_mem_degree hpD 1 hl)))

include hC hD hpC hpD in
/-- **Brundan–Ellis, §6 (after Definition 6.1), over a graded ground ring.** For supercategories
`C`, `D` over `R` that are graded over `K` compatibly with the grading `𝒜` of `R`, the product
`C ⊠ D` over `R` is a graded supercategory over `K`: the morphisms of degree `n` are the
`K`-spans of the `f ⊗ g` with `deg f + deg g = n`. -/
@[instance_reducible]
def gradedSupercategory :
    letI := Linear.restrictScalars K R (BoxProd R C D)
    letI := Supercategory.restrictScalars K R (BoxProd R C D)
    GradedSupercategory K (BoxProd R C D) :=
  letI := Linear.restrictScalars K R (BoxProd R C D)
  letI := Supercategory.restrictScalars K R (BoxProd R C D)
  { degree := homDegree
    isInternal_degree := isInternal_homDegree hC hD
    proj_mem_degree := fun p hy => by
      rw [proj_eq_proj (fun _ _ _ _ => Submodule.restrictScalars_mem K _ _)]
      exact projR_mem_homDegree hpC hpD p hy
    id_mem_degree := fun X => by
      have := tmulHom_mem_homDegree (K := K) (X := X) (Y := X)
        (id_mem_degree (R := K) X.fst) (id_mem_degree (R := K) X.snd)
      rwa [add_zero, ← id_eq_tmulHom] at this
    comp_mem_degree := comp_mem_homDegree hpC hpD }

end OddMath.Diagrams.BoxProdCoefficient
