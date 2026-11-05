/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import StringDiagrams.Grading

/-!
# Presentations graded with coefficients of positive degree

`StringDiagrams.Grading` grades a presented category when every scalar has degree zero. Here
the coefficient ring `R` is itself graded, by a graded algebra `𝒜 : A → Submodule K R`, and a
linear combination `Σ r_g g` of diagrams has degree `d` when each coefficient `r_g` lies in
`𝒜 (d - deg g)`. A presentation is *coefficient-graded homogeneous* when each defining
relation lies in one degree in this sense. Then every Hom group of the presented category is
the internal direct sum of its homogeneous parts.

For the trivial grading of `R` (everything in degree `0`) this is the grading of
`StringDiagrams.Grading`. The case of interest is `R = K[h]/(h^N)` with `h` in positive
degree: the Rees parameters `sᵢⱼ^{pq} h^{deg}` of a lower-degree parameter system make the
quiver Hecke presentation homogeneous in this sense, but not in the sense of
`StringDiagrams.Grading` (route step 2 of `docs/Nondegeneracy/Phase2Plan.md`).

The homogeneous parts are additive subgroups closed under multiplication by `𝒜 0`, hence
`K`-submodules once the Hom groups are viewed as `K`-modules.

## Main definitions and results

* `CoefficientGrading.part 𝒜 deg a b d`, `CoefficientGrading.component 𝒜 deg d`: the
  degree-`d` linear combinations of diagrams and the projection onto them.
* `CoefficientGrading.IsHomogeneous 𝒜 deg P`: every defining relation lies in one degree.
* `CoefficientGrading.component_mem_ideal`: the tensor ideal is homogeneous.
* `CoefficientGrading.presentedPart`, `CoefficientGrading.iSup_presentedPart`,
  `CoefficientGrading.iSupIndep_presentedPart`: the Hom groups of the presented category are
  the internal direct sums of their homogeneous parts.
-/

noncomputable section

namespace OddMath.Diagrams.CoefficientGrading

open CategoryTheory StringDiagrams

universe w v u₀ u₁ u₂

variable {S : Signature.{u₀, u₁, u₂}} {A : Type*} [AddCommGroup A]
  {K : Type*} [CommRing K] {R : Type w} [CommRing R] [Algebra K R]
  (𝒜 : A → Submodule K R) (deg : S.Gen → A)

variable {a b c : Obj S}

/-! ## Linear combinations of diagrams -/

/-- The linear combinations `Σ r_g g` of diagrams with `r_g ∈ 𝒜 (d - deg g)` for all `g`. -/
def part (a b : Obj S) (d : A) : AddSubgroup (LinDiagram R a b) where
  carrier := {f | ∀ g : a ⟶ b, f.toFinsupp g ∈ 𝒜 (d - Diagram.degree deg g)}
  add_mem' {f f'} hf hf' g := by
    change f.toFinsupp g + f'.toFinsupp g ∈ _
    exact add_mem (hf g) (hf' g)
  zero_mem' g := by
    change (0 : R) ∈ _
    exact zero_mem _
  neg_mem' {f} hf g := by
    change -f.toFinsupp g ∈ _
    exact neg_mem (hf g)

variable {𝒜 deg}

theorem mem_part_iff {f : LinDiagram R a b} {d : A} :
    f ∈ part 𝒜 deg a b d ↔ ∀ g : a ⟶ b, f.toFinsupp g ∈ 𝒜 (d - Diagram.degree deg g) :=
  Iff.rfl

theorem single_mem_part {g : a ⟶ b} {r : R} {m : A} (hr : r ∈ 𝒜 m) :
    (Finsupp.single g r : LinDiagram R a b) ∈ part 𝒜 deg a b (Diagram.degree deg g + m) := by
  classical
  intro g'
  change (Finsupp.single g r : (a ⟶ b) →₀ R) g' ∈ _
  rw [Finsupp.single_apply]
  split_ifs with h
  · subst h; rwa [add_sub_cancel_left]
  · exact zero_mem _

theorem single_mem_part' {g : a ⟶ b} {r : R} {d : A}
    (hr : r ∈ 𝒜 (d - Diagram.degree deg g)) :
    (Finsupp.single g r : LinDiagram R a b) ∈ part 𝒜 deg a b d := by
  have := single_mem_part (deg := deg) (g := g) hr
  rwa [add_sub_cancel] at this

/-- Induction over the homogeneous single terms of a homogeneous combination. -/
@[elab_as_elim]
theorem part_induction {d : A} {motive : LinDiagram R a b → Prop} (f : LinDiagram R a b)
    (hf : f ∈ part 𝒜 deg a b d) (zero : motive 0)
    (add : ∀ x y, motive x → motive y → motive (x + y))
    (single : ∀ (g : a ⟶ b) (r : R), r ∈ 𝒜 (d - Diagram.degree deg g) →
      motive (Finsupp.single g r)) : motive f := by
  have key : ∀ x : (a ⟶ b) →₀ R, (∀ g, x g ∈ 𝒜 (d - Diagram.degree deg g)) →
      motive (x : LinDiagram R a b) := by
    intro x
    induction x using Finsupp.induction with
    | zero => intro; exact zero
    | single_add g r x hg hr ih =>
      intro hx
      have hxg : x g = 0 := Finsupp.notMem_support_iff.mp hg
      refine add _ _ (single g r ?_) (ih fun g' => ?_)
      · have := hx g
        rwa [Finsupp.add_apply, Finsupp.single_eq_same, hxg, add_zero] at this
      · by_cases h : g' = g
        · subst h; rw [hxg]; exact zero_mem _
        · have := hx g'
          rwa [Finsupp.add_apply, Finsupp.single_eq_of_ne h, zero_add] at this
  exact key f.toFinsupp hf

theorem mapDomain_mem_part {a' b' : Obj S} (φ : (a ⟶ b) → (a' ⟶ b'))
    (hφ : ∀ g, Diagram.degree deg (φ g) = Diagram.degree deg g) {f : LinDiagram R a b} {d : A}
    (hf : f ∈ part 𝒜 deg a b d) :
    (Finsupp.mapDomain φ f.toFinsupp : LinDiagram R a' b') ∈ part 𝒜 deg a' b' d := by
  refine part_induction f hf ?_ ?_ ?_
  · rw [LinDiagram.toFinsupp, Finsupp.mapDomain_zero]; exact zero_mem _
  · intro x y hx hy
    rw [LinDiagram.toFinsupp, Finsupp.mapDomain_add]; exact add_mem hx hy
  · intro g r hr
    rw [LinDiagram.toFinsupp, Finsupp.mapDomain_single]
    exact single_mem_part' (by rwa [hφ])

theorem whisker_mem_part {f : LinDiagram R a b} {d : A} (hf : f ∈ part 𝒜 deg a b d)
    (u : Obj S) (v : List S.Colour) (hw : a.WhiskerOK u v) :
    LinDiagram.whisker f u v hw ∈ part 𝒜 deg _ _ d :=
  mapDomain_mem_part _ (fun g => Diagram.degree_whisker deg g u v hw) hf

section GradedMonoid

variable [SetLike.GradedMonoid 𝒜]

theorem of_mem_part (g : a ⟶ b) :
    (LinDiagram.of g : LinDiagram R a b) ∈ part 𝒜 deg a b (Diagram.degree deg g) := by
  have := single_mem_part (𝒜 := 𝒜) (deg := deg) (g := g) SetLike.GradedOne.one_mem
  rwa [add_zero] at this

theorem of_mem_part' (g : a ⟶ b) {d : A} (hd : Diagram.degree deg g = d) :
    (LinDiagram.of g : LinDiagram R a b) ∈ part 𝒜 deg a b d :=
  hd ▸ of_mem_part g

/-- Multiplying by a coefficient of degree `m` raises the degree by `m`. -/
theorem smul_mem_part {r : R} {m : A} (hr : r ∈ 𝒜 m) {f : LinDiagram R a b} {d : A}
    (hf : f ∈ part 𝒜 deg a b d) : r • f ∈ part 𝒜 deg a b (m + d) := by
  intro g
  change r * f.toFinsupp g ∈ _
  convert SetLike.GradedMul.mul_mem hr (hf g) using 2
  abel

/-- Coefficients of degree `0` preserve the degree. -/
theorem smul_mem_part_zero {r : R} (hr : r ∈ 𝒜 0) {f : LinDiagram R a b} {d : A}
    (hf : f ∈ part 𝒜 deg a b d) : r • f ∈ part 𝒜 deg a b d := by
  simpa using smul_mem_part hr hf

/-- Composition of homogeneous combinations adds degrees. -/
theorem comp_mem_part {f : LinDiagram R a b} {g : LinDiagram R b c} {d e : A}
    (hf : f ∈ part 𝒜 deg a b d) (hg : g ∈ part 𝒜 deg b c e) :
    f ≫ g ∈ part 𝒜 deg a c (d + e) := by
  refine part_induction f hf ?_ ?_ ?_
  · rw [Limits.zero_comp]; exact zero_mem _
  · intro x y hx hy; rw [Preadditive.add_comp]; exact add_mem hx hy
  · intro p r hr
    refine part_induction g hg ?_ ?_ ?_
    · rw [Limits.comp_zero]; exact zero_mem _
    · intro x y hx hy; rw [Preadditive.comp_add]; exact add_mem hx hy
    · intro q s hs
      erw [Free.single_comp_single R (Obj S) p q r s]
      apply single_mem_part'
      rw [Diagram.degree_comp]
      convert SetLike.GradedMul.mul_mem hr hs using 2
      abel

/-- The interchange relation lies in one degree. -/
theorem interchange_mem_part {x : InterchangeData S} (hx : x.Valid) :
    InterchangeData.rel R hx ∈ part 𝒜 deg x.dom x.cod (deg x.g + deg x.h) := by
  refine sub_mem ?_ ?_
  · have := of_mem_part (𝒜 := 𝒜) (deg := deg) (R := R) (InterchangeData.ghDiagram hx)
    rwa [InterchangeData.degree_ghDiagram] at this
  · rw [Int.cast_smul_eq_zsmul]
    refine zsmul_mem ?_ _
    have := of_mem_part (𝒜 := 𝒜) (deg := deg) (R := R) (InterchangeData.hgDiagram hx)
    rwa [InterchangeData.degree_hgDiagram] at this

end GradedMonoid

variable [DecidableEq A] [GradedAlgebra 𝒜]

variable (𝒜 deg) in
/-- The projection of a combination of diagrams onto its degree-`d` part: the coefficient of
`g` is replaced by its component of degree `d - deg g`. -/
def component (d : A) : LinDiagram R a b →+ LinDiagram R a b :=
  Finsupp.liftAddHom fun g =>
    (Finsupp.singleAddHom g).comp (GradedRing.proj 𝒜 (d - Diagram.degree deg g))

theorem component_single (d : A) (g : a ⟶ b) (r : R) :
    component 𝒜 deg d (Finsupp.single g r : LinDiagram R a b) =
      Finsupp.single g (GradedRing.proj 𝒜 (d - Diagram.degree deg g) r) :=
  Finsupp.liftAddHom_apply_single _ _ _

theorem component_mem (d : A) (f : LinDiagram R a b) :
    component 𝒜 deg d f ∈ part 𝒜 deg a b d := by
  induction f using Finsupp.induction_linear with
  | zero => rw [map_zero]; exact zero_mem _
  | add x y hx hy => rw [map_add]; exact add_mem hx hy
  | single g r =>
    rw [component_single]
    exact single_mem_part' (SetLike.coe_mem _)

theorem component_of_mem {f : LinDiagram R a b} {d : A} (hf : f ∈ part 𝒜 deg a b d) :
    component 𝒜 deg d f = f := by
  refine part_induction f hf ?_ ?_ ?_
  · exact map_zero _
  · intro x y hx hy; rw [map_add, hx, hy]
  · intro g r hr
    rw [component_single, GradedRing.proj_apply, DirectSum.decompose_of_mem_same _ hr]

theorem component_of_mem_of_ne {f : LinDiagram R a b} {d e : A}
    (hf : f ∈ part 𝒜 deg a b e) (h : e ≠ d) : component 𝒜 deg d f = 0 := by
  refine part_induction f hf ?_ ?_ ?_
  · exact map_zero _
  · intro x y hx hy; rw [map_add, hx, hy, add_zero]
  · intro g r hr
    rw [component_single, GradedRing.proj_apply,
      DirectSum.decompose_of_mem_ne _ hr (fun h' => h (sub_left_injective h')),
      Finsupp.single_zero]

/-- Every combination of diagrams is a sum of homogeneous ones. -/
theorem mem_iSup_part (f : LinDiagram R a b) : f ∈ ⨆ d, part 𝒜 deg a b d := by
  classical
  induction f using Finsupp.induction_linear with
  | zero => exact zero_mem _
  | add x y hx hy => exact add_mem hx hy
  | single g r =>
    rw [← DirectSum.sum_support_decompose 𝒜 r, Finsupp.single_finsetSum]
    exact sum_mem fun m _ =>
      AddSubgroup.mem_iSup_of_mem _ (single_mem_part (SetLike.coe_mem _))

/-! ## Homogeneous presentations -/

variable (P : Presentation.{w, v} S R)

variable (𝒜 deg) in
/-- A presentation is homogeneous for the coefficient grading `𝒜` and the generator degrees
`deg` if each defining relation lies in one degree. -/
def IsHomogeneous : Prop :=
  ∀ i, ∃ d, P.rel i ∈ part 𝒜 deg (P.dom i) (P.cod i) d

variable {P}

theorem IsHomogeneous.allRel (hP : IsHomogeneous 𝒜 deg P) (k : P.AllRel) :
    ∃ d, k.rel ∈ part 𝒜 deg k.dom k.cod d := by
  cases k with
  | user i => exact hP i
  | interchange x hx => exact ⟨_, interchange_mem_part hx⟩

/-- A homogeneous element of the ideal: all its components lie in the ideal. -/
theorem component_mem_ideal_of_mem {W : LinDiagram R a b} {e : A}
    (hW : W ∈ part 𝒜 deg a b e) (hWI : W ∈ P.ideal a b) (d : A) :
    component 𝒜 deg d W ∈ P.ideal a b := by
  by_cases h : e = d
  · subst h; rwa [component_of_mem hW]
  · rw [component_of_mem_of_ne hW h]; exact zero_mem _

/-- A homogeneous element of the ideal, composed on both sides with arbitrary combinations:
all components lie in the ideal. -/
theorem component_comp_comp_mem_ideal {a' b' : Obj S} {W : LinDiagram R a' b'} {e : A}
    (hW : W ∈ part 𝒜 deg a' b' e) (hWI : W ∈ P.ideal a' b')
    (pre : LinDiagram R a a') (post : LinDiagram R b' b) (d : A) :
    component 𝒜 deg d (pre ≫ W ≫ post) ∈ P.ideal a b := by
  classical
  induction pre using Finsupp.induction_linear with
  | zero => rw [Limits.zero_comp, map_zero]; exact zero_mem _
  | add f₁ f₂ h₁ h₂ => rw [Preadditive.add_comp, map_add]; exact add_mem h₁ h₂
  | single p r =>
    induction post using Finsupp.induction_linear with
    | zero => rw [Limits.comp_zero, Limits.comp_zero, map_zero]; exact zero_mem _
    | add g₁ g₂ h₁ h₂ =>
      rw [Preadditive.comp_add, Preadditive.comp_add, map_add]; exact add_mem h₁ h₂
    | single q s =>
      rw [← DirectSum.sum_support_decompose 𝒜 r, Finsupp.single_finsetSum,
        Preadditive.sum_comp, map_sum]
      refine sum_mem fun m _ => ?_
      rw [← DirectSum.sum_support_decompose 𝒜 s, Finsupp.single_finsetSum,
        Preadditive.comp_sum, Preadditive.comp_sum, map_sum]
      refine sum_mem fun m' _ => ?_
      exact component_mem_ideal_of_mem
        (comp_mem_part (single_mem_part (SetLike.coe_mem _))
          (comp_mem_part hW (single_mem_part (SetLike.coe_mem _))))
        (P.comp_mem_ideal _ (P.mem_ideal_comp hWI _)) d

/-- The ideal is closed under composition with arbitrary scalars, so it is generated as an
additive group by its generators. -/
theorem ideal_le_closure (a b : Obj S) :
    (P.ideal a b).toAddSubgroup ≤ AddSubgroup.closure {f | P.IdealGen f} := by
  intro f hf
  induction hf using Submodule.span_induction with
  | mem x hx => exact AddSubgroup.subset_closure hx
  | zero => exact zero_mem _
  | add x y _ _ hx hy => exact add_mem hx hy
  | smul r x hxs hx =>
    clear hxs
    induction hx using AddSubgroup.closure_induction with
    | mem y hy =>
      obtain ⟨k, u, v, hw, pre, post⟩ := hy
      apply AddSubgroup.subset_closure
      rw [← Linear.smul_comp]
      exact Presentation.IdealGen.intro k u v hw _ post
    | zero => rw [smul_zero]; exact zero_mem _
    | add y z _ _ hy hz => rw [smul_add]; exact add_mem hy hz
    | neg y _ hy => rw [smul_neg]; exact neg_mem hy

/-- For a homogeneous presentation the tensor ideal is homogeneous. -/
theorem component_mem_ideal (hP : IsHomogeneous 𝒜 deg P) {f : LinDiagram R a b}
    (hf : f ∈ P.ideal a b) (d : A) : component 𝒜 deg d f ∈ P.ideal a b := by
  have hf' := ideal_le_closure (P := P) a b hf
  clear hf
  induction hf' using AddSubgroup.closure_induction with
  | mem x hx =>
    obtain ⟨k, u, v, hw, pre, post⟩ := hx
    obtain ⟨e, he⟩ := hP.allRel k
    exact component_comp_comp_mem_ideal (whisker_mem_part he u v hw)
      (P.whisker_rel_mem_ideal k u v hw) pre post d
  | zero => rw [map_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | neg x _ hx => rw [map_neg]; exact neg_mem hx

/-! ## Hom groups of the presented category -/

variable (P 𝒜 deg) in
/-- The degree-`d` part of a Hom group of the presented category. -/
def presentedPart (a b : Obj S) (d : A) : AddSubgroup (P.obj a ⟶ P.obj b) :=
  (part 𝒜 deg a b d).map (P.linMap a b).toAddMonoidHom

omit [DecidableEq A] [GradedAlgebra 𝒜] in
theorem lin_mem_presentedPart {f : LinDiagram R a b} {d : A} (hf : f ∈ part 𝒜 deg a b d) :
    P.lin f ∈ presentedPart 𝒜 deg P a b d :=
  ⟨f, hf, rfl⟩

variable (P 𝒜 deg) in
/-- The homogeneous parts generate each Hom group. -/
theorem iSup_presentedPart (a b : Obj S) : ⨆ d, presentedPart 𝒜 deg P a b d = ⊤ := by
  rw [eq_top_iff]
  rintro x -
  obtain ⟨f, rfl⟩ := P.lin_surjective x
  have := AddSubgroup.mem_map_of_mem (P.linMap a b).toAddMonoidHom
    (mem_iSup_part (𝒜 := 𝒜) (deg := deg) f)
  rwa [AddSubgroup.map_iSup] at this

omit [DecidableEq A] [GradedAlgebra 𝒜] in
theorem mem_presentedPart_iff {x : P.obj a ⟶ P.obj b} {d : A} :
    x ∈ presentedPart 𝒜 deg P a b d ↔ ∃ f ∈ part 𝒜 deg a b d, P.lin f = x :=
  AddSubgroup.mem_map

/-- The projection onto the degree-`d` part of a Hom group of the presented category of a
homogeneous presentation, induced by `component`. -/
def presentedComponent (hP : IsHomogeneous 𝒜 deg P) (d : A) :
    (P.obj a ⟶ P.obj b) →+ (P.obj a ⟶ P.obj b) where
  toFun x := Quot.lift (fun g : LinDiagram R a b => P.lin (component 𝒜 deg d g))
    (fun g₁ g₂ h => by
      have h' : P.homRel g₁ g₂ := by
        rwa [HomRel.compClosure_eq_self] at h
      rw [P.lin_eq_iff, ← map_sub]
      exact component_mem_ideal hP h' d) x
  map_zero' := by
    rw [← P.lin_zero]
    show P.lin _ = _
    rw [map_zero]
  map_add' x y := by
    obtain ⟨x, rfl⟩ := P.lin_surjective x
    obtain ⟨y, rfl⟩ := P.lin_surjective y
    rw [← P.lin_add]
    show P.lin _ = P.lin _ + P.lin _
    rw [map_add, P.lin_add]

@[simp] theorem presentedComponent_lin (hP : IsHomogeneous 𝒜 deg P) (d : A)
    (f : LinDiagram R a b) :
    presentedComponent hP d (P.lin f) = P.lin (component 𝒜 deg d f) := rfl

theorem presentedComponent_mem (hP : IsHomogeneous 𝒜 deg P) (d : A)
    (x : P.obj a ⟶ P.obj b) : presentedComponent hP d x ∈ presentedPart 𝒜 deg P a b d := by
  obtain ⟨x, rfl⟩ := P.lin_surjective x
  rw [presentedComponent_lin]
  exact lin_mem_presentedPart (component_mem d x)

theorem presentedComponent_of_mem (hP : IsHomogeneous 𝒜 deg P) {d : A}
    {x : P.obj a ⟶ P.obj b} (hx : x ∈ presentedPart 𝒜 deg P a b d) :
    presentedComponent hP d x = x := by
  obtain ⟨f, hf, rfl⟩ := mem_presentedPart_iff.mp hx
  rw [presentedComponent_lin, component_of_mem hf]

theorem presentedComponent_of_mem_of_ne (hP : IsHomogeneous 𝒜 deg P) {d e : A}
    {x : P.obj a ⟶ P.obj b} (hx : x ∈ presentedPart 𝒜 deg P a b e) (h : e ≠ d) :
    presentedComponent hP d x = 0 := by
  obtain ⟨f, hf, rfl⟩ := mem_presentedPart_iff.mp hx
  rw [presentedComponent_lin, component_of_mem_of_ne hf h, P.lin_zero]

/-- **Graded Hom groups.** For a coefficient-graded homogeneous presentation, the homogeneous
parts of each Hom group of the presented category are independent; with
`iSup_presentedPart`, each Hom group is their internal direct sum. -/
theorem iSupIndep_presentedPart (hP : IsHomogeneous 𝒜 deg P) (a b : Obj S) :
    iSupIndep (presentedPart 𝒜 deg P a b) := by
  intro d
  rw [AddSubgroup.disjoint_def]
  intro x hx hx'
  have hker : (⨆ (e) (_ : e ≠ d), presentedPart 𝒜 deg P a b e) ≤
      (presentedComponent hP d).ker :=
    iSup₂_le fun e he y hy => presentedComponent_of_mem_of_ne hP hy he
  rw [← presentedComponent_of_mem hP hx]
  exact hker hx'

/-- The homogeneous parts are closed under multiplication by degree-zero scalars. -/
theorem smul_mem_presentedPart {r : R} (hr : r ∈ 𝒜 0) {x : P.obj a ⟶ P.obj b} {d : A}
    (hx : x ∈ presentedPart 𝒜 deg P a b d) : r • x ∈ presentedPart 𝒜 deg P a b d := by
  obtain ⟨f, hf, rfl⟩ := mem_presentedPart_iff.mp hx
  rw [← P.lin_smul]
  refine lin_mem_presentedPart ?_
  intro g
  change r * f.toFinsupp g ∈ _
  simpa using SetLike.GradedMul.mul_mem hr (hf g)

end OddMath.Diagrams.CoefficientGrading
