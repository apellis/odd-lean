import StringDiagrams.Super.SKarSuperalgebraK0
import Mathlib.LinearAlgebra.FreeModule.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import StringDiagrams.Super.GSKar
import Mathlib.Algebra.MonoidAlgebra.Grading

/-!
# The degree-zero Clifford superalgebra

The opening of Brundan–Ellis, *Super Kac–Moody 2-categories*, arXiv:1701.04133v2,
§11 requires care with parity-fixed projectives. Here the Clifford algebra is the group
algebra of `ZMod 2`: its odd basis element squares to one. We use the supercategory and
projective-category constructions of `StringDiagrams`, not a prescribed coefficient module.

The projective comparison `projectiveEquivalence` concerns right supermodules without an
integer grading. The graded result uses `GSKar` itself and its existing `K₀.moduleLaurent`.
Over every field, `gradedRegular_class_ne_zero` detects the regular class by the dimension
of a representable Hom space. The natural isomorphism `gradedProjectiveParityNatIso` makes
parity act trivially on the entire split Grothendieck group. Consequently
`gradedK0_not_free` disproves the unconditional Laurent freeness assertion in the first
bullet of §11: a nonzero free module is faithful, whereas `π - 1` annihilates this group.
The integer grading is concentrated in degree zero and has finite-dimensional pieces
(`laurentian`). In particular, the example applies over `ℚ`, in characteristic different
from two. No classification of all indecomposable projectives is needed.
-/

noncomputable section

namespace OddMath.SKM.CliffordK0

open CategoryTheory CategoryTheory.Idempotents StringDiagrams Supercategory

variable (k : Type) [CommRing k]

/-- The Clifford algebra on one odd generator with square one. -/
abbrev Algebra := AddMonoidAlgebra k (ZMod 2)

/-- The parity grading by the group basis. -/
abbrev parity : ZMod 2 → Submodule k (Algebra k) := AddMonoidAlgebra.grade k

/-- The odd Clifford generator. -/
def c : Algebra k := AddMonoidAlgebra.single 1 1

theorem c_mem : c k ∈ parity k 1 := AddMonoidAlgebra.single_mem_grade _ _

@[simp] theorem c_mul_c : c k * c k = 1 := by
  simp [c, AddMonoidAlgebra.single_mul_single, show (1 : ZMod 2) + 1 = 0 from rfl,
    AddMonoidAlgebra.one_def]

/-- The algebra has the two group-basis coordinates, rather than an imposed parity action. -/
theorem expansion (a : Algebra k) :
    a = AddMonoidAlgebra.single 0 (a.coeff 0) +
      AddMonoidAlgebra.single 1 (a.coeff 1) := by
  ext p
  rcases Supercategory.parity_eq_zero_or_one p with rfl | rfl <;> simp

/-- The odd unit is nonzero over a nontrivial coefficient ring. -/
theorem c_ne_zero [Nontrivial k] : c k ≠ 0 := by
  intro h
  have := congrArg (fun a : Algebra k => a.coeff 1) h
  simp [c] at this

/-- The even and odd basis elements are distinct. -/
theorem one_ne_c [Nontrivial k] : (1 : Algebra k) ≠ c k := by
  intro h
  have := congrArg (fun a : Algebra k => a.coeff 0) h
  simp [c, AddMonoidAlgebra.one_def] at this

/-- The supercategory with this endomorphism algebra. -/
abbrev Cat := SuperalgebraCat (parity k)

/-- Its parity envelope, with even morphisms. -/
abbrev ParityCat := SKarAlg.D (parity k)

/-- The additive idempotent completion. -/
abbrev Projectives := SKar k (Cat k)

/-- Comparison with finitely generated projective right Clifford supermodules. -/
def projectiveEquivalence : Projectives k ≌ SKarAlg.FGProj (parity k) :=
  (SKarAlg.toFGProj (parity k)).asEquivalence

/-- The comparison uses the split Grothendieck group of projective supermodules. -/
def projectiveK0Equiv : K₀ (Projectives k) ≃+ K₀ (SKarAlg.FGProj (parity k)) :=
  SKarAlg.K₀Equiv (parity k)

/-- The free rank-one object and its parity shifts. -/
def line (p : ZMod 2) : ParityCat k := ⟨⟨p, SuperalgebraCat.star (parity k)⟩⟩

/-- Multiplication by the odd unit identifies the two parity shifts. -/
def lineParityIso (p : ZMod 2) : line k (p + 1) ≅ line k p where
  hom := SKarAlg.ofElem (by
    change c k ∈ parity k (p + 1 + p)
    convert c_mem k using 1; congr 1;
      rcases Supercategory.parity_eq_zero_or_one p with rfl | rfl <;> decide)
  inv := SKarAlg.ofElem (by
    change c k ∈ parity k (p + (p + 1))
    convert c_mem k using 1; congr 1;
      rcases Supercategory.parity_eq_zero_or_one p with rfl | rfl <;> decide)
  hom_inv_id := SKarAlg.hom_ext (by
    simp only [SKarAlg.elem_comp, SKarAlg.elem_ofElem, SKarAlg.elem_id, c_mul_c])
  inv_hom_id := SKarAlg.hom_ext (by
    simp only [SKarAlg.elem_comp, SKarAlg.elem_ofElem, SKarAlg.elem_id, c_mul_c])

/-- The Clifford unit gives a parity isomorphism on every object of the parity envelope. -/
def parityIso (X : ParityCat k) : (PiCategory.pi (R := k)).obj X ≅ X where
  hom := SKarAlg.ofElem (by
    change c k ∈ parity k (X.obj.par + 1 + X.obj.par)
    simpa only [add_right_comm, zmod2_add_self, zero_add] using c_mem k)
  inv := SKarAlg.ofElem (by
    change c k ∈ parity k (X.obj.par + (X.obj.par + 1))
    simpa only [← add_assoc, zmod2_add_self, zero_add] using c_mem k)
  hom_inv_id := SKarAlg.hom_ext (by
    simp only [SKarAlg.elem_comp, SKarAlg.elem_ofElem, SKarAlg.elem_id, c_mul_c])
  inv_hom_id := SKarAlg.hom_ext (by
    simp only [SKarAlg.elem_comp, SKarAlg.elem_ofElem, SKarAlg.elem_id, c_mul_c])

/-- On even envelope morphisms, parity does not change the underlying algebra element. -/
theorem elem_pi_map {X Y : ParityCat k} (f : X ⟶ Y) :
    SKarAlg.elem ((PiCategory.pi (R := k)).map f) = SKarAlg.elem f := by
  change Envelope.toHom ((PiSupercategory.pi (R := k)).map f.1) = Envelope.toHom f.1
  rw [Envelope.toHom_pi_map, Supercategory.twist_of_mem 1 (SKarAlg.elem_mem f)]
  simp only [one_mul, sign_smul_sign_smul]

/-- Parity is naturally isomorphic to the identity on the even parity envelope. -/
def parityNatIso : PiCategory.pi (R := k) (C := ParityCat k) ≅ 𝟭 _ :=
  NatIso.ofComponents (parityIso k) (fun f => by
    apply SKarAlg.hom_ext
    simp only [SKarAlg.elem_comp, Functor.id_map, elem_pi_map]
    change c k * SKarAlg.elem f = SKarAlg.elem f * c k
    exact mul_comm _ _)

/-- Parity is naturally isomorphic to the identity on all ungraded Clifford projectives. -/
def projectiveParityNatIso : PiCategory.pi (R := k) (C := Projectives k) ≅ 𝟭 _ :=
  StringDiagrams.Karoubi.mapIsoId
    (StringDiagrams.Mat_.mapMatIso (parityNatIso k))

/-- Parity acts trivially on the entire ungraded split Grothendieck group. -/
theorem piInvolution_eq_id :
    K₀.piInvolution k (Projectives k) = AddMonoidHom.id (K₀ (Projectives k)) := by
  rw [K₀.piInvolution, K₀.map_eq_of_iso (projectiveParityNatIso k), K₀.map_id]

/-- The regular projective, placed in parity `p`. -/
def regular (p : ZMod 2) : Projectives k := (SKar.of k (Cat k)).obj (line k p)

theorem regular_parity_class (p : ZMod 2) :
    K₀.mk (regular k (p + 1)) = K₀.mk (regular k p) :=
  K₀.mk_eq_mk_of_iso ((SKar.of k (Cat k)).mapIso (lineParityIso k p))

/-- The same equality in the projective-supermodule Grothendieck group. -/
theorem projective_regular_parity_class (p : ZMod 2) :
    K₀.mk ((SKarAlg.toFGProj (parity k)).obj (regular k (p + 1))) =
      K₀.mk ((SKarAlg.toFGProj (parity k)).obj (regular k p)) := by
  simpa only [projectiveK0Equiv, SKarAlg.K₀Equiv_mk] using
    congrArg (projectiveK0Equiv k) (regular_parity_class k p)

/-- The integer grading is concentrated in degree zero. -/
abbrev degree : ℤ → Submodule k (Algebra k) :=
  AddMonoidAlgebra.gradeBy k (0 : ZMod 2 →+ ℤ)

theorem eq_zero_of_degree_ne_zero {n : ℤ} (hn : n ≠ 0) {a : Algebra k}
    (ha : a ∈ degree k n) : a = 0 := by
  ext i
  by_contra hi
  exact hn (ha i (Finsupp.mem_support_iff.mpr hi)).symm

instance : GradedSupercategory k (Cat k) where
  degree _ _ := degree k
  isInternal_degree _ _ := AddMonoidAlgebra.gradeBy.isInternal _
  proj_mem_degree {X Y n f} p hf := by
    by_cases hn : n = 0
    · subst n
      intro i hi
      rfl
    · have hz : f = 0 := eq_zero_of_degree_ne_zero k hn hf
      subst f
      simpa only [map_zero] using (Submodule.zero_mem (degree k n))
  id_mem_degree _ := AddMonoidAlgebra.single_mem_gradeBy _ _ _
  comp_mem_degree {X Y Z m n f g} hf hg := by
    change SuperalgebraCat.toElem g * SuperalgebraCat.toElem f ∈ degree k (m + n)
    by_cases hm : m = 0
    · by_cases hn : n = 0
      · subst m; subst n; intro i hi; rfl
      · have hz : SuperalgebraCat.toElem g = 0 := eq_zero_of_degree_ne_zero k hn hg
        rw [hz, zero_mul]
        exact Submodule.zero_mem _
    · have hz : SuperalgebraCat.toElem f = 0 := eq_zero_of_degree_ne_zero k hm hf
      rw [hz, mul_zero]
      exact Submodule.zero_mem _

/-- The graded super Karoubi envelope of the degree-zero Clifford algebra. -/
abbrev GradedProjectives := GSKar k (Cat k)

/-- The existing Laurent action induced by integer and parity shifts. -/
@[instance_reducible]
def laurentModule : Module (LaurentPolynomial Zπ) (K₀ (GradedProjectives k)) :=
  K₀.moduleLaurent k (GradedProjectives k)

open GradedSupercategory

/-- Even degree-zero morphisms between shifted Clifford lines. -/
abbrev GradedLines := GUnderlying k (QPiEnvelope k (Cat k))

/-- The Clifford element underlying an even degree-zero map. -/
def gradedElem {X Y : GradedLines k} (f : X ⟶ Y) : Algebra k :=
  SuperalgebraCat.toElem (QEnvelope.toHom (Envelope.toHom f.1.1))

theorem gradedElem_injective {X Y : GradedLines k} :
    Function.Injective (@gradedElem k _ X Y) := by
  intro f g h
  exact Subtype.ext (Subtype.ext h)

theorem gradedElem_mem {X Y : GradedLines k} (f : X ⟶ Y) :
    gradedElem k f ∈ parity k (X.obj.obj.par + Y.obj.obj.par) := by
  have h := Envelope.mem_parity_iff.mp (DegreeZero.mem_parity_iff.mp f.2)
  change gradedElem k f ∈ parity k (0 + (X.obj.obj.par + Y.obj.obj.par)) at h
  simpa only [zero_add] using h

/-- The odd Clifford unit gives an even degree-zero parity isomorphism. -/
def gradedLineParityIso (X : GradedLines k) :
    (PiCategory.pi (R := k)).obj X ≅ X where
  hom := ⟨⟨Envelope.ofHom (QEnvelope.ofHom (SuperalgebraCat.ofElem (c k))), by
    change c k ∈ degree k (0 + (X.obj.obj.obj.shift - X.obj.obj.obj.shift))
    simp only [sub_self, add_zero]
    intro i hi; rfl⟩, by
    apply DegreeZero.mem_parity_iff.mpr
    apply Envelope.mem_parity_iff.mpr
    change c k ∈ parity k (0 + ((X.obj.obj.par + 1) + X.obj.obj.par))
    simpa only [zero_add, add_right_comm, zmod2_add_self, zero_add] using c_mem k⟩
  inv := ⟨⟨Envelope.ofHom (QEnvelope.ofHom (SuperalgebraCat.ofElem (c k))), by
    change c k ∈ degree k (0 + (X.obj.obj.obj.shift - X.obj.obj.obj.shift))
    simp only [sub_self, add_zero]
    intro i hi; rfl⟩, by
    apply DegreeZero.mem_parity_iff.mpr
    apply Envelope.mem_parity_iff.mpr
    change c k ∈ parity k (0 + (X.obj.obj.par + (X.obj.obj.par + 1)))
    simpa only [zero_add, ← add_assoc, zmod2_add_self, zero_add] using c_mem k⟩
  hom_inv_id := gradedElem_injective k (c_mul_c k)
  inv_hom_id := gradedElem_injective k (c_mul_c k)

theorem gradedElem_pi_map {X Y : GradedLines k} (f : X ⟶ Y) :
    gradedElem k ((PiCategory.pi (R := k)).map f) = gradedElem k f := by
  change QEnvelope.toHom (Envelope.toHom ((PiSupercategory.pi (R := k)).map f.1.1)) = _
  rw [Envelope.toHom_pi_map]
  have h : QEnvelope.toHom (Supercategory.twist k 1 (Envelope.toHom f.1.1)) =
      Supercategory.twist k 1 (gradedElem k f) := by
    rw [Supercategory.twist_apply, Supercategory.twist_apply]
    simp only [QEnvelope.toHom_add, QEnvelope.toHom_smul, QEnvelope.toHom_proj]
    rfl
  rw [QEnvelope.toHom_smul, h, Supercategory.twist_of_mem 1 (gradedElem_mem k f)]
  simp only [one_mul, sign_smul_sign_smul]

/-- Parity is the identity up to natural isomorphism on the graded line category. -/
def gradedLineParityNatIso : PiCategory.pi (R := k) (C := GradedLines k) ≅ 𝟭 _ :=
  NatIso.ofComponents (gradedLineParityIso k) (fun f => by
    apply gradedElem_injective k
    change c k * gradedElem k ((PiCategory.pi (R := k)).map f) = gradedElem k f * c k
    rw [gradedElem_pi_map, mul_comm])

/-- Parity is naturally isomorphic to the identity on every graded Clifford projective. -/
def gradedProjectiveParityNatIso :
    PiCategory.pi (R := k) (C := GradedProjectives k) ≅ 𝟭 _ :=
  StringDiagrams.Karoubi.mapIsoId
    (StringDiagrams.Mat_.mapMatIso (gradedLineParityNatIso k))

/-- Parity acts trivially on the entire graded split Grothendieck group. -/
theorem graded_piInvolution_eq_id :
    K₀.piInvolution k (GradedProjectives k) = AddMonoidHom.id (K₀ (GradedProjectives k)) := by
  rw [K₀.piInvolution, K₀.map_eq_of_iso (gradedProjectiveParityNatIso k), K₀.map_id]

/-- The regular graded projective in degree zero. -/
def gradedRegular : GradedProjectives k :=
  (toKaroubi _).obj ((Mat_.embedding _).obj
    (⟨⟨⟨0, ⟨0, SuperalgebraCat.star (parity k)⟩⟩⟩⟩ : GradedLines k))

/-- The underlying matrix of a map of graded projectives. -/
def homMatrix (P Q : GradedProjectives k) :
    (P ⟶ Q) →ₗ[k] (P.X.ι → Q.X.ι → Algebra k) where
  toFun f i j := gradedElem k (f.f i j)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem homMatrix_injective (P Q : GradedProjectives k) :
    Function.Injective (homMatrix k P Q) := by
  intro f g h
  apply CategoryTheory.Idempotents.Karoubi.hom_ext
  apply CategoryTheory.Mat_.hom_ext
  intro i j
  exact gradedElem_injective k (congrFun (congrFun h i) j)

section Field

variable (K : Type) [Field K]

/-- The Clifford grading has finite-dimensional pieces and vanishes in negative degrees. -/
theorem laurentian : (∀ n : ℤ, FiniteDimensional K (degree K n)) ∧
    ∀ n : ℤ, n < 0 → degree K n = ⊥ := by
  refine ⟨fun _ => inferInstance, fun n hn => ?_⟩
  apply le_antisymm _ bot_le
  intro a ha
  exact (Submodule.mem_bot K).mpr (eq_zero_of_degree_ne_zero K (ne_of_lt hn) ha)

instance (P Q : GradedProjectives K) : FiniteDimensional K (P ⟶ Q) := by
  apply FiniteDimensional.of_injective (homMatrix K P Q) (homMatrix_injective K P Q)

open CategoryTheory.Limits

/-- The linear biproduct decomposition of representable morphisms. -/
def homBiprodEquiv (P X Y : GradedProjectives K) :
    (P ⟶ X ⊞ Y) ≃ₗ[K] (P ⟶ X) × (P ⟶ Y) where
  toFun f := (f ≫ biprod.fst, f ≫ biprod.snd)
  invFun f := biprod.lift f.1 f.2
  map_add' _ _ := by simp
  map_smul' _ _ := by simp
  left_inv f := by apply biprod.hom_ext <;> simp
  right_inv f := by simp

/-- Dimension of maps from the regular projective, as a split Grothendieck invariant. -/
def gradedDimension : K₀ (GradedProjectives K) →+ ℤ :=
  K₀.lift (fun X => (Module.finrank K (gradedRegular K ⟶ X) : ℤ))
    (fun _ _ e => by rw [(Linear.homCongr K (Iso.refl _) e).finrank_eq])
    (fun X Y => by
      rw [(homBiprodEquiv K _ X Y).finrank_eq, Module.finrank_prod, Nat.cast_add])

theorem gradedRegular_id_ne_zero : (𝟙 (gradedRegular K)) ≠ 0 := by
  intro h
  have he := congrArg (fun f => homMatrix K _ _ f PUnit.unit PUnit.unit) h
  simp only [homMatrix, LinearMap.coe_mk, AddHom.coe_mk, Karoubi.id_f,
    gradedRegular, toKaroubi_obj_p, Mat_.id_apply_self] at he
  change (1 : Algebra K) = 0 at he
  exact one_ne_zero he

/-- The regular Clifford projective has a nonzero split Grothendieck class. -/
theorem gradedRegular_class_ne_zero : K₀.mk (gradedRegular K) ≠ 0 := by
  have : Nontrivial (gradedRegular K ⟶ gradedRegular K) :=
    ⟨⟨𝟙 _, 0, gradedRegular_id_ne_zero K⟩⟩
  intro h
  have hd := congrArg (gradedDimension K) h
  rw [gradedDimension, K₀.lift_mk, map_zero] at hd
  have hp := Module.finrank_pos (R := K) (M := gradedRegular K ⟶ gradedRegular K)
  exact (ne_of_gt hp) (Int.ofNat_eq_zero.mp hd)

instance : Nontrivial (K₀ (GradedProjectives K)) :=
  ⟨⟨K₀.mk (gradedRegular K), 0, gradedRegular_class_ne_zero K⟩⟩

/-- The Laurent parity scalar acts trivially on every class, not just the regular class. -/
theorem C_pi_smul (x : K₀ (GradedProjectives K)) :
    letI := laurentModule K
    LaurentPolynomial.C Zπ.π • x = x := by
  change K₀.laurentEnd K (GradedProjectives K) (LaurentPolynomial.C Zπ.π) x = x
  rw [K₀.laurentEnd_C, Zπ.toEnd_π, graded_piInvolution_eq_id]
  rfl

/-- The parity scalar in the Laurent coefficient ring is not one. -/
theorem C_pi_ne_one : (LaurentPolynomial.C Zπ.π : LaurentPolynomial Zπ) ≠ 1 := by
  intro h
  have he := congrArg (fun p : LaurentPolynomial Zπ => p.coeff 0) h
  have hp : Zπ.π = 1 := by
    simpa only [← LaurentPolynomial.single_eq_C, AddMonoidAlgebra.coeff_single,
      Finsupp.single_eq_same, AddMonoidAlgebra.one_def] using he
  have hm := congrArg (Zπ.eval (-1) (by norm_num)) hp
  rw [Zπ.eval_π, map_one] at hm
  norm_num at hm

/-- The graded Clifford split Grothendieck group is not free over `Zπ[q,q⁻¹]`.
The proof uses nonvanishing and the trivial parity action on the entire group. -/
theorem gradedK0_not_free :
    letI := laurentModule K
    ¬ Module.Free (LaurentPolynomial Zπ) (K₀ (GradedProjectives K)) := by
  let := laurentModule K
  intro h
  let := h
  apply C_pi_ne_one
  apply eq_of_smul_eq_smul (α := K₀ (GradedProjectives K))
  intro x
  rw [one_smul, C_pi_smul K]

end Field

end OddMath.SKM.CliffordK0
