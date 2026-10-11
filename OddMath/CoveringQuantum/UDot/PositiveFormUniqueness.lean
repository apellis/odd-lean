import OddMath.CoveringQuantum.UDot.PositiveForm

/-!
# Uniqueness and symmetry of the positive-normalized modified form

`positiveModifiedForm_unique` characterizes the form by endpoint orthogonality,
left rho-adjointness, and normalization on all positive-half pairs. Its proof uses
FE triangular spanning directly, and imposes no root-independence hypothesis.
Symmetry follows by transposing the form. Agreement on positive words is exposed
separately for transporting the characterization to semilinear forms.
`positiveModifiedForm_eq_iff_of_length_separation` reduces normalization to
same-length words under an explicit, theorem-local root-sum separation hypothesis.
-/

noncomputable section
namespace OddMath.CoveringQuantum.UDot.GenericTensor
open Coefficients TensorProduct PreF
variable {I X : Type*} [AddCommGroup X] [DecidableEq I] [DecidableEq X]
variable (D : RootDatum I X)

private def wordModified (positive : Bool) (w : List I) (μ : X) :
    modified D Coefficients.q pi :=
  ⟨halfWord D Coefficients.q pi positive w μ,
    block_le_modified D Coefficients.q pi _ _ (halfWord_mem_block D Coefficients.q pi positive w μ)⟩

private def weightOne (μ : X) : modified D Coefficients.q pi :=
  ⟨one D Coefficients.q pi μ, one_mem_modified D Coefficients.q pi μ⟩

private theorem wordModified_positive (w : List I) (μ : X) :
    wordModified D true w μ = positiveHalf D Coefficients.q pi μ
      (D.toSerreF Coefficients.q pi (monomial Coefficients.Ring w)) := by
  apply Subtype.ext
  exact (halfMap_monomial D Coefficients.q pi true w μ).symm

private theorem linear_ext_FE
    (f g : modified D Coefficients.q pi →ₗ[Coefficients.Ring] Coefficients.Ring)
    (h : ∀ a b μ ν, f (wordModified D false a μ * wordModified D true b ν) =
      g (wordModified D false a μ * wordModified D true b ν)) : f = g := by
  ext x
  have hx : (x : CoveringUDot Coefficients.Ring D Coefficients.q pi) ∈
      triangularSpan D Coefficients.q pi := by
    rw [triangularSpan_eq_modified]
    exact x.property
  have aux : ∀ z ∈ triangularSpan D Coefficients.q pi, ∀ hz : z ∈ modified D Coefficients.q pi,
      f ⟨z, hz⟩ = g ⟨z, hz⟩ := by
    intro z hz
    induction hz using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨a, b, μ, ν, rfl⟩ := hz
      intro hz
      exact h a b μ ν
    | zero => intro hz; exact map_zero f |>.trans (map_zero g).symm
    | add z w hz hw ihz ihw =>
      intro hzw
      have ez : z ∈ modified D Coefficients.q pi := by
        change z ∈ (modified D Coefficients.q pi).toSubmodule
        rw [← triangularSpan_eq_modified]; exact hz
      have ew : w ∈ modified D Coefficients.q pi := by
        change w ∈ (modified D Coefficients.q pi).toSubmodule
        rw [← triangularSpan_eq_modified]; exact hw
      change f (⟨z, ez⟩ + ⟨w, ew⟩) = g (⟨z, ez⟩ + ⟨w, ew⟩)
      simp only [map_add, ihz ez, ihw ew]
    | smul c z hz ih =>
      intro hcz
      have ez : z ∈ modified D Coefficients.q pi := by
        change z ∈ (modified D Coefficients.q pi).toSubmodule
        rw [← triangularSpan_eq_modified]; exact hz
      change f (c • ⟨z, ez⟩) = g (c • ⟨z, ez⟩)
      simp only [map_smul, ih ez]
  exact aux _ hx x.property

/-- Adjoint bilinear forms agreeing on all positive words agree everywhere.
This uses FE triangular spanning and finite local units, without root separation. -/
theorem forms_eq_of_positive_words
    (B C : LinearMap.BilinForm Coefficients.Ring (modified D Coefficients.q pi))
    (hB : ∀ u x y, B (u * x) y = B x (rhoModified D Coefficients.q pi pi_sq u * y))
    (hC : ∀ u x y, C (u * x) y = C x (rhoModified D Coefficients.q pi pi_sq u * y))
    (hpositive : ∀ a b μ ν,
      B (positiveHalf D Coefficients.q pi μ (D.toSerreF Coefficients.q pi (monomial Coefficients.Ring a)))
        (positiveHalf D Coefficients.q pi ν (D.toSerreF Coefficients.q pi (monomial Coefficients.Ring b))) =
      C (positiveHalf D Coefficients.q pi μ (D.toSerreF Coefficients.q pi (monomial Coefficients.Ring a)))
        (positiveHalf D Coefficients.q pi ν (D.toSerreF Coefficients.q pi (monomial Coefficients.Ring b)))) : B = C := by
  have hn : ∀ a b μ ν, B (wordModified D true a μ) (wordModified D true b ν) =
      C (wordModified D true a μ) (wordModified D true b ν) := by
    intro a b μ ν
    simpa only [wordModified_positive] using hpositive a b μ ν
  have ho (η : X) : B (weightOne D η) = C (weightOne D η) := by
    apply linear_ext_FE D
    intro a b μ ν
    obtain ⟨c, hc⟩ := rho_halfWord_unit D Coefficients.q pi pi_sq false a μ
    have hr : rhoModified D Coefficients.q pi pi_sq (wordModified D false a μ) =
        (c : Coefficients.Ring) • wordModified D true a.reverse
          (μ + halfWeight D false (wordWeight a)) := Subtype.ext hc
    have he (F : LinearMap.BilinForm Coefficients.Ring (modified D Coefficients.q pi))
        (hF : ∀ u x y, F (u * x) y = F x (rhoModified D Coefficients.q pi pi_sq u * y)) :
        F (weightOne D η) (wordModified D false a μ * wordModified D true b ν) =
        F ((rhoModified D Coefficients.q pi pi_sq (wordModified D false a μ)) * weightOne D η)
          (wordModified D true b ν) := by
      rw [hF, rhoModified_rhoModified]
    rw [he B hB, he C hC, hr, smul_mul_assoc]
    have hm : wordModified D true a.reverse (μ + halfWeight D false (wordWeight a)) * weightOne D η =
        if μ + halfWeight D false (wordWeight a) = η then
          wordModified D true a.reverse (μ + halfWeight D false (wordWeight a)) else 0 := by
      apply Subtype.ext
      simpa only [wordModified, weightOne, NonUnitalSubalgebra.coe_mul, Subtype.coe_mk,
        apply_ite, NonUnitalSubalgebra.coe_zero] using
        mul_one_of_mem_block D Coefficients.q pi
          (halfWord_mem_block D Coefficients.q pi true a.reverse
            (μ + halfWeight D false (wordWeight a))) η
    rw [hm]
    split_ifs <;> simp [hn]
  ext x y
  obtain ⟨s, _, hs⟩ := exists_localUnit D Coefficients.q pi x.property
  have hx : x * ∑ η ∈ s, weightOne D η = x := by
    apply Subtype.ext
    change (x : CoveringUDot Coefficients.Ring D Coefficients.q pi) *
      (modified D Coefficients.q pi).toSubmodule.subtype (∑ η ∈ s, weightOne D η) = _
    simpa only [map_sum, Submodule.subtype_apply, weightOne] using hs
  calc
    B x y = B (x * ∑ η ∈ s, weightOne D η) y := by rw [hx]
    _ = B (∑ η ∈ s, weightOne D η) (rhoModified D Coefficients.q pi pi_sq x * y) := hB _ _ _
    _ = C (∑ η ∈ s, weightOne D η) (rhoModified D Coefficients.q pi pi_sq x * y) := by
      simp only [map_sum, LinearMap.sum_apply, ho]
    _ = C (x * ∑ η ∈ s, weightOne D η) y := (hC _ _ _).symm
    _ = C x y := by rw [hx]

variable [Finite I]

/-- Endpoint orthogonality, adjointness for all actual modified elements, and
normalization on all positive-half pairs uniquely determine the constructed form.
No homogeneity or independence of the simple roots is assumed. -/
theorem positiveModifiedForm_unique (hD : D.toSuperCartanDatum.BarConsistent)
    (B : LinearMap.BilinForm Coefficients.Ring (modified D Coefficients.q pi))
    (horth : ∀ μ ν μ' ν' (x y : modified D Coefficients.q pi),
      (x : CoveringUDot Coefficients.Ring D Coefficients.q pi) ∈ block D Coefficients.q pi μ ν →
      (y : CoveringUDot Coefficients.Ring D Coefficients.q pi) ∈ block D Coefficients.q pi μ' ν' →
      μ ≠ μ' ∨ ν ≠ ν' → B x y = 0)
    (hadj : ∀ u x y, B (u * x) y = B x (rhoModified D Coefficients.q pi pi_sq u * y))
    (hpositive : ∀ μ (x y : D.serreF Coefficients.q pi),
      B (positiveHalf D Coefficients.q pi μ x) (positiveHalf D Coefficients.q pi μ y) =
        D.serreForm Coefficients.q pi pi_sq x y) : B = positiveModifiedForm D hD := by
  apply forms_eq_of_positive_words D B (positiveModifiedForm D hD) hadj (positiveModifiedForm_adjoint D hD)
  intro a b μ ν
  simp only [← wordModified_positive]
  by_cases h : μ = ν
  · subst ν
    rw [wordModified_positive, wordModified_positive, hpositive, positiveModifiedForm_positiveHalf]
  · rw [horth _ _ _ _ _ _ (halfWord_mem_block D Coefficients.q pi true a μ)
        (halfWord_mem_block D Coefficients.q pi true b ν) (Or.inr h),
      positiveModifiedForm_orthogonal D hD _ _ _ _ _ _ (halfWord_mem_block D Coefficients.q pi true a μ)
        (halfWord_mem_block D Coefficients.q pi true b ν) (Or.inr h)]

/-- Symmetry follows by applying uniqueness to the transposed form. -/
theorem positiveModifiedForm_comm (hD : D.toSuperCartanDatum.BarConsistent)
    (x y : modified D Coefficients.q pi) : positiveModifiedForm D hD x y = positiveModifiedForm D hD y x := by
  have he : (positiveModifiedForm D hD).flip = positiveModifiedForm D hD := by
    apply positiveModifiedForm_unique D hD
    · intro μ ν μ' ν' a b ha hb hn
      exact positiveModifiedForm_orthogonal D hD μ' ν' μ ν b a hb ha
        (hn.imp Ne.symm Ne.symm)
    · intro u a b
      change positiveModifiedForm D hD b (u * a) =
        positiveModifiedForm D hD (rhoModified D Coefficients.q pi pi_sq u * b) a
      rw [positiveModifiedForm_adjoint, rhoModified_rhoModified]
    · intro μ a b
      change positiveModifiedForm D hD (positiveHalf D Coefficients.q pi μ b)
        (positiveHalf D Coefficients.q pi μ a) = _
      rw [positiveModifiedForm_positiveHalf, SuperCartanDatum.serreForm_comm]
  exact (LinearMap.congr_fun (LinearMap.congr_fun he x) y).symm

omit [DecidableEq I] [DecidableEq X] [Finite I] in
private theorem halfWeight_wordWeight_positive (a : List I) :
    halfWeight D true (wordWeight a) = (a.map D.α).sum := by
  induction a with
  | nil => simp
  | cons i a ih => simp [wordWeight_cons, halfWeight_add, ih, halfRoot]

/-- Same-length positive-word normalization suffices when equality of root sums
forces equality of word lengths. The separation hypothesis is local to this
shorter characterization; all-half uniqueness and symmetry do not require it.
Unequal lengths give distinct left endpoints, so endpoint orthogonality supplies
both zero values without any root-independence assumption on the datum itself. -/
theorem positiveModifiedForm_unique_of_same_length (hD : D.toSuperCartanDatum.BarConsistent)
    (hlength : ∀ a b : List I, (a.map D.α).sum = (b.map D.α).sum → a.length = b.length)
    (B : LinearMap.BilinForm Coefficients.Ring (modified D Coefficients.q pi))
    (horth : ∀ μ ν μ' ν' (x y : modified D Coefficients.q pi),
      (x : CoveringUDot Coefficients.Ring D Coefficients.q pi) ∈ block D Coefficients.q pi μ ν →
      (y : CoveringUDot Coefficients.Ring D Coefficients.q pi) ∈ block D Coefficients.q pi μ' ν' →
      μ ≠ μ' ∨ ν ≠ ν' → B x y = 0)
    (hadj : ∀ u x y, B (u * x) y = B x (rhoModified D Coefficients.q pi pi_sq u * y))
    (hwords : ∀ μ (a b : List I), a.length = b.length →
      B (positiveHalf D Coefficients.q pi μ (D.toSerreF Coefficients.q pi (monomial Coefficients.Ring a)))
        (positiveHalf D Coefficients.q pi μ (D.toSerreF Coefficients.q pi (monomial Coefficients.Ring b))) =
      D.serreForm Coefficients.q pi pi_sq
        (D.toSerreF Coefficients.q pi (monomial Coefficients.Ring a))
        (D.toSerreF Coefficients.q pi (monomial Coefficients.Ring b))) :
    B = positiveModifiedForm D hD := by
  apply forms_eq_of_positive_words D B (positiveModifiedForm D hD) hadj
    (positiveModifiedForm_adjoint D hD)
  intro a b μ ν
  simp only [← wordModified_positive]
  by_cases hμ : μ = ν
  · subst ν
    by_cases hab : a.length = b.length
    · rw [wordModified_positive, wordModified_positive, hwords μ a b hab,
        positiveModifiedForm_positiveHalf]
    · have hleft : μ + halfWeight D true (wordWeight a) ≠
          μ + halfWeight D true (wordWeight b) := by
        intro he
        apply hab
        apply hlength a b
        simpa only [halfWeight_wordWeight_positive] using add_left_cancel he
      rw [horth _ _ _ _ _ _ (halfWord_mem_block D Coefficients.q pi true a μ)
          (halfWord_mem_block D Coefficients.q pi true b μ) (Or.inl hleft),
        positiveModifiedForm_orthogonal D hD _ _ _ _ _ _
          (halfWord_mem_block D Coefficients.q pi true a μ)
          (halfWord_mem_block D Coefficients.q pi true b μ) (Or.inl hleft)]
  · rw [horth _ _ _ _ _ _ (halfWord_mem_block D Coefficients.q pi true a μ)
        (halfWord_mem_block D Coefficients.q pi true b ν) (Or.inr hμ),
      positiveModifiedForm_orthogonal D hD _ _ _ _ _ _
        (halfWord_mem_block D Coefficients.q pi true a μ)
        (halfWord_mem_block D Coefficients.q pi true b ν) (Or.inr hμ)]

/-- The three-axiom positive-word characterization, with only same-length word
pairs in the normalization clause. Root-sum length separation is an explicit
hypothesis rather than a global assumption or a root-independence assertion. -/
theorem positiveModifiedForm_eq_iff_of_length_separation
    (hD : D.toSuperCartanDatum.BarConsistent)
    (hlength : ∀ a b : List I, (a.map D.α).sum = (b.map D.α).sum → a.length = b.length)
    (B : LinearMap.BilinForm Coefficients.Ring (modified D Coefficients.q pi)) :
    B = positiveModifiedForm D hD ↔
      (∀ μ ν μ' ν' (x y : modified D Coefficients.q pi),
        (x : CoveringUDot Coefficients.Ring D Coefficients.q pi) ∈ block D Coefficients.q pi μ ν →
        (y : CoveringUDot Coefficients.Ring D Coefficients.q pi) ∈ block D Coefficients.q pi μ' ν' →
        μ ≠ μ' ∨ ν ≠ ν' → B x y = 0) ∧
      (∀ u x y, B (u * x) y = B x (rhoModified D Coefficients.q pi pi_sq u * y)) ∧
      (∀ μ (a b : List I), a.length = b.length →
        B (positiveHalf D Coefficients.q pi μ (D.toSerreF Coefficients.q pi (monomial Coefficients.Ring a)))
          (positiveHalf D Coefficients.q pi μ (D.toSerreF Coefficients.q pi (monomial Coefficients.Ring b))) =
        D.serreForm Coefficients.q pi pi_sq
          (D.toSerreF Coefficients.q pi (monomial Coefficients.Ring a))
          (D.toSerreF Coefficients.q pi (monomial Coefficients.Ring b))) := by
  constructor
  · rintro rfl
    refine ⟨positiveModifiedForm_orthogonal D hD, positiveModifiedForm_adjoint D hD, ?_⟩
    intro μ a b _
    exact positiveModifiedForm_positiveHalf D hD μ _ _
  · rintro ⟨horth, hadj, hwords⟩
    exact positiveModifiedForm_unique_of_same_length D hD hlength B horth hadj hwords

end OddMath.CoveringQuantum.UDot.GenericTensor
