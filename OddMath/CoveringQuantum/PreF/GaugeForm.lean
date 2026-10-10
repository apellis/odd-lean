import OddMath.CoveringQuantum.PreF.WordGauge
import OddMath.CoveringQuantum.PreF.Form

/-!
# Word gauges and diagonal operators

The diagonal word map conjugates the two skew derivatives when their bicharacters
differ by the ratio of pair phases. It then intertwines the free bilinear forms
and identifies their radicals. No Serre-ideal transport is asserted here.
-/

noncomputable section

namespace OddMath.CoveringQuantum.PreF

variable {k I : Type*} [CommRing k]

/-- A diagonal algebra map acts on a word by the product of the letter scalars. -/
theorem diagTwist_monomial (c : I → k) (w : List I) :
    diagTwist c (monomial k w) = (w.map c).prod • monomial k w := by
  induction w with
  | nil => simp
  | cons i w ih =>
    simp only [monomial_cons, map_mul, diagTwist_θ, ih, List.map_cons,
      List.prod_cons, smul_mul_smul_comm]

variable (f : I → I → kˣ)

/-- Coercion of the row phase is the corresponding scalar product. -/
theorem coe_rowPhase (i : I) (w : List I) :
    (((w.map (f i)).prod : kˣ) : k) = (w.map fun j ↦ (f i j : k)).prod := by
  simpa [List.map_map, Function.comp_def] using map_list_prod (Units.coeHom k) (w.map (f i))

/-- Diagonal word maps commute with all diagonal algebra maps. -/
theorem wordGauge_diagTwist (c : I → k) (x : PreF k I) :
    wordGauge f (diagTwist c x) = diagTwist c (wordGauge f x) := by
  induction x using FreeAlgebra.induction_wordBasis with
  | zero => simp
  | add x y hx hy => simp [map_add, hx, hy]
  | smul a x hx => simp [map_smul, hx]
  | word w =>
    simp only [FreeAlgebra.wordBasis_apply]
    change wordGauge f (diagTwist c (monomial k w)) =
      diagTwist c (wordGauge f (monomial k w))
    rw [diagTwist_monomial, map_smul, wordGauge_monomial, map_smul, diagTwist_monomial]
    simp only [smul_smul, mul_comm]

/-- Left multiplication picks up the row twist of the new letter. -/
theorem wordGauge_theta_mul (i : I) (x : PreF k I) :
    wordGauge f (θ k i * x) =
      θ k i * diagTwist (fun j ↦ (f i j : k)) (wordGauge f x) := by
  induction x using FreeAlgebra.induction_wordBasis with
  | zero => simp
  | add x y hx hy => simp [mul_add, map_add, hx, hy]
  | smul a x hx => simp [map_smul, hx]
  | word w =>
    simp only [FreeAlgebra.wordBasis_apply]
    change wordGauge f (θ k i * monomial k w) =
      θ k i * diagTwist (fun j ↦ (f i j : k)) (wordGauge f (monomial k w))
    rw [← monomial_cons, wordGauge_monomial, wordGauge_monomial, map_smul,
      diagTwist_monomial, smul_smul, wordPhase_cons, Units.val_mul, coe_rowPhase]
    rw [monomial_cons, mul_smul_comm, mul_comm]

/-- Right multiplication picks up the column twist of the new letter. -/
theorem wordGauge_mul_theta (x : PreF k I) (i : I) :
    wordGauge f (x * θ k i) =
      diagTwist (fun j ↦ (f j i : k)) (wordGauge f x) * θ k i := by
  induction x using FreeAlgebra.induction_wordBasis with
  | zero => simp
  | add x y hx hy => simp [add_mul, map_add, hx, hy]
  | smul a x hx => simp [map_smul, hx]
  | word w =>
    simp only [FreeAlgebra.wordBasis_apply]
    change wordGauge f (monomial k w * θ k i) =
      diagTwist (fun j ↦ (f j i : k)) (wordGauge f (monomial k w)) * θ k i
    have hword : monomial k (w ++ [i]) = monomial k w * θ k i := by
      simp [monomial_append]
    have hp : wordPhase f (w ++ [i]) = wordPhase f w * (w.map fun j ↦ f j i).prod := by
      simp [wordPhase_append, wordPhase]
    rw [← hword, wordGauge_monomial, hp, wordGauge_monomial, map_smul,
      diagTwist_monomial, smul_smul, hword, smul_mul_assoc, Units.val_mul]
    congr 2
    simpa [List.map_map, Function.comp_def] using
      map_list_prod (Units.coeHom k) (w.map fun j ↦ f j i)

variable [DecidableEq I] (χ ψ : Bichar k I)
  (hχ : ∀ i j, χ i j = ψ i j * (f i j : k) * ((f j i)⁻¹ : kˣ))

include hχ in
/-- The word gauge conjugates the skew derivative, with the inverse column twist. -/
theorem wordGauge_rDeriv (i : I) (x : PreF k I) :
    wordGauge f (rDeriv χ i x) =
      diagTwist (fun j ↦ (((f j i)⁻¹ : kˣ) : k)) (rDeriv ψ i (wordGauge f x)) := by
  let row (j : I) : I → k := fun l ↦ (f j l : k)
  let col : I → k := fun l ↦ ((f l i)⁻¹ : kˣ)
  have htw (y : PreF k I) :
      diagTwist col (twist ψ i (diagTwist (row i) y)) = twist χ i y := by
    simp only [twist, diagTwist_diagTwist]
    congr 2
    funext j
    dsimp [col, row]
    rw [hχ]
    ring
  induction x using induction_left with
  | algebraMap a => simp [Algebra.algebraMap_eq_smul_one]
  | smul a x hx => simp [map_smul, hx]
  | add x y hx hy => simp [map_add, hx, hy]
  | θ_mul j x hx =>
    rw [rDeriv_θ_mul, map_add, wordGauge_theta_mul, hx, wordGauge_theta_mul,
      rDeriv_θ_mul, rDeriv_diagTwist, map_add, map_mul, diagTwist_θ]
    simp only [map_smul, smul_mul_smul_comm, Units.inv_mul, one_smul]
    rw [diagTwist_comm]
    congr 1
    split_ifs with hij
    · subst j
      rw [twist, wordGauge_diagTwist]
      exact (htw (wordGauge f x)).symm
    · simp

omit [DecidableEq I] in
/-- Word gauges preserve the augmentation. -/
theorem counit_wordGauge (x : PreF k I) : counit (wordGauge f x) = counit x := by
  induction x using induction_left with
  | algebraMap a => simp [Algebra.algebraMap_eq_smul_one]
  | smul a x hx => simp [map_smul, hx]
  | add x y hx hy => simp [map_add, hx, hy]
  | θ_mul i x hx => simp [wordGauge_theta_mul]

/-- Every diagonal algebra map is self-adjoint for the free form. -/
theorem form_diagTwist (nm : I → k) (c : I → k) (x y : PreF k I) :
    form χ nm (diagTwist c x) y = form χ nm x (diagTwist c y) := by
  induction x using induction_right generalizing y with
  | algebraMap a => simp
  | smul a x hx => simp [hx]
  | add x z hx hz => simp [hx, hz]
  | mul_θ x i hx =>
    simp only [map_mul, diagTwist_θ, mul_smul_comm, map_smul, LinearMap.smul_apply,
      form_mul_θ, rDeriv_diagTwist, hx, smul_eq_mul]
    ring

omit [DecidableEq I] in
/-- Opposite unit-valued diagonal twists cancel. -/
theorem diagTwist_units_inverse (c : I → kˣ) (x : PreF k I) :
    diagTwist (fun i ↦ (c i : k)) (diagTwist (fun i ↦ (((c i)⁻¹ : kˣ) : k)) x) = x := by
  have h : (diagTwist (fun i ↦ (c i : k))).comp
      (diagTwist (fun i ↦ (((c i)⁻¹ : kˣ) : k))) = AlgHom.id k (PreF k I) := by
    ext i
    simp [smul_smul]
  exact congrArg (fun g : PreF k I →ₐ[k] PreF k I ↦ g x) h

include hχ in
/-- The two free forms are intertwined by the diagonal word equivalence. -/
theorem form_wordGauge (nm : I → k) (x y : PreF k I) :
    form χ nm (wordGauge f x) y = form ψ nm x (wordGauge f y) := by
  induction x using induction_right generalizing y with
  | algebraMap a => simp [Algebra.algebraMap_eq_smul_one, counit_wordGauge]
  | smul a x hx => simp [hx]
  | add x z hx hz => simp [hx, hz]
  | mul_θ x i hx =>
    rw [wordGauge_mul_theta, form_mul_θ, form_diagTwist, hx, wordGauge_diagTwist,
      wordGauge_rDeriv f χ ψ hχ, diagTwist_units_inverse, form_mul_θ]

include hχ in
/-- The word gauge transports the ordinary radical to the twisted radical. -/
theorem wordGauge_mem_radical_iff (nm : I → k) (x : PreF k I) :
    wordGauge f x ∈ radical χ nm ↔ x ∈ radical ψ nm := by
  rw [mem_radical_iff, mem_radical_iff]
  constructor
  · intro hx y
    obtain ⟨z, rfl⟩ := (wordGauge f).surjective y
    rw [← form_wordGauge f χ ψ hχ]
    exact hx z
  · intro hx y
    rw [form_wordGauge f χ ψ hχ]
    exact hx _

end OddMath.CoveringQuantum.PreF
