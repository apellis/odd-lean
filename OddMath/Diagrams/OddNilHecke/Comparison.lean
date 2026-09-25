import OddMath.Diagrams.OddNilHecke.Action
import OddMath.Frontier.NilHeckeBasis
import StringDiagrams.Generation

/-!
# The odd nilHecke ring is the endomorphism ring of `n + 2` strands

Source: A. P. Ellis, M. Khovanov, A. D. Lauda, *The odd nilHecke algebra and its
diagrammatics*, arXiv:1111.1320v1, §2.2: the odd nilHecke algebra `ONH_{n+2}` is presented
by generators and relations in Proposition 2.1, (2.7)–(2.10), and is described
diagrammatically by odd dots and crossings on `n + 2` strands, with the anticommutation
relations read as the (super) interchange law.

This file compares odd-lean's presented ring `OddMath.Frontier.NilHeckeAction.Presented n`
(the free `ℤ`-algebra on dots and crossings modulo exactly the seven relator families of
Prop. 2.1) with the endomorphism ring of the object of `n + 2` strands in the presented
diagrammatic category `ONH ℤ` of `OddMath.Diagrams.OddNilHecke.Basic`, in which only the
square, braid and two mixed relations are imposed and the anticommutations come from the
Koszul sign of the interchange law.

## Main results

* `toDiagrams n : Presented n →+* End (strands (n + 2))`, sending `dot n j ↦ x (n+2) j` and
  `crossing n i ↦ ψ (n+2) i`.
* `realize_toDiagrams`: composing with the polynomial representation of the diagrammatic
  category (`realize`, from `polyFunctor`) recovers odd-lean's action `action n` on
  `SkewPolynomial (n + 2)`.
* `toDiagrams_injective` (from `NilHeckeBasis.action_injective`) and `toDiagrams_surjective`
  (every endomorphism of `n + 2` strands is a combination of composites of dot and crossing
  layers, `StringDiagrams.Presentation.hom_induction_layers`).
* `presentedEquivEnd n : Presented n ≃+* End (strands (n + 2))`, the headline ring
  isomorphism, and `realize_injective`: the polynomial representation of the diagrammatic
  category is faithful on `n + 2` strands.

The cases of zero and one strand are not covered (odd-lean's `Presented n` has rank `n + 2`).
-/

noncomputable section

namespace OddMath.Diagrams.OddNilHecke

open CategoryTheory StringDiagrams
open OddMath.Frontier NilHeckeAction

/-! ## The comparison homomorphism -/

/-- Dots and crossings of the free algebra go to the corresponding diagrams on `n + 2`
strands. -/
def toDiagramsFree (n : ℕ) : NilHeckeAction.Free n →ₐ[ℤ] End ((pres ℤ).obj (strands (n + 2))) :=
  FreeAlgebra.lift ℤ (Sum.elim (fun j => x ℤ (n + 2) j) (fun i => ψ ℤ (n + 2) i))

@[simp] theorem toDiagramsFree_dot (n : ℕ) (j : Fin (n + 2)) :
    toDiagramsFree n (dotFree n j) = x ℤ (n + 2) j := by
  simp [toDiagramsFree, dotFree]

@[simp] theorem toDiagramsFree_crossing (n : ℕ) (i : Fin (n + 1)) :
    toDiagramsFree n (crossingFree n i) = ψ ℤ (n + 2) i := by
  simp [toDiagramsFree, crossingFree]

/-- Every relator of EKL Prop. 2.1 holds between the diagrams. -/
theorem toDiagramsFree_relator (n : ℕ) (w : NilHeckeAction.Free n) (hw : Relator n w) :
    toDiagramsFree n w = 0 := by
  cases hw with
  | square i =>
    simp only [map_mul, toDiagramsFree_crossing]
    exact ψ_mul_ψ ℤ _ _
  | braid i j h =>
    simp only [map_sub, map_mul, toDiagramsFree_crossing, sub_eq_zero, h]
    exact ψ_braid ℤ _ _
  | dots i j h =>
    simp only [map_add, map_mul, toDiagramsFree_dot]
    exact x_mul_x_add_x_mul_x ℤ (Fin.val_ne_of_ne h)
  | distant i j h =>
    simp only [map_add, map_mul, toDiagramsFree_crossing]
    exact ψ_mul_ψ_add_ψ_mul_ψ ℤ h
  | mixedRight i =>
    simp only [map_sub, map_add, map_mul, map_one, toDiagramsFree_dot, toDiagramsFree_crossing,
      Fin.coe_castSucc, Fin.val_succ, sub_eq_zero]
    exact x_mul_ψ_add_ψ_mul_x ℤ (by omega)
  | mixedLeft i =>
    simp only [map_sub, map_add, map_mul, map_one, toDiagramsFree_dot, toDiagramsFree_crossing,
      Fin.coe_castSucc, Fin.val_succ, sub_eq_zero]
    exact ψ_mul_x_add_x_mul_ψ ℤ (by omega)
  | spectator i j hl hr =>
    simp only [map_add, map_mul, toDiagramsFree_dot, toDiagramsFree_crossing]
    exact x_mul_ψ_add_ψ_mul_x_of_ne ℤ (fun h => hl (Fin.ext h)) (fun h => hr (Fin.ext h))

theorem toDiagramsFree_ideal (n : ℕ) (w : NilHeckeAction.Free n) (hw : w ∈ relIdeal n) :
    toDiagramsFree n w = 0 := by
  rw [relIdeal, relTwoSided, TwoSidedIdeal.mem_asIdeal] at hw
  induction hw using TwoSidedIdeal.span_induction with
  | mem x h => exact toDiagramsFree_relator n x h
  | zero => exact map_zero _
  | add x y hx hy ihx ihy => rw [map_add, ihx, ihy, add_zero]
  | neg x hx ih => rw [map_neg, ih, neg_zero]
  | left_absorb a x hx ih => rw [map_mul, ih, mul_zero]
  | right_absorb b x hx ih => rw [map_mul, ih, zero_mul]

/-- The comparison homomorphism from odd-lean's presented odd nilHecke ring to endomorphisms
of `n + 2` strands in the diagrammatic category. -/
def toDiagrams (n : ℕ) : Presented n →+* End ((pres ℤ).obj (strands (n + 2))) :=
  Ideal.Quotient.lift (relIdeal n) (toDiagramsFree n).toRingHom (toDiagramsFree_ideal n)

@[simp] theorem toDiagrams_mk (n : ℕ) (w : NilHeckeAction.Free n) :
    toDiagrams n (Ideal.Quotient.mk (relIdeal n) w) = toDiagramsFree n w := rfl

@[simp] theorem toDiagrams_dot (n : ℕ) (j : Fin (n + 2)) :
    toDiagrams n (dot n j) = x ℤ (n + 2) j := toDiagramsFree_dot n j

@[simp] theorem toDiagrams_crossing (n : ℕ) (i : Fin (n + 1)) :
    toDiagrams n (crossing n i) = ψ ℤ (n + 2) i := toDiagramsFree_crossing n i

/-! ## Compatibility with the polynomial action -/

/-- The polynomial representation of the diagrammatic category, restricted along
`toDiagrams`, is odd-lean's action of the presented ring on `SkewPolynomial (n + 2)`. -/
theorem realize_toDiagrams (n : ℕ) (a : Presented n) :
    realize (n + 2) (toDiagrams n a) = action n a := by
  obtain ⟨w, rfl⟩ := Ideal.Quotient.mk_surjective a
  rw [toDiagrams_mk, action_mk]
  induction w using FreeAlgebra.induction with
  | grade0 r =>
    rw [AlgHom.commutes, AlgHom.commutes, eq_intCast, eq_intCast, map_intCast]
  | grade1 g =>
    cases g with
    | inl j =>
      rw [show FreeAlgebra.ι ℤ (Sum.inl j) = dotFree n j from rfl, toDiagramsFree_dot,
        freeAction_dot, realize_x]
    | inr i =>
      rw [show FreeAlgebra.ι ℤ (Sum.inr i) = crossingFree n i from rfl, toDiagramsFree_crossing,
        freeAction_crossing, realize_ψ]
  | add a b ha hb => rw [map_add, map_add, map_add, ha, hb]
  | mul a b ha hb => rw [map_mul, map_mul, map_mul, ha, hb]

theorem realize_comp_toDiagrams (n : ℕ) : (realize (n + 2)).comp (toDiagrams n) = action n :=
  RingHom.ext (realize_toDiagrams n)

theorem toDiagrams_injective (n : ℕ) : Function.Injective (toDiagrams n) := by
  intro a b h
  apply NilHeckeBasis.action_injective n
  rw [← realize_toDiagrams, ← realize_toDiagrams, h]

/-! ## Surjectivity: diagrams are generated by dots and crossings -/

theorem diag_cast {a b a' b' : Obj sig} (f : a ⟶ b) (ha : a = a') (hb : b = b') :
    (pres ℤ).diag (Diagram.cast f ha hb) =
      eqToHom (congrArg (pres ℤ).obj ha.symm) ≫ (pres ℤ).diag f ≫
        eqToHom (congrArg (pres ℤ).obj hb) := by
  subst ha hb; simp

/-- The `ℤ`-linear structure of the presented category coming from the presentation. For
`R = ℤ` it is not definitionally the generic `ℤ`-linear structure of a preadditive category,
so lemmas about the scalar action of `Presentation.hom_induction_layers` must name it. -/
abbrev presLinear : Linear ℤ (ONH ℤ) := Presentation.instLinearQuotientFreeObjHomRel (pres ℤ)

/-- The induction predicate for surjectivity: morphisms between objects of different widths
vanish, and endomorphisms of `n + 2` strands lie in the image of `toDiagrams n`. -/
def InImage (n : ℕ) {a b : Obj sig} (g : (pres ℤ).obj a ⟶ (pres ℤ).obj b) : Prop :=
  (a.word.length ≠ b.word.length → g = 0) ∧
    ∀ (ha : a = strands (n + 2)) (hb : b = strands (n + 2)),
      eqToHom (congrArg (pres ℤ).obj ha.symm) ≫ g ≫ eqToHom (congrArg (pres ℤ).obj hb) ∈
        (toDiagrams n).range

theorem inImage_layer (n : ℕ) (L : Layer sig) (hv : L.Valid) :
    InImage n ((pres ℤ).diag (Diagram.ofLayer L hv)) := by
  refine ⟨fun hne => absurd (layer_cod_length L).symm hne, fun ha hb => ?_⟩
  have hlen : L.left.length + L.gen.arity + L.right.length = n + 2 := by
    have := congrArg (fun o : Obj sig => o.word.length) ha
    simpa [Layer.dom, Nat.add_assoc] using this
  rw [← diag_cast _ ha hb]
  rcases hg : L.gen with _ | _
  · rw [hg] at hlen
    refine ⟨dot n ⟨L.left.length, by simp [Gen.arity] at hlen; omega⟩, ?_⟩
    rw [toDiagrams_dot, x_def ℤ (by simp [Gen.arity] at hlen; omega)]
    apply Presentation.diag_eq_of_layers_eq
    simp only [layers_dlay, Diagram.layers_cast, Diagram.layers_ofLayer, List.cons.injEq,
      and_true]
    refine layer_ext ?_ ?_ ?_ <;> simp [lay, hg, Gen.arity] at hlen ⊢
    omega
  · rw [hg] at hlen
    refine ⟨crossing n ⟨L.left.length, by simp [Gen.arity] at hlen; omega⟩, ?_⟩
    rw [toDiagrams_crossing, ψ_def ℤ (by simp [Gen.arity] at hlen; omega)]
    apply Presentation.diag_eq_of_layers_eq
    simp only [layers_dlay, Diagram.layers_cast, Diagram.layers_ofLayer, List.cons.injEq,
      and_true]
    refine layer_ext ?_ ?_ ?_ <;> simp [lay, hg, Gen.arity] at hlen ⊢
    omega

theorem inImage (n : ℕ) {a b : Obj sig} (g : (pres ℤ).obj a ⟶ (pres ℤ).obj b) :
    InImage n g := by
  induction g using (pres ℤ).hom_induction_layers with
  | nil h =>
    refine ⟨fun hne => absurd (congrArg (fun o : Obj sig => o.word.length) h) hne,
      fun ha hb => ?_⟩
    subst ha hb
    simp only [eqToHom_refl, Presentation.diag_id, Category.id_comp]
    exact (toDiagrams n).range.one_mem
  | layer L hv => exact inImage_layer n L hv
  | comp f g hf hg =>
    rename_i a b c
    refine ⟨fun hne => ?_, fun ha hc => ?_⟩
    · by_cases hab : a.word.length = b.word.length
      · rw [hg.1 (fun h => hne (hab.trans h)), Limits.comp_zero]
      · rw [hf.1 hab, Limits.zero_comp]
    · by_cases hb : b.word.length = n + 2
      · have hb' : b = strands (n + 2) := obj_ext (by simpa using hb)
        have e : eqToHom (congrArg (pres ℤ).obj ha.symm) ≫ (f ≫ g) ≫
            eqToHom (congrArg (pres ℤ).obj hc) =
            (eqToHom (congrArg (pres ℤ).obj ha.symm) ≫ f ≫ eqToHom (congrArg (pres ℤ).obj hb')) ≫
              (eqToHom (congrArg (pres ℤ).obj hb'.symm) ≫ g ≫
                eqToHom (congrArg (pres ℤ).obj hc)) := by
          simp
        rw [e]
        exact (toDiagrams n).range.mul_mem (hg.2 hb' hc) (hf.2 ha hb')
      · have hf0 : f = 0 := hf.1 (by rw [ha]; simpa using Ne.symm hb)
        simp only [hf0, Limits.zero_comp, Limits.comp_zero]
        exact (toDiagrams n).range.zero_mem
  | zero =>
    refine ⟨fun _ => rfl, fun ha hb => ?_⟩
    rw [Limits.zero_comp, Limits.comp_zero]
    exact (toDiagrams n).range.zero_mem
  | add f g hf hg =>
    refine ⟨fun hne => by rw [hf.1 hne, hg.1 hne, add_zero], fun ha hb => ?_⟩
    rw [Preadditive.add_comp, Preadditive.comp_add]
    exact (toDiagrams n).range.add_mem (hf.2 ha hb) (hg.2 ha hb)
  | smul r f hf =>
    rename_i a b
    refine ⟨fun hne => ?_, fun ha hb => ?_⟩
    · have h := @Linear.comp_smul ℤ _ _ _ _ presLinear _ _ _
        (0 : (pres ℤ).obj a ⟶ (pres ℤ).obj a) r (0 : (pres ℤ).obj a ⟶ (pres ℤ).obj b)
      rw [Limits.zero_comp, Limits.zero_comp] at h
      rw [hf.1 hne]
      exact h.symm
    · rw [@Linear.smul_comp ℤ _ _ _ _ presLinear, @Linear.comp_smul ℤ _ _ _ _ presLinear]
      convert (toDiagrams n).range.zsmul_mem (hf.2 ha hb) r using 1
      exact int_smul_eq_zsmul (@Linear.homModule ℤ _ _ _ _ presLinear _ _) r _

theorem toDiagrams_surjective (n : ℕ) : Function.Surjective (toDiagrams n) := by
  intro f
  obtain ⟨a, ha⟩ := (inImage n f).2 rfl rfl
  exact ⟨a, by simpa using ha⟩

/-! ## The isomorphism -/

theorem toDiagrams_bijective (n : ℕ) : Function.Bijective (toDiagrams n) :=
  ⟨toDiagrams_injective n, toDiagrams_surjective n⟩

/-- **The odd nilHecke ring is the diagrammatic endomorphism ring of `n + 2` strands.**

EKL, arXiv:1111.1320v1, Proposition 2.1 and §2.2: odd-lean's presented odd nilHecke ring
`Presented n` (rank `n + 2`, the seven relator families (2.7)–(2.10)) is isomorphic, via
`dot n j ↦ x (n+2) j` and `crossing n i ↦ ψ (n+2) i`, to the endomorphism ring of `n + 2`
strands in the presented super 2-category with odd dots and crossings in which only the
square, braid and mixed relations are imposed and the anticommutation relations are the
Koszul-signed interchange law. -/
def presentedEquivEnd (n : ℕ) : Presented n ≃+* End ((pres ℤ).obj (strands (n + 2))) :=
  RingEquiv.ofBijective (toDiagrams n) (toDiagrams_bijective n)

@[simp] theorem presentedEquivEnd_apply (n : ℕ) (a : Presented n) :
    presentedEquivEnd n a = toDiagrams n a := rfl

theorem presentedEquivEnd_dot (n : ℕ) (j : Fin (n + 2)) :
    presentedEquivEnd n (dot n j) = x ℤ (n + 2) j := toDiagrams_dot n j

theorem presentedEquivEnd_crossing (n : ℕ) (i : Fin (n + 1)) :
    presentedEquivEnd n (crossing n i) = ψ ℤ (n + 2) i := toDiagrams_crossing n i

/-- The polynomial representation of the diagrammatic odd nilHecke category is faithful on
endomorphisms of `n + 2` strands. -/
theorem realize_injective (n : ℕ) : Function.Injective (realize (n + 2)) := by
  intro f g h
  obtain ⟨a, rfl⟩ := toDiagrams_surjective n f
  obtain ⟨b, rfl⟩ := toDiagrams_surjective n g
  rw [realize_toDiagrams, realize_toDiagrams] at h
  rw [NilHeckeBasis.action_injective n h]

end OddMath.Diagrams.OddNilHecke

end
