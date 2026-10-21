import OddMath.CoveringQuantum.Ordinary

/-!
# Weight dimensions in the ordinary specialization

The ordinary dimension input for Hill–Wang's character comparison is obtained from
quantum Gabber–Kac. At `π = 1`, the dimension of a Serre weight space plus the dimension
of the classical Serre span is the number of words of that weight. In particular the
weight dimension is independent of the characteristic-zero field and transcendental
parameter. No parity or bar-consistency assumption is needed for this specialization.
-/

noncomputable section

namespace OddMath.CoveringQuantum.SuperCartanDatum

open LieLean Module

variable {I : Type*} (C : SuperCartanDatum I)

/-- The image of the free weight space in the Serre-presented half algebra. -/
def serreWeightSpace {k : Type*} [CommRing k] (q : kˣ) (π : k) (ν : I →₀ ℕ) :
    Submodule k (C.serreF q π) :=
  (PreF.weightSpace k ν).map (C.toSerreF q π).toLinearMap

/-- Each weight space is finite dimensional, since only finitely many words have
any fixed weight. This does not require a finite set of simple roots. -/
instance finiteDimensional_serreWeightSpace {k : Type*} [Field k]
    (q : kˣ) (π : k) (ν : I →₀ ℕ) : FiniteDimensional k (C.serreWeightSpace q π ν) := by
  change FiniteDimensional k ((LusztigF.weightSpace k ν).map _)
  infer_instance

variable [DecidableEq I] {k : Type*} [Field k] [CharZero k] (q : kˣ)
  (hq : Transcendental ℚ (q : k)) [Finite I]

include hq

/-- On a fixed weight space, the ordinary quotient kernel is the quantum Serre span
at the inverse parameter, matching the normalization of the free form. -/
theorem toSerreF_one_eq_zero_iff_mem_serreSpan (ν : I →₀ ℕ) {x : PreF k I}
    (hx : x ∈ PreF.weightSpace k ν) :
    C.toSerreF q 1 x = 0 ↔
      x ∈ LusztigF.serreSpan C.lusztigDatum
        (fun i ↦ ((q : k)⁻¹) ^ C.lusztigDatum.d i) ν := by
  have hqi : Transcendental ℚ ((q : k)⁻¹) := fun h ↦ hq (by simpa using h.inv)
  constructor
  · intro h
    apply (LusztigF.mem_serreSpan_of_mem_radical_and_finrank_serreSpan
      C.lusztigDatum hqi ν).1 x _ hx
    apply (LusztigF.mem_radical_iff C.lusztigDatum ((q : k)⁻¹)).mpr
    intro y
    rw [← C.form_one q]
    exact (PreF.mem_radical_iff _ _).mp
      (C.serreIdeal_le_radical q 1 (one_pow 2) ((C.mem_serreIdeal q 1 x).mpr h)) y
  · intro h
    apply (C.mem_serreIdeal q 1 x).mp
    apply C.ordinary_serreIdeal_le q hq
    exact LusztigF.serreSpan_le_serreIdeal C.lusztigDatum (inv_ne_zero q.ne_zero)
      (fun _ hn ↦ LusztigF.pow_ne_one_of_transcendental hqi hn) h

/-- The ordinary weight dimension is determined by a parameter-free classical Serre
span over `ℚ` and the finite set of words of the given weight. -/
theorem finrank_serreWeightSpace_one (ν : I →₀ ℕ) :
    finrank k (C.serreWeightSpace q 1 ν) +
      finrank ℚ (LusztigF.serreSpan C.lusztigDatum (fun _ ↦ (1 : ℚ)) ν) =
        Fintype.card (LusztigF.Words ν) := by
  have hqi : Transcendental ℚ ((q : k)⁻¹) := fun h ↦ hq (by simpa using h.inv)
  set V := LusztigF.weightSpace k ν
  set S := LusztigF.serreSpan C.lusztigDatum
    (fun i ↦ ((q : k)⁻¹) ^ C.lusztigDatum.d i) ν
  set f := (C.toSerreF q 1).toLinearMap.domRestrict V
  have hrange : LinearMap.range f = C.serreWeightSpace q 1 ν := by
    rw [LinearMap.range_domRestrict]
    rfl
  have hker : LinearMap.ker f = S.comap V.subtype := by
    ext y
    simp only [LinearMap.mem_ker, Submodule.mem_comap, Submodule.subtype_apply]
    exact C.toSerreF_one_eq_zero_iff_mem_serreSpan q hq ν y.2
  have hSer : finrank k (S.comap V.subtype) = finrank k S := by
    rw [← Submodule.finrank_map_subtype_eq, Submodule.map_comap_subtype,
      inf_eq_right.2 (LusztigF.serreSpan_le_weightSpace C.lusztigDatum _ ν)]
  have hrn := LinearMap.finrank_range_add_finrank_ker f
  rw [hrange, hker, hSer, LusztigF.finrank_weightSpace,
    (LusztigF.mem_serreSpan_of_mem_radical_and_finrank_serreSpan
      C.lusztigDatum hqi ν).2] at hrn
  exact hrn

/-- Ordinary weight dimensions agree over any two characteristic-zero fields with
transcendental quantum parameters. -/
theorem finrank_serreWeightSpace_one_eq {k' : Type*} [Field k'] [CharZero k']
    (q' : k'ˣ) (hq' : Transcendental ℚ (q' : k')) (ν : I →₀ ℕ) :
    finrank k (C.serreWeightSpace q 1 ν) = finrank k' (C.serreWeightSpace q' 1 ν) := by
  have h := C.finrank_serreWeightSpace_one q hq ν
  have h' := C.finrank_serreWeightSpace_one q' hq' ν
  omega

end OddMath.CoveringQuantum.SuperCartanDatum
