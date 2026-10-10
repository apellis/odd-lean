import OddMath.CoveringQuantum.Twistor.Form
import OddMath.CoveringQuantum.Twistor.Integers
import OddMath.CoveringQuantum.Serre

/-!
# Ordered phases on Serre words

The phase of a Serre word and the twisting rule for quantum binomials identify
the image of each ordinary Serre generator as a unit multiple of its covering
counterpart. The statement is on individual generators; preservation of their
entire two-sided ideals is a separate step.
-/

noncomputable section

namespace OddMath.CoveringQuantum

namespace PreF

variable {k I : Type*} [CommRing k] (f : I → I → kˣ)

/-- The internal phase of a repeated letter counts pairs of positions. -/
theorem wordPhase_replicate (i : I) (n : ℕ) :
    wordPhase f (List.replicate n i) = f i i ^ n.choose 2 := by
  induction n with
  | zero => simp
  | succ n ih =>
    simp only [List.replicate_succ, wordPhase_cons, List.map_replicate, List.prod_replicate, ih]
    rw [← pow_add, Nat.choose_succ_succ, Nat.choose_one_right]

private theorem choose_two_add (s r : ℕ) :
    (s + r).choose 2 = s.choose 2 + r.choose 2 + s * r := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [Nat.add_succ, Nat.choose_succ_succ, Nat.choose_one_right, ih,
      Nat.choose_succ_succ, Nat.choose_one_right]
    ring

/-- The phase of a word with one distinguished letter. -/
theorem wordPhase_serreWord (i j : I) (s r : ℕ) :
    wordPhase f (List.replicate s i ++ [j] ++ List.replicate r i) =
      f i i ^ (s + r).choose 2 * f i j ^ s * f j i ^ r := by
  simp only [wordPhase_append, wordPhase_replicate, wordPhase_cons, wordPhase_nil,
    List.map_nil, List.prod_nil, mul_one, List.map_append, List.prod_append,
    List.map_replicate, List.prod_replicate, List.map_cons, List.prod_cons]
  rw [choose_two_add, pow_add, pow_add]
  simp only [← pow_mul]
  rw [Nat.mul_comm r s]
  ac_rfl

end PreF

namespace SuperCartanDatum

variable {I k : Type*} [LinearOrder I] [CommRing k]
  (C : SuperCartanDatum I) (t : kˣ)

/-- The free twist on an individual monomial of a Serre relation. -/
theorem freeTwist_serreWord (i j : I) (s r : ℕ) :
    C.freeTwist t (PreF.θ k i ^ s * PreF.θ k j * PreF.θ k i ^ r) =
      ((t ^ ((C.d i : ℤ) * ((s + r).choose 2 : ℤ) +
        (s : ℤ) * C.twistPhi i j + (r : ℤ) * C.twistPhi j i) : kˣ) : k) •
        (PreF.θ k i ^ s * PreF.θ k j * PreF.θ k i ^ r) := by
  have hw : PreF.monomial k (List.replicate s i ++ [j] ++ List.replicate r i) =
      PreF.θ k i ^ s * PreF.θ k j * PreF.θ k i ^ r := by
    simp [PreF.monomial, mul_assoc]
  rw [← hw, freeTwist, PreF.wordGauge_monomial, PreF.wordPhase_serreWord]
  congr 2
  rw [C.twistPhi_self]
  simp only [zpow_add, zpow_mul, zpow_natCast]
  congr 1 <;> group

private theorem cast_two_choose_two (r : ℕ) :
    (r : ℤ) * ((r : ℤ) - 1) = 2 * (r.choose 2 : ℤ) := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [Nat.choose_succ_succ, Nat.choose_one_right]
    push_cast
    linear_combination ih

/-- The phase varying with the Serre summation index is precisely its super sign. -/
theorem serre_phase_mod_four (hC : C.BarConsistent) {i j : I} (hij : i ≠ j) (r : ℕ) :
    Int.ModEq 4
      ((C.d i : ℤ) * r * ((C.serreDeg i j : ℤ) - r) +
        ((C.serreDeg i j : ℤ) - r) * C.twistPhi i j + (r : ℤ) * C.twistPhi j i)
      ((C.serreDeg i j : ℤ) * C.twistPhi i j +
        2 * (C.parity i).val * ((r : ℤ) * (C.parity j).val + (r.choose 2 : ℤ))) := by
  have hm := congrArg ZMod.val (hC i)
  simp only [ZMod.val_natCast] at hm
  have hp := ZMod.val_lt (C.parity i)
  have hb : (C.d i : ℤ) + (C.parity i).val =
      2 * (((C.d i + (C.parity i).val) / 2 : ℕ) : ℤ) := by omega
  have hphi := C.twistPhi_skew_mod_four hC j i
  rw [C.dot_comm j i, Int.modEq_iff_dvd] at hphi
  obtain ⟨a, ha⟩ := hphi
  have hd : C.dot i j = (C.d i : ℤ) * (1 - (C.serreDeg i j : ℤ)) := by
    rw [C.serreDeg_eq hij, dot]
    ring
  rw [Int.modEq_iff_dvd]
  refine ⟨(r : ℤ) * a + (((C.d i + (C.parity i).val) / 2 : ℕ) : ℤ) * (r.choose 2 : ℤ), ?_⟩
  linear_combination (r : ℤ) * ha - (r : ℤ) * hd +
    (C.d i : ℤ) * cast_two_choose_two r + 2 * (r.choose 2 : ℤ) * hb

omit [LinearOrder I] in
/-- The square of the simple-root twisting parameter is the corresponding sign. -/
theorem twist_qi_sq (hC : C.BarConsistent) (ht : t ^ 2 = -1) (i : I) :
    (((t ^ C.d i : kˣ) : k)) ^ 2 = C.pii (-1) i := by
  have hp : (-1 : kˣ) ^ C.d i = (-1 : kˣ) ^ (C.parity i).val := by
    have hm := congrArg ZMod.val (hC i)
    simp only [ZMod.val_natCast] at hm
    rw [pow_eq_pow_mod _ (show (-1 : kˣ) ^ 2 = 1 by simp), hm]
  have h : (t ^ C.d i) ^ 2 = (-1 : kˣ) ^ (C.parity i).val := by
    rw [← pow_mul, Nat.mul_comm, pow_mul, ht, hp]
  simpa only [pii, Units.val_pow_eq_pow_val, Units.val_neg, Units.val_one] using
    congrArg (fun v : kˣ ↦ (v : k)) h

omit [LinearOrder I] in
/-- The binomial twisting rule at a simple root. -/
theorem qpBinom_qi_twist (hC : C.BarConsistent) (ht : t ^ 2 = -1)
    (q : kˣ) (i : I) (n r : ℕ) :
    qpBinom (C.qi (t * q) i) 1 n r =
      ((t ^ ((C.d i : ℤ) * r * ((n : ℤ) - r)) : kˣ) : k) *
        qpBinom (C.qi q i) (C.pii (-1) i) n r := by
  have ht4 : t ^ 4 = 1 := by rw [show 4 = 2 * 2 by decide, pow_mul, ht]; simp
  have hi4 : (t ^ C.d i) ^ 4 = 1 := by
    rw [← pow_mul, Nat.mul_comm, pow_mul, ht4, one_pow]
  simp only [qi, mul_pow]
  rw [qpBinom_twist _ _ hi4, C.twist_qi_sq t hC ht]
  congr 2
  rw [← zpow_natCast t, ← zpow_mul]
  congr 1
  ring

/-- The ordered map carries each ordinary Serre generator to a unit multiple of the
covering Serre generator at the negative sign. -/
theorem freeTwist_serreElt (hC : C.BarConsistent) (ht : t ^ 2 = -1)
    (q : kˣ) {i j : I} (hij : i ≠ j) :
    C.freeTwist t (C.serreElt (t * q) 1 i j) =
      ((t ^ ((C.d i : ℤ) * ((C.serreDeg i j).choose 2 : ℤ) +
        (C.serreDeg i j : ℤ) * C.twistPhi i j) : kˣ) : k) • C.serreElt q (-1) i j := by
  let N := C.serreDeg i j
  let K := (C.d i : ℤ) * (N.choose 2 : ℤ) + (N : ℤ) * C.twistPhi i j
  have ht4 : t ^ 4 = 1 := by rw [show 4 = 2 * 2 by decide, pow_mul, ht]; simp
  unfold serreElt
  rw [map_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun r hr ↦ ?_
  have hrN : r ≤ N := Nat.lt_succ_iff.mp (Finset.mem_range.mp hr)
  have hp : t ^ ((C.d i : ℤ) * r * ((N : ℤ) - r)) *
      t ^ ((C.d i : ℤ) * (N.choose 2 : ℤ) + ((N - r : ℕ) : ℤ) * C.twistPhi i j +
        (r : ℤ) * C.twistPhi j i) =
      t ^ K * ((-1 : kˣ) ^ (C.parity i).val) ^ (r * (C.parity j).val + r.choose 2) := by
    have hm : Int.ModEq 4
        ((C.d i : ℤ) * r * ((N : ℤ) - r) + (C.d i : ℤ) * (N.choose 2 : ℤ) +
          ((N - r : ℕ) : ℤ) * C.twistPhi i j + (r : ℤ) * C.twistPhi j i)
        (K + 2 * (C.parity i).val * ((r : ℤ) * (C.parity j).val + (r.choose 2 : ℤ))) := by
      rw [Nat.cast_sub hrN]
      convert (Int.ModEq.refl ((C.d i : ℤ) * (N.choose 2 : ℤ))).add
        (C.serre_phase_mod_four hC hij r) using 1 <;> dsimp [N, K] <;> ring
    rw [← zpow_add]
    have he := (zpow_eq_zpow_emod'
      ((C.d i : ℤ) * r * ((N : ℤ) - r) + (C.d i : ℤ) * (N.choose 2 : ℤ) +
        ((N - r : ℕ) : ℤ) * C.twistPhi i j + (r : ℤ) * C.twistPhi j i) ht4).trans
      ((congrArg (fun z : ℤ ↦ t ^ z) hm).trans
        (zpow_eq_zpow_emod'
          (K + 2 * (C.parity i).val * ((r : ℤ) * (C.parity j).val + (r.choose 2 : ℤ))) ht4).symm)
    rw [show (C.d i : ℤ) * r * ((N : ℤ) - r) +
      ((C.d i : ℤ) * (N.choose 2 : ℤ) + ((N - r : ℕ) : ℤ) * C.twistPhi i j +
        (r : ℤ) * C.twistPhi j i) =
      (C.d i : ℤ) * r * ((N : ℤ) - r) + (C.d i : ℤ) * (N.choose 2 : ℤ) +
        ((N - r : ℕ) : ℤ) * C.twistPhi i j + (r : ℤ) * C.twistPhi j i by ring, he]
    rw [zpow_add]
    congr 1
    rw [show 2 * ((C.parity i).val : ℤ) * ((r : ℤ) * (C.parity j).val + (r.choose 2 : ℤ)) =
      2 * ((C.parity i).val : ℤ) * ((r * (C.parity j).val + r.choose 2 : ℕ) : ℤ) by
        push_cast; ring]
    simp only [zpow_mul, zpow_natCast, zpow_ofNat, ht]
  have hp' := congrArg (fun v : kˣ ↦ (v : k)) hp
  simp only [Units.val_mul, Units.val_pow_eq_pow_val, Units.val_neg, Units.val_one] at hp'
  rw [map_smul, C.freeTwist_serreWord, Nat.sub_add_cancel hrN]
  simp only [serreCoeff, show C.pii (1 : k) i = 1 by simp [pii], one_pow, mul_one]
  rw [C.qpBinom_qi_twist t hC ht]
  simp only [smul_smul]
  congr 1
  dsimp [N, K] at hp' ⊢
  simp only [pii]
  linear_combination (-1 : k) ^ r * qpBinom (C.qi q i) ((-1 : k) ^ (C.parity i).val)
    (C.serreDeg i j) r * hp'

end SuperCartanDatum

end OddMath.CoveringQuantum
