import OddMath.CoveringQuantum.Datum

/-!
# The ordered twisting form

CFLW, arXiv:1307.7056v2, §2.2, fixes an order on the simple indices and defines
an integral bilinear form whose skew part controls the twisting multiplication.
Here we give its entries and their congruence modulo four. The diagonal case of
the congruence uses bar-consistency as well as the off-diagonal evenness condition.
This file does not yet construct the half-algebra twistor.
-/

namespace OddMath.CoveringQuantum.SuperCartanDatum

variable {I : Type*} [LinearOrder I] (C : SuperCartanDatum I)

/-- The entries of the ordered form in CFLW §2.2. -/
def twistPhi (i j : I) : ℤ :=
  if j < i then C.dot i j else if i = j then C.d i
  else -2 * (C.parity i).val * (C.parity j).val

@[simp] theorem twistPhi_self (i : I) : C.twistPhi i i = C.d i := by
  simp [twistPhi]

theorem twistPhi_of_lt {i j : I} (h : i < j) :
    C.twistPhi i j = -2 * (C.parity i).val * (C.parity j).val := by
  simp [twistPhi, not_lt_of_gt h, ne_of_lt h]

theorem twistPhi_of_gt {i j : I} (h : j < i) : C.twistPhi i j = C.dot i j := by
  simp [twistPhi, h]

/-- The skew part of the ordered form agrees modulo four with the Cartan/parity expression. -/
theorem twistPhi_skew_mod_four (hC : C.BarConsistent) (i j : I) :
    Int.ModEq 4 (C.twistPhi i j - C.twistPhi j i)
      (C.dot i j + 2 * (C.parity i).val * (C.parity j).val) := by
  rcases lt_trichotomy i j with hij | rfl | hji
  · rw [C.twistPhi_of_lt hij, C.twistPhi_of_gt hij, C.dot_comm j i]
    obtain ⟨a, ha⟩ := C.even_dot_of_barConsistent hC i j
    change _ % 4 = _ % 4
    rw [ha]
    ring_nf
    omega
  · rw [sub_self, C.dot_self]
    have hm := congrArg ZMod.val (hC i)
    simp only [ZMod.val_natCast] at hm
    have hp : (C.parity i).val = 0 ∨ (C.parity i).val = 1 := by
      have := ZMod.val_lt (C.parity i)
      omega
    change _ % 4 = _ % 4
    rcases hp with hp | hp <;> rw [hp] <;> norm_num <;> omega
  · rw [C.twistPhi_of_gt hji, C.twistPhi_of_lt hji]
    change _ % 4 = _ % 4
    congr 1
    ring

end OddMath.CoveringQuantum.SuperCartanDatum
