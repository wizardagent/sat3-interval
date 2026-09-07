import Sat3.RComplete
import Sat3.Digits

/-
  Iterate `rcomplete_admissible_step` along an admissible digit list.
  Paper Lemma 8.2 covering, without a cardinality bound.
-/

namespace Sat3

def buildFrom (A : Int → Prop) : List Nat → (Int → Prop)
  | [] => A
  | d :: ds => buildFrom (unionShift A (d : Int)) ds

theorem buildFrom_nil (A : Int → Prop) : buildFrom A [] = A := rfl

theorem buildFrom_cons (A : Int → Prop) (d : Nat) (ds : List Nat) :
    buildFrom A (d :: ds) = buildFrom (unionShift A (d : Int)) ds := rfl

private theorem nat_le_int {a b : Nat} (h : a ≤ b) : (a : Int) ≤ b :=
  Int.ofNat_le.mpr h

private theorem two_S_add_one (S : Nat) :
    ((2 * S + 1 : Nat) : Int) = 2 * (S : Int) + 1 := by
  simp

private theorem three_S_add_one (S : Nat) :
    ((3 * S + 1 : Nat) : Int) = 3 * (S : Int) + 1 := by
  simp

private theorem sumList_cons (d : Nat) (ds : List Nat) :
    sumList (d :: ds) = d + sumList ds :=
  rfl

/-- Covering half of Lemma 8.2: admissible digits keep an `S`-complete
set complete, with radius the prefix sum. -/
theorem rcomplete_from_admissible (S : Nat) (A : Int → Prop) :
    ∀ ds,
      IsRComplete (S : Int) A →
      AdmissibleFrom S ds →
      IsRComplete (↑(S + sumList ds)) (buildFrom A ds)
  | [], hA, _ => by
      simpa [buildFrom, sumList] using hA
  | d :: ds, hA, hds => by
      simp [AdmissibleFrom] at hds
      have hdlo : (2 * (S : Int) + 1) ≤ (d : Int) := by
        have := nat_le_int hds.1
        simpa [two_S_add_one] using this
      have hdhi : (d : Int) ≤ 3 * (S : Int) + 1 := by
        have := nat_le_int hds.2.1
        simpa [three_S_add_one] using this
      have hstep : IsRComplete (↑S + ↑d) (unionShift A (d : Int)) :=
        rcomplete_admissible_step A (S : Int) (d : Int)
          (Int.natCast_nonneg S) hdlo hdhi hA
      have hcast : ((S + d : Nat) : Int) = (S : Int) + d := by simp
      have hstep' : IsRComplete (↑(S + d)) (unionShift A (d : Int)) := by
        simpa [hcast] using hstep
      have ih := rcomplete_from_admissible (S + d) (unionShift A (d : Int))
        ds hstep' hds.2.2
      have hsum : S + sumList (d :: ds) = (S + d) + sumList ds := by
        simp [sumList]
        omega
      simpa [buildFrom_cons, hsum] using ih

theorem rcomplete_of_admissible (ds : List Nat)
    (h : IsAdmissible ds) :
    IsRComplete (sumList ds : Int) (buildFrom (fun t => t = 0 ∨ t = 1) ds.tail) := by
  match ds with
  | [] => cases h
  | d :: rest =>
    simp [IsAdmissible] at h
    have hd : d = 1 := h.1
    subst d
    have hbase : IsRComplete (1 : Int) (fun t => t = 0 ∨ t = 1) := rcomplete_01
    have hrest := rcomplete_from_admissible 1 (fun t => t = 0 ∨ t = 1) rest
      hbase h.2
    have : sumList (1 :: rest) = 1 + sumList rest := rfl
    simpa [this, buildFrom] using hrest

/-- Corollary 8.3, covering: greedy digits yield an `R`-complete set. -/
theorem greedy_rcomplete (k R : Nat) (hk : 1 ≤ k)
    (hlo : Ilo k ≤ R) (hhi : R ≤ Ihi k) :
    IsRComplete (R : Int)
      (buildFrom (fun t => t = 0 ∨ t = 1) (greedyDigits k R).tail) := by
  have hadm := greedyDigits_admissible k R hk hlo hhi
  have hsum := greedyDigits_sum k R hk hlo hhi
  have h := rcomplete_of_admissible (greedyDigits k R) hadm
  simpa [hsum] using h

end Sat3
