import Sat3.Card

/-
  Distinct subset sums for admissible digits (Lemma 8.2, cardinality).
  Nested doubling from the front: if P ⊆ [0, S] is duplicate-free and
  d ≥ 2S+1, then P ∪ (P+d) is duplicate-free in [0, S+d].
-/

namespace Sat3

def Nodup : List Nat → Prop
  | [] => True
  | x :: xs => ¬ Mem xs x ∧ Nodup xs

def Bounded (S : Nat) (P : List Nat) : Prop :=
  ∀ x, Mem P x → x ≤ S

def ofList (P : List Nat) : Int → Prop :=
  fun t => ∃ n, Mem P n ∧ t = (n : Int)

/-- Nested doubling in digit order (first digit first). -/
def growFrom (P : List Nat) : List Nat → List Nat
  | [] => P
  | d :: ds => growFrom (P ++ mapAdd d P) ds

theorem growFrom_nil (P : List Nat) : growFrom P [] = P := rfl

theorem growFrom_cons (P : List Nat) (d : Nat) (ds : List Nat) :
    growFrom P (d :: ds) = growFrom (P ++ mapAdd d P) ds := rfl

theorem nodup_nil : Nodup [] := trivial

theorem nodup_singleton (x : Nat) : Nodup [x] := by
  constructor
  · intro h; cases h
  · trivial

theorem nodup_01 : Nodup [0, 1] := by
  constructor
  · intro h
    cases h with
    | inl h => cases h
    | inr h => cases h
  · exact nodup_singleton 1

theorem bounded_01 : Bounded 1 [0, 1] := by
  intro x hx
  cases hx with
  | inl h => omega
  | inr h =>
    cases h with
    | inl h => omega
    | inr h => cases h

theorem nodup_append :
    ∀ xs ys,
      Nodup xs →
      Nodup ys →
      (∀ y, Mem xs y → ¬ Mem ys y) →
      Nodup (xs ++ ys)
  | [], ys, _, hy, _ => hy
  | x :: xs, ys, hx, hy, hdis => by
      constructor
      · intro hmem
        have h := (mem_append xs ys x).mp hmem
        cases h with
        | inl h => exact hx.1 h
        | inr h => exact hdis x (Or.inl rfl) h
      · exact nodup_append xs ys hx.2 hy
          (fun y hyxs => hdis y (Or.inr hyxs))

theorem nodup_mapAdd (d : Nat) :
    ∀ xs, Nodup xs → Nodup (mapAdd d xs)
  | [], _ => trivial
  | x :: xs, h => by
      constructor
      · intro hmem
        obtain ⟨z, hz, heq⟩ := (mem_mapAdd d xs (x + d)).mp hmem
        have hz' : z = x := by
          have : z + d = x + d := heq.symm
          exact Nat.add_right_cancel this
        exact h.1 (hz' ▸ hz)
      · exact nodup_mapAdd d xs h.2

theorem disjoint_shift (S d : Nat) (P : List Nat)
    (hB : Bounded S P) (hd : 2 * S + 1 ≤ d) (y : Nat)
    (hy : Mem P y) : ¬ Mem (mapAdd d P) y := by
  intro hmem
  obtain ⟨x, hx, heq⟩ := (mem_mapAdd d P y).mp hmem
  have hyS : y ≤ S := hB y hy
  have hxS : x ≤ S := hB x hx
  omega

theorem bounded_grow (S d : Nat) (P : List Nat)
    (hB : Bounded S P) : Bounded (S + d) (P ++ mapAdd d P) := by
  intro y hy
  have hy' := (mem_append P (mapAdd d P) y).mp hy
  cases hy' with
  | inl hP =>
    have := hB y hP
    omega
  | inr hQ =>
    obtain ⟨x, hx, heq⟩ := (mem_mapAdd d P y).mp hQ
    have := hB x hx
    omega

theorem nodup_grow (S d : Nat) (P : List Nat)
    (hN : Nodup P) (hB : Bounded S P) (hd : 2 * S + 1 ≤ d) :
    Nodup (P ++ mapAdd d P) :=
  nodup_append P (mapAdd d P) hN (nodup_mapAdd d P hN)
    (fun y hy => disjoint_shift S d P hB hd y hy)

theorem nodup_growFrom (S : Nat) (P : List Nat) :
    ∀ ds,
      Nodup P →
      Bounded S P →
      AdmissibleFrom S ds →
      Nodup (growFrom P ds)
  | [], hN, _, _ => hN
  | d :: ds, hN, hB, hds => by
      simp [AdmissibleFrom] at hds
      have hN' := nodup_grow S d P hN hB hds.1
      have hB' := bounded_grow S d P hB
      exact nodup_growFrom (S + d) (P ++ mapAdd d P) ds hN' hB' hds.2.2

theorem growFrom_length (P : List Nat) :
    ∀ ds, (growFrom P ds).length = P.length * 2 ^ ds.length
  | [] => by
      simp [growFrom]
  | d :: ds => by
      have ih := growFrom_length (P ++ mapAdd d P) ds
      have hlen : (P ++ mapAdd d P).length = P.length * 2 := by
        rw [List.length_append, mapAdd_length]
        omega
      have h2 : 2 ^ (ds.length + 1) = 2 ^ ds.length * 2 := Nat.pow_succ 2 ds.length
      calc
        (growFrom P (d :: ds)).length
            = (growFrom (P ++ mapAdd d P) ds).length := rfl
        _ = (P ++ mapAdd d P).length * 2 ^ ds.length := ih
        _ = (P.length * 2) * 2 ^ ds.length := by rw [hlen]
        _ = P.length * (2 * 2 ^ ds.length) := by rw [Nat.mul_assoc]
        _ = P.length * (2 ^ ds.length * 2) := by rw [Nat.mul_comm 2]
        _ = P.length * 2 ^ (ds.length + 1) := by rw [h2]

theorem ofList_01 (t : Int) : ofList [0, 1] t ↔ t = 0 ∨ t = 1 := by
  constructor
  · intro ⟨n, hn, ht⟩
    have hn' : n = 0 ∨ n = 1 := by
      cases hn with
      | inl h => exact Or.inl h
      | inr h =>
        cases h with
        | inl h => exact Or.inr h
        | inr h => cases h
    cases hn' with
    | inl h => subst n; exact Or.inl ht
    | inr h => subst n; exact Or.inr ht
  · intro h
    cases h with
    | inl h => exact ⟨0, Or.inl rfl, h⟩
    | inr h => exact ⟨1, Or.inr (Or.inl rfl), h⟩

theorem ofList_union (P : List Nat) (d : Nat) (t : Int) :
    unionShift (ofList P) (d : Int) t ↔ ofList (P ++ mapAdd d P) t := by
  constructor
  · intro h
    cases h with
    | inl h =>
      obtain ⟨n, hn, ht⟩ := h
      exact ⟨n, (mem_append _ _ _).mpr (Or.inl hn), ht⟩
    | inr h =>
      obtain ⟨n, hn, ht⟩ := h
      refine ⟨n + d, (mem_append _ _ _).mpr
        (Or.inr ((mem_mapAdd d P (n + d)).mpr ⟨n, hn, rfl⟩)), ?_⟩
      have hcast : ((n + d : Nat) : Int) = (n : Int) + d := by simp
      omega
  · intro ⟨n, hn, ht⟩
    have hn' := (mem_append P (mapAdd d P) n).mp hn
    cases hn' with
    | inl hP =>
      exact Or.inl ⟨n, hP, ht⟩
    | inr hQ =>
      obtain ⟨m, hm, hnm⟩ := (mem_mapAdd d P n).mp hQ
      subst n
      refine Or.inr ?_
      simp [shift]
      refine ⟨m, hm, ?_⟩
      have hcast : ((m + d : Nat) : Int) = (m : Int) + d := by simp
      omega

theorem buildFrom_congr {A B : Int → Prop} (h : ∀ t, A t ↔ B t) :
    ∀ ds t, buildFrom A ds t ↔ buildFrom B ds t
  | [], t => h t
  | d :: ds, t => by
      have hU : ∀ u, unionShift A (d : Int) u ↔ unionShift B (d : Int) u := by
        intro u
        constructor
        · intro hu
          cases hu with
          | inl hu => exact Or.inl ((h u).mp hu)
          | inr hu => exact Or.inr ((h (u - d)).mp hu)
        · intro hu
          cases hu with
          | inl hu => exact Or.inl ((h u).mpr hu)
          | inr hu => exact Or.inr ((h (u - d)).mpr hu)
      exact buildFrom_congr hU ds t

theorem buildFrom_ofList (P : List Nat) :
    ∀ ds t, buildFrom (ofList P) ds t ↔ ofList (growFrom P ds) t
  | [], t => Iff.rfl
  | d :: ds, t => by
      have hU := ofList_union P d
      have hcong := buildFrom_congr hU ds t
      have ih := buildFrom_ofList (P ++ mapAdd d P) ds t
      constructor
      · intro h
        exact ih.mp (hcong.mp h)
      · intro h
        exact hcong.mpr (ih.mpr h)

theorem greedyDigits_tail_admissible (k R : Nat) (hk : 1 ≤ k)
    (hlo : Ilo k ≤ R) (hhi : R ≤ Ihi k) :
    AdmissibleFrom 1 (greedyDigits k R).tail := by
  have hadm := greedyDigits_admissible k R hk hlo hhi
  revert hadm
  cases greedyDigits k R with
  | nil =>
    intro hadm
    simp [IsAdmissible] at hadm
  | cons d rest =>
    intro hadm
    simp [IsAdmissible] at hadm
    have hd : d = 1 := hadm.1
    subst d
    exact hadm.2

/-- The greedy nested union, as a list, is duplicate-free. -/
theorem greedy_growFrom_nodup (k R : Nat) (hk : 1 ≤ k)
    (hlo : Ilo k ≤ R) (hhi : R ≤ Ihi k) :
    Nodup (growFrom [0, 1] (greedyDigits k R).tail) :=
  nodup_growFrom 1 [0, 1] (greedyDigits k R).tail
    nodup_01 bounded_01 (greedyDigits_tail_admissible k R hk hlo hhi)

theorem greedy_growFrom_length (k R : Nat) (hk : 1 ≤ k)
    (hlo : Ilo k ≤ R) (hhi : R ≤ Ihi k) :
    (growFrom [0, 1] (greedyDigits k R).tail).length = 2 ^ k := by
  obtain ⟨rest, hrest⟩ := greedyDigits_cons_one k R hk hlo hhi
  have hlen := greedyDigits_length k R hk hlo hhi
  have : (greedyDigits k R).tail = rest := by
    rw [hrest]
    rfl
  have hrestlen : rest.length + 1 = k := by
    have : (1 :: rest).length = k := by
      rw [← hrest, hlen]
    simpa using this
  have hgl := growFrom_length [0, 1] rest
  have hP : ([0, 1] : List Nat).length = 2 := by simp
  rw [this, hgl, hP]
  have hpow : 2 ^ (rest.length + 1) = 2 ^ rest.length * 2 :=
    Nat.pow_succ 2 rest.length
  have hk' : k = rest.length + 1 := by omega
  rw [hk', hpow]
  omega

/-- Every point of the greedy `R`-complete set is an entry of a
duplicate-free list of length `2^k`, and conversely. -/
theorem greedy_set_iff (k R : Nat) (_hk : 1 ≤ k)
    (_hlo : Ilo k ≤ R) (_hhi : R ≤ Ihi k) (t : Int) :
    buildFrom (fun z => z = 0 ∨ z = 1) (greedyDigits k R).tail t ↔
      ofList (growFrom [0, 1] (greedyDigits k R).tail) t := by
  have h01 : ∀ u, ofList [0, 1] u ↔ ((fun z => z = 0 ∨ z = 1) u) :=
    fun u => ofList_01 u
  have hcong := buildFrom_congr h01 (greedyDigits k R).tail t
  have hlist := buildFrom_ofList [0, 1] (greedyDigits k R).tail t
  constructor
  · intro h
    exact hlist.mp (hcong.mpr h)
  · intro h
    exact hcong.mp (hlist.mpr h)

end Sat3
