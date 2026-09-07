import Sat3.Distinct
import Sat3.PairCover
import Sat3.Cert
import Sat3.NoTriple
import Sat3.NoQuad

/-
  Theorem 9.2: a placed greedy R-complete set is maximal in [n],
  and every point of it is an entry of a list of length 2^k.
-/

namespace Sat3

/-- The unique `k` with `4^{k-1} < n ≤ 4^k` for `n ≥ 2`. -/
def windowK (n : Nat) : Nat :=
  (n - 1).log2 / 2 + 1

theorem two_pow_even (a : Nat) : 2 ^ (2 * a) = 4 ^ a := by
  have hmul : 2 ^ (2 * a) = (2 ^ 2) ^ a := Nat.pow_mul 2 2 a
  have h4 : (2 : Nat) ^ 2 = 4 := by decide
  rw [hmul, h4]

theorem four_pow_succ (a : Nat) : 4 ^ (a + 1) = 4 * 4 ^ a := by
  rw [Nat.pow_succ, Nat.mul_comm]

theorem two_pow_odd (a : Nat) : 2 ^ (2 * a + 1) = 2 * 4 ^ a := by
  rw [Nat.pow_succ, two_pow_even]
  rw [Nat.mul_comm]

theorem windowK_ge_one (n : Nat) : 1 ≤ windowK n := by
  unfold windowK
  omega

/-- Lemma 9.1's window, for the `k` attached to `n`. -/
theorem windowK_spec (n : Nat) (hn : 2 ≤ n) :
    1 ≤ windowK n ∧
    4 ^ (windowK n - 1) < n ∧
    n ≤ 4 ^ (windowK n) := by
  have hk0 : 1 ≤ windowK n := windowK_ge_one n
  have hn1 : n - 1 ≠ 0 := by omega
  have hlog := (Nat.log2_eq_iff hn1).mp rfl
  have hlog1 : 2 ^ ((n - 1).log2) ≤ n - 1 := hlog.1
  have hlog2 : n - 1 < 2 ^ ((n - 1).log2 + 1) := hlog.2
  have hk : windowK n - 1 = (n - 1).log2 / 2 := by
    unfold windowK
    omega
  have hmod : (n - 1).log2 % 2 = 0 ∨ (n - 1).log2 % 2 = 1 :=
    Nat.mod_two_eq_zero_or_one _
  have hdiv := Nat.div_add_mod (n - 1).log2 2
  refine ⟨hk0, ?_, ?_⟩
  · rcases hmod with h0 | h1
    · have hm' : (n - 1).log2 = 2 * ((n - 1).log2 / 2) := by omega
      have heq : 4 ^ (windowK n - 1) = 2 ^ (n - 1).log2 := by
        rw [hk, ← two_pow_even, ← hm']
      have : 4 ^ (windowK n - 1) ≤ n - 1 := by
        rw [heq]
        exact hlog1
      omega
    · have hm' : (n - 1).log2 = 2 * ((n - 1).log2 / 2) + 1 := by omega
      have heq : 2 * 4 ^ (windowK n - 1) = 2 ^ (n - 1).log2 := by
        rw [hk, ← two_pow_odd, ← hm']
      have : 2 * 4 ^ (windowK n - 1) ≤ n - 1 := by
        rw [heq]
        exact hlog1
      omega
  · rcases hmod with h0 | h1
    · have hm' : (n - 1).log2 = 2 * ((n - 1).log2 / 2) := by omega
      have hpow : 2 ^ ((n - 1).log2 + 1) = 2 * 4 ^ (windowK n - 1) := by
        have : (n - 1).log2 + 1 = 2 * ((n - 1).log2 / 2) + 1 := by omega
        rw [this, two_pow_odd, hk]
      have hn' : n ≤ 2 * 4 ^ (windowK n - 1) := by
        have : n ≤ 2 ^ ((n - 1).log2 + 1) := by omega
        rw [hpow] at this
        exact this
      have hkw : windowK n = (windowK n - 1) + 1 := by omega
      have h4 : 4 ^ (windowK n) = 4 * 4 ^ (windowK n - 1) := by
        rw [hkw]
        exact four_pow_succ (windowK n - 1)
      have : 2 * 4 ^ (windowK n - 1) ≤ 4 ^ (windowK n) := by
        rw [h4]
        omega
      omega
    · have hm' : (n - 1).log2 = 2 * ((n - 1).log2 / 2) + 1 := by omega
      have hk' : windowK n = (n - 1).log2 / 2 + 1 := rfl
      have hpow : 2 ^ ((n - 1).log2 + 1) = 4 ^ (windowK n) := by
        have : (n - 1).log2 + 1 = 2 * ((n - 1).log2 / 2 + 1) := by omega
        rw [this, two_pow_even, hk']
      have : n - 1 < 4 ^ (windowK n) := by
        rw [← hpow]
        exact hlog2
      omega

private theorem nat_le_int {a b : Nat} (h : a ≤ b) : (a : Int) ≤ b :=
  Int.ofNat_le.mpr h

/-- Placement offset of Corollary 7.4. -/
def placeShift (R n : Nat) : Int :=
  if (n : Int) ≤ 2 * (R : Int) + 1 then (1 : Int) else (n : Int) - 2 * (R : Int)

/-- The greedy nested union for `R ∈ I_k`. -/
def greedySet (k R : Nat) : Int → Prop :=
  buildFrom (fun t => t = 0 ∨ t = 1) (greedyDigits k R).tail

/-- Greedy set placed into `[n]`. -/
def placedGreedy (k R n : Nat) : Int → Prop :=
  shift (greedySet k R) (placeShift R n)

/-- Corollary 7.4: an `R`-complete set places into `[n]` on the window
`R+1 ≤ n ≤ 3R+1`. -/
theorem rcomplete_place (A : Int → Prop) (R : Int) (n : Nat)
    (hR : 0 ≤ R)
    (hn1 : R + 1 ≤ (n : Int))
    (hn2 : (n : Int) ≤ 3 * R + 1)
    (hA : IsRComplete R A) :
    MaximalAP3Free n
      (shift A (if (n : Int) ≤ 2 * R + 1 then (1 : Int) else (n : Int) - 2 * R)) := by
  by_cases h : (n : Int) ≤ 2 * R + 1
  · simp [h]
    exact rcomplete_place_left A R n hR hn1 h hA
  · simp [h]
    have hn1' : 2 * R + 1 ≤ (n : Int) := by omega
    exact rcomplete_place_right A R n hR hn1' hn2 hA

theorem placeShift_eq (R n : Nat) :
    placeShift R n =
      (if (n : Int) ≤ 2 * (R : Int) + 1 then (1 : Int) else (n : Int) - 2 * (R : Int)) :=
  rfl

/-- The placed greedy set is maximal 3-AP-free in `[n]`. -/
theorem placedGreedy_maximal (k n : Nat) (hk : 1 ≤ k) (hn2 : 2 ≤ n)
    (hnlo : 4 ^ (k - 1) < n) (hnhi : n ≤ 4 ^ k) :
    MaximalAP3Free n (placedGreedy k (chosenR k n) n) := by
  have hwin := chosenR_window k n hk hn2 hnlo hnhi
  let R := chosenR k n
  have hRcomp : IsRComplete (R : Int) (greedySet k R) :=
    greedy_rcomplete k R hk hwin.1 hwin.2.1
  have hn1 : (R : Int) + 1 ≤ (n : Int) := by
    have h : R + 1 ≤ n := hwin.2.2.1
    have := nat_le_int h
    simpa using this
  have hn3 : (n : Int) ≤ 3 * (R : Int) + 1 := by
    have h : n ≤ 3 * R + 1 := hwin.2.2.2
    have := nat_le_int h
    simpa using this
  have hplace :=
    rcomplete_place (greedySet k R) (R : Int) n
      (Int.natCast_nonneg R) hn1 hn3 hRcomp
  simpa [placedGreedy, greedySet, placeShift_eq] using hplace

/-- Every point of the placed greedy set is a (shifted) subset sum of
the greedy digits, a list of length `2^k`. -/
theorem placedGreedy_support (k n : Nat) (hk : 1 ≤ k) (hn2 : 2 ≤ n)
    (hnlo : 4 ^ (k - 1) < n) (hnhi : n ≤ 4 ^ k)
    {t : Int}
    (ht : placedGreedy k (chosenR k n) n t) :
    ∃ m, Mem (subsetSums (greedyDigits k (chosenR k n))) m ∧
      t = (m : Int) + placeShift (chosenR k n) n := by
  have hwin := chosenR_window k n hk hn2 hnlo hnhi
  let R := chosenR k n
  have ht' : greedySet k R (t - placeShift R n) := ht
  have hsup := greedy_support k R hk hwin.1 hwin.2.1 ht'
  obtain ⟨m, hm, heq⟩ := hsup
  refine ⟨m, hm, ?_⟩
  have hshift : placeShift R n = placeShift (chosenR k n) n := rfl
  omega

/-- `{1}` is maximal in `[1]`. -/
theorem maximal_singleton_one :
    MaximalAP3Free 1 (fun t => t = 1) := by
  refine ⟨?_, ?_, ?_⟩
  · intro t ht
    simp [InIcc1]
    omega
  · intro x y z hx hy hz hAP
    rcases hAP with ⟨_, _, _, _⟩
    omega
  · intro t ht
    simp [InIcc1] at ht
    have : t = 1 := by omega
    subst t
    exact Or.inl rfl

/-- The placed greedy set is the shifted nested-doubling list. -/
theorem placedGreedy_iff (k n : Nat) (hk : 1 ≤ k) (hn2 : 2 ≤ n)
    (hnlo : 4 ^ (k - 1) < n) (hnhi : n ≤ 4 ^ k) (t : Int) :
    placedGreedy k (chosenR k n) n t ↔
      ofList (growFrom [0, 1] (greedyDigits k (chosenR k n)).tail)
        (t - placeShift (chosenR k n) n) := by
  have hwin := chosenR_window k n hk hn2 hnlo hnhi
  have hiff := greedy_set_iff k (chosenR k n) hk hwin.1 hwin.2.1
    (t - placeShift (chosenR k n) n)
  constructor
  · intro ht
    exact hiff.mp ht
  · intro ht
    exact hiff.mpr ht

/-- Theorem 9.2, constructive form: for every `n ≥ 2` there is a
maximal 3-AP-free subset of `[n]` equal to a (shifted) duplicate-free
list of length `2^k`, and `(2^k)^2 < 4n`. -/
theorem sat3_construction (n : Nat) (hn : 2 ≤ n) :
    MaximalAP3Free n (placedGreedy (windowK n) (chosenR (windowK n) n) n) ∧
    (∀ t, placedGreedy (windowK n) (chosenR (windowK n) n) n t ↔
      ofList (growFrom [0, 1]
          (greedyDigits (windowK n) (chosenR (windowK n) n)).tail)
        (t - placeShift (chosenR (windowK n) n) n)) ∧
    Nodup (growFrom [0, 1]
      (greedyDigits (windowK n) (chosenR (windowK n) n)).tail) ∧
    (growFrom [0, 1]
      (greedyDigits (windowK n) (chosenR (windowK n) n)).tail).length =
      2 ^ windowK n ∧
    2 ^ windowK n * 2 ^ windowK n < 4 * n := by
  have hwin := windowK_spec n hn
  have hk := hwin.1
  have hnlo := hwin.2.1
  have hnhi := hwin.2.2
  have hR := chosenR_window (windowK n) n hk hn hnlo hnhi
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact placedGreedy_maximal (windowK n) n hk hn hnlo hnhi
  · intro t
    exact placedGreedy_iff (windowK n) n hk hn hnlo hnhi t
  · exact greedy_growFrom_nodup (windowK n) (chosenR (windowK n) n)
      hk hR.1 hR.2.1
  · exact greedy_growFrom_length (windowK n) (chosenR (windowK n) n)
      hk hR.1 hR.2.1
  · exact two_pow_sq_lt (windowK n) n hk hnlo

/-- Theorem 9.2 as an existence statement: a maximal 3-AP-free subset
of `[n]` of size `2^{windowK n}`, with `(2^k)^2 < 4n`. -/
theorem sat3_upper (n : Nat) (hn : 2 ≤ n) :
    ∃ A : Int → Prop,
      MaximalAP3Free n A ∧
      (∃ P : List Nat, Nodup P ∧ P.length = 2 ^ windowK n ∧
        ∀ t, A t ↔ ofList P (t - placeShift (chosenR (windowK n) n) n)) ∧
      2 ^ windowK n * 2 ^ windowK n < 4 * n := by
  have h := sat3_construction n hn
  refine ⟨placedGreedy (windowK n) (chosenR (windowK n) n) n, h.1, ?_, h.2.2.2.2⟩
  refine ⟨growFrom [0, 1]
      (greedyDigits (windowK n) (chosenR (windowK n) n)).tail, ?_, ?_, ?_⟩
  · exact h.2.2.1
  · exact h.2.2.2.1
  · exact h.2.1

/-- Membership in a `List Int`. -/
def MemInt : List Int → Int → Prop
  | [], _ => False
  | x :: xs, y => y = x ∨ MemInt xs y

def NodupInt : List Int → Prop
  | [] => True
  | x :: xs => ¬ MemInt xs x ∧ NodupInt xs

/-- Shift a list of naturals by an integer offset. -/
def mapAddInt (s : Int) : List Nat → List Int
  | [] => []
  | x :: xs => ((x : Int) + s) :: mapAddInt s xs

theorem mem_mapAddInt (s : Int) :
    ∀ xs y, MemInt (mapAddInt s xs) y ↔ ∃ x, Mem xs x ∧ y = (x : Int) + s
  | [], y => by
      constructor
      · intro h; cases h
      · intro ⟨_, h, _⟩; cases h
  | x :: xs, y => by
      have ih := mem_mapAddInt s xs y
      constructor
      · intro h
        cases h with
        | inl h => exact ⟨x, Or.inl rfl, h⟩
        | inr h =>
          obtain ⟨x', hx, hy⟩ := ih.mp h
          exact ⟨x', Or.inr hx, hy⟩
      · intro ⟨z, hz, hy⟩
        cases hz with
        | inl hz =>
          subst z
          exact Or.inl hy
        | inr hz =>
          exact Or.inr (ih.mpr ⟨z, hz, hy⟩)

theorem ofList_shift (P : List Nat) (s t : Int) :
    ofList P (t - s) ↔ MemInt (mapAddInt s P) t := by
  constructor
  · intro ⟨n, hn, ht⟩
    exact (mem_mapAddInt s P t).mpr ⟨n, hn, by omega⟩
  · intro h
    obtain ⟨n, hn, ht⟩ := (mem_mapAddInt s P t).mp h
    exact ⟨n, hn, by omega⟩

/-- Existence of a maximal 3-AP-free subset of `[n]` of size `k`.
This is the Lean stand-in for `sat_3(n) ≤ k`. -/
def HasMaximalOfSize (n k : Nat) : Prop :=
  ∃ (A : Int → Prop) (P : List Int),
    MaximalAP3Free n A ∧
    NodupInt P ∧
    P.length = k ∧
    ∀ t, A t ↔ MemInt P t

theorem nodup_mapAddInt (s : Int) :
    ∀ xs, Nodup xs → NodupInt (mapAddInt s xs)
  | [], _ => trivial
  | x :: xs, h => by
      constructor
      · intro hmem
        obtain ⟨z, hz, heq⟩ := (mem_mapAddInt s xs ((x : Int) + s)).mp hmem
        have : z = x := by
          have : (z : Int) + s = (x : Int) + s := heq.symm
          omega
        exact h.1 (this ▸ hz)
      · exact nodup_mapAddInt s xs h.2

theorem mapAddInt_length (s : Int) :
    ∀ xs, (mapAddInt s xs).length = xs.length
  | [] => rfl
  | _ :: xs => by
      simp [mapAddInt]
      exact mapAddInt_length s xs

theorem sat3_le_two_pow (n : Nat) (hn : 2 ≤ n) :
    HasMaximalOfSize n (2 ^ windowK n) := by
  obtain ⟨A, hA, ⟨P, hN, hlen, hiff⟩, _⟩ := sat3_upper n hn
  let s := placeShift (chosenR (windowK n) n) n
  refine ⟨A, mapAddInt s P, hA, nodup_mapAddInt s P hN, ?_, ?_⟩
  · rw [mapAddInt_length, hlen]
  · intro t
    constructor
    · intro ht
      exact (ofList_shift P s t).mp ((hiff t).mp ht)
    · intro ht
      exact (hiff t).mpr ((ofList_shift P s t).mpr ht)

/-- Theorem 1.1 / 9.2 for every `n ≥ 1`. -/
theorem sat3_O_sqrt (n : Nat) (hn : 1 ≤ n) :
    (n = 1 ∧ MaximalAP3Free 1 (fun t => t = 1)) ∨
    (2 ≤ n ∧ HasMaximalOfSize n (2 ^ windowK n) ∧
      2 ^ windowK n * 2 ^ windowK n < 4 * n) := by
  cases n with
  | zero => omega
  | succ m =>
    cases m with
    | zero =>
      exact Or.inl ⟨rfl, maximal_singleton_one⟩
    | succ m =>
      have hn2 : 2 ≤ m + 2 := by omega
      exact Or.inr ⟨hn2, sat3_le_two_pow (m + 2) hn2,
        (sat3_construction (m + 2) hn2).2.2.2.2⟩

theorem memInt_iff_mem :
    ∀ P t, MemInt P t ↔ t ∈ P
  | [], t => by
      constructor
      · intro h; cases h
      · intro h; cases h
  | x :: xs, t => by
      have ih := memInt_iff_mem xs t
      constructor
      · intro h
        cases h with
        | inl h => exact List.mem_cons.mpr (Or.inl h)
        | inr h => exact List.mem_cons.mpr (Or.inr (ih.mp h))
      · intro h
        cases (List.mem_cons.mp h) with
        | inl h => exact Or.inl h
        | inr h => exact Or.inr (ih.mpr h)

theorem ofIntList_of_memInt (P : List Int) (t : Int) :
    ofIntList P t ↔ MemInt P t :=
  (memInt_iff_mem P t).symm

theorem MaximalAP3Free_ofIntList (n : Nat) (P : List Int) (A : Int → Prop)
    (hA : MaximalAP3Free n A) (hiff : ∀ t, A t ↔ MemInt P t) :
    MaximalAP3Free n (ofIntList P) := by
  rcases hA with ⟨hsupp, hfree, hcov⟩
  refine ⟨?_, ?_, ?_⟩
  · intro t ht
    exact hsupp t ((hiff t).mpr ((ofIntList_of_memInt P t).mp ht))
  · intro x y z hx hy hz hAP
    exact hfree x y z
      ((hiff x).mpr ((ofIntList_of_memInt P x).mp hx))
      ((hiff y).mpr ((ofIntList_of_memInt P y).mp hy))
      ((hiff z).mpr ((ofIntList_of_memInt P z).mp hz)) hAP
  · intro t ht
    have h := hcov t ht
    cases h with
    | inl hA =>
      exact Or.inl ((ofIntList_of_memInt P t).mpr ((hiff t).mp hA))
    | inr hC =>
      obtain ⟨x, y, hx, hy, hf⟩ := hC
      refine Or.inr ⟨x, y, ?_, ?_, hf⟩
      · exact (ofIntList_of_memInt P x).mpr ((hiff x).mp hx)
      · exact (ofIntList_of_memInt P y).mpr ((hiff y).mp hy)

/-- Proposition 2.2 for `HasMaximalOfSize`: a maximal set of size `k`
forces `n ≤ pairBound k`. -/
theorem HasMaximalOfSize_pairBound (n k : Nat)
    (h : HasMaximalOfSize n k) :
    n ≤ pairBound k := by
  obtain ⟨A, P, hA, _, hlen, hiff⟩ := h
  have hP := MaximalAP3Free_ofIntList n P A hA hiff
  have := pairBound_of_maximal n P hP
  rw [hlen] at this
  exact this

theorem HasMaximalOfSize_quadratic (n k : Nat) (hk : 1 ≤ k)
    (h : HasMaximalOfSize n k) : 2 * n ≤ 3 * k * k :=
  pairBound_quadratic k n hk (HasMaximalOfSize_pairBound n k h)

theorem nodupInt_singleton (x : Int) : NodupInt [x] := by
  constructor
  · intro h; cases h
  · trivial

theorem memInt_singleton (x y : Int) : MemInt [x] y ↔ y = x := by
  constructor
  · intro h
    cases h with
    | inl h => exact h
    | inr h => cases h
  · intro h
    exact Or.inl h

theorem HasMaximalOfSize_one : HasMaximalOfSize 1 1 := by
  refine ⟨fun t => t = 1, [1], maximal_singleton_one, nodupInt_singleton 1, rfl, ?_⟩
  intro t
  constructor
  · intro ht
    exact (memInt_singleton 1 t).mpr ht
  · intro ht
    exact (memInt_singleton 1 t).mp ht

/-- Construction size: `1` at `n=1`, else `2^{windowK n}`. -/
def sat3Upper (n : Nat) : Nat :=
  if n = 1 then 1 else 2 ^ windowK n

/-- Theorem 1.1 as a sandwich for every `n ≥ 1`. -/
theorem sat3_theta (n : Nat) (hn : 1 ≤ n) :
    HasMaximalOfSize n (sat3Upper n) ∧
    (n = 1 ∨ sat3Upper n * sat3Upper n < 4 * n) ∧
    (∀ k, 1 ≤ k → HasMaximalOfSize n k → 2 * n ≤ 3 * k * k) := by
  cases n with
  | zero => omega
  | succ m =>
    cases m with
    | zero =>
      refine ⟨HasMaximalOfSize_one, Or.inl rfl, ?_⟩
      intro k hk h
      exact HasMaximalOfSize_quadratic 1 k hk h
    | succ m =>
      have hn2 : 2 ≤ m + 2 := by omega
      have hne : m + 2 ≠ 1 := by omega
      have hsize : sat3Upper (m + 2) = 2 ^ windowK (m + 2) := by
        simp [sat3Upper, hne]
      refine ⟨?_, ?_, ?_⟩
      · simpa [hsize] using sat3_le_two_pow (m + 2) hn2
      · have hsq := (sat3_construction (m + 2) hn2).2.2.2.2
        refine Or.inr ?_
        simpa [hsize] using hsq
      · intro k hk h
        exact HasMaximalOfSize_quadratic (m + 2) k hk h

/-- If a maximal set of size `k` exists and `pairBound (k-1) < n`,
then every maximal set has size at least `k`. Lean stand-in for
`sat_3(n) = k` when the construction meets the pair bound. -/
theorem HasMaximalOfSize_ge (n k : Nat) (hk : 1 ≤ k)
    (_hex : HasMaximalOfSize n k)
    (hpin : pairBound (k - 1) < n) :
    ∀ m, HasMaximalOfSize n m → k ≤ m := by
  intro m hm
  have hn : n ≤ pairBound m := HasMaximalOfSize_pairBound n m hm
  by_cases hle : k ≤ m
  · exact hle
  · have hmk : m ≤ k - 1 := by omega
    have hmono : pairBound m ≤ pairBound (k - 1) := pairBound_mono hmk
    omega

theorem pairBound_three : pairBound 3 = 12 := by
  simp [pairBound]

theorem nodupInt_S6 : NodupInt [6, 7, 10, 11] := by
  refine ⟨?_, ⟨?_, ⟨?_, ⟨?_, trivial⟩⟩⟩⟩
  · intro h
    rcases h with h | h | h | h
    · omega
    · omega
    · omega
    · cases h
  · intro h
    rcases h with h | h | h
    · omega
    · omega
    · cases h
  · intro h
    rcases h with h | h
    · omega
    · cases h
  · intro h
    cases h

theorem memInt_S6 (t : Int) : S 6 t ↔ MemInt [6, 7, 10, 11] t := by
  constructor
  · intro h
    simp [S, memS] at h
    rcases h with h | h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
  · intro h
    simp [S, memS]
    rcases h with h | h | h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr h))
    · cases h

theorem HasMaximalOfSize_16_4 : HasMaximalOfSize 16 4 :=
  ⟨S 6, [6, 7, 10, 11], S6_maximal_16, nodupInt_S6, rfl, memInt_S6⟩

/-- Corollary 3.3: a maximal 4-point set in `[16]`, and no smaller
maximal set exists (pair bound: `pairBound 3 = 12 < 16`). -/
theorem sat3_exact_16 :
    HasMaximalOfSize 16 4 ∧ ∀ m, HasMaximalOfSize 16 m → 4 ≤ m := by
  refine ⟨HasMaximalOfSize_16_4, ?_⟩
  have hpin : pairBound 3 < 16 := by
    rw [pairBound_three]
    decide
  exact HasMaximalOfSize_ge 16 4 (by decide) HasMaximalOfSize_16_4 hpin

theorem sat3Upper_ge_one (n : Nat) : 1 ≤ sat3Upper n := by
  unfold sat3Upper
  by_cases h : n = 1
  · simp [h]
  · simp [h]
    exact Nat.one_le_pow (windowK n) 2 (by decide)

/-- If the construction size meets the pair-bound pin, every maximal
set has size at least `sat3Upper n`. -/
theorem sat3_exact_when_pin (n : Nat) (hn : 1 ≤ n)
    (hpin : pairBound (sat3Upper n - 1) < n) :
    HasMaximalOfSize n (sat3Upper n) ∧
    ∀ m, HasMaximalOfSize n m → sat3Upper n ≤ m := by
  have hex := (sat3_theta n hn).1
  exact ⟨hex, HasMaximalOfSize_ge n (sat3Upper n) (sat3Upper_ge_one n) hex hpin⟩

theorem sat3Upper_one : sat3Upper 1 = 1 := rfl
theorem sat3Upper_two : sat3Upper 2 = 2 := by decide
theorem sat3Upper_three : sat3Upper 3 = 2 := by decide
theorem sat3Upper_four : sat3Upper 4 = 2 := by decide
theorem sat3Upper_thirteen : sat3Upper 13 = 4 := by decide
theorem sat3Upper_fourteen : sat3Upper 14 = 4 := by decide
theorem sat3Upper_fifteen : sat3Upper 15 = 4 := by decide
theorem sat3Upper_sixteen : sat3Upper 16 = 4 := by decide

theorem sat3_exact_1 :
    HasMaximalOfSize 1 1 ∧ ∀ m, HasMaximalOfSize 1 m → 1 ≤ m := by
  have h := sat3_exact_when_pin 1 (by decide) (by decide)
  simpa [sat3Upper_one] using h

theorem sat3_exact_2 :
    HasMaximalOfSize 2 2 ∧ ∀ m, HasMaximalOfSize 2 m → 2 ≤ m := by
  have h := sat3_exact_when_pin 2 (by decide) (by
    rw [sat3Upper_two]; decide)
  simpa [sat3Upper_two] using h

theorem sat3_exact_3 :
    HasMaximalOfSize 3 2 ∧ ∀ m, HasMaximalOfSize 3 m → 2 ≤ m := by
  have h := sat3_exact_when_pin 3 (by decide) (by
    rw [sat3Upper_three]; decide)
  simpa [sat3Upper_three] using h

theorem sat3_exact_4 :
    HasMaximalOfSize 4 2 ∧ ∀ m, HasMaximalOfSize 4 m → 2 ≤ m := by
  have h := sat3_exact_when_pin 4 (by decide) (by
    rw [sat3Upper_four]; decide)
  simpa [sat3Upper_four] using h

theorem sat3_exact_13 :
    HasMaximalOfSize 13 4 ∧ ∀ m, HasMaximalOfSize 13 m → 4 ≤ m := by
  have h := sat3_exact_when_pin 13 (by decide) (by
    rw [sat3Upper_thirteen]; decide)
  simpa [sat3Upper_thirteen] using h

theorem sat3_exact_14 :
    HasMaximalOfSize 14 4 ∧ ∀ m, HasMaximalOfSize 14 m → 4 ≤ m := by
  have h := sat3_exact_when_pin 14 (by decide) (by
    rw [sat3Upper_fourteen]; decide)
  simpa [sat3Upper_fourteen] using h

theorem sat3_exact_15 :
    HasMaximalOfSize 15 4 ∧ ∀ m, HasMaximalOfSize 15 m → 4 ≤ m := by
  have h := sat3_exact_when_pin 15 (by decide) (by
    rw [sat3Upper_fifteen]; decide)
  simpa [sat3Upper_fifteen] using h

theorem memInt_cons (x : Int) :
    ∀ xs y, MemInt (x :: xs) y ↔ y = x ∨ MemInt xs y
  | _, _ => Iff.rfl

theorem nodupInt_cons {x : Int} {xs : List Int}
    (h : ¬ MemInt xs x) (hN : NodupInt xs) : NodupInt (x :: xs) :=
  ⟨h, hN⟩

theorem memInt_extend_keep (A : Int → Prop) (P : List Int) (n : Nat)
    (hiff : ∀ t, A t ↔ MemInt P t)
    (hC : CompletedBy A ((n : Int) + 1)) (t : Int) :
    extendRight A n t ↔ MemInt P t := by
  constructor
  · intro ht
    cases ht with
    | inl hA => exact (hiff t).mp hA
    | inr hN => exact (hN.2 (by simpa [hN.1] using hC)).elim
  · intro ht
    exact Or.inl ((hiff t).mpr ht)

theorem memInt_extend_add (A : Int → Prop) (P : List Int) (n : Nat)
    (hiff : ∀ t, A t ↔ MemInt P t)
    (hC : ¬ CompletedBy A ((n : Int) + 1)) (t : Int) :
    extendRight A n t ↔ MemInt (((n : Int) + 1) :: P) t := by
  constructor
  · intro ht
    cases ht with
    | inl hA => exact Or.inr ((hiff t).mp hA)
    | inr hN => exact Or.inl hN.1
  · intro ht
    cases ht with
    | inl heq => exact Or.inr ⟨heq, by simpa [heq] using hC⟩
    | inr hP => exact Or.inl ((hiff t).mpr hP)

theorem not_memInt_new (A : Int → Prop) (P : List Int) (n : Nat)
    (hA : MaximalAP3Free n A) (hiff : ∀ t, A t ↔ MemInt P t) :
    ¬ MemInt P ((n : Int) + 1) := by
  intro h
  have : A ((n : Int) + 1) := (hiff _).mpr h
  have hs := hA.1 _ this
  have : (n : Int) + 1 ≤ (n : Int) := hs.2
  omega

/-- Lemma 9.4 for the existence encoding: `sat_3(n+1) ≤ sat_3(n)+1`. -/
theorem HasMaximalOfSize_succ (n k : Nat)
    (h : HasMaximalOfSize n k) :
    HasMaximalOfSize (n + 1) k ∨ HasMaximalOfSize (n + 1) (k + 1) := by
  obtain ⟨A, P, hA, hN, hlen, hiff⟩ := h
  have hExt := maximal_extend_right n A hA
  cases Classical.em (CompletedBy A ((n : Int) + 1)) with
  | inl hC =>
    refine Or.inl ⟨extendRight A n, P, hExt, hN, hlen, ?_⟩
    intro t
    exact memInt_extend_keep A P n hiff hC t
  | inr hC =>
    have hnm : ¬ MemInt P ((n : Int) + 1) := not_memInt_new A P n hA hiff
    refine Or.inr ⟨extendRight A n, ((n : Int) + 1) :: P, hExt,
      nodupInt_cons hnm hN, by simp [hlen], ?_⟩
    intro t
    exact memInt_extend_add A P n hiff hC t

/-- Lean stand-in for `sat_3(n) ≤ k`. -/
def Sat3Le (n k : Nat) : Prop :=
  ∃ m, m ≤ k ∧ HasMaximalOfSize n m

theorem Sat3Le_of_exact (n k : Nat) (h : HasMaximalOfSize n k) :
    Sat3Le n k :=
  ⟨k, Nat.le_refl _, h⟩

theorem Sat3Le_succ (n k : Nat) (h : Sat3Le n k) :
    Sat3Le (n + 1) (k + 1) := by
  obtain ⟨m, hm, hex⟩ := h
  cases HasMaximalOfSize_succ n m hex with
  | inl h' => exact ⟨m, Nat.le_trans hm (Nat.le_succ k), h'⟩
  | inr h' => exact ⟨m + 1, Nat.succ_le_succ hm, h'⟩

theorem Sat3Le_add (n k t : Nat) (h : Sat3Le n k) :
    Sat3Le (n + t) (k + t) := by
  induction t with
  | zero => exact h
  | succ t ih =>
    have h' := Sat3Le_succ (n + t) (k + t) ih
    have hn : n + (t + 1) = n + t + 1 := Nat.add_succ n t
    have hk : k + (t + 1) = k + t + 1 := Nat.add_succ k t
    rw [hn, hk]
    exact h'

theorem Sat3Le_upper (n : Nat) (hn : 1 ≤ n) : Sat3Le n (sat3Upper n) :=
  Sat3Le_of_exact n (sat3Upper n) (sat3_theta n hn).1

theorem four_pow_pred (k : Nat) (hk : 1 ≤ k) :
    4 ^ k = 4 * 4 ^ (k - 1) := by
  cases k with
  | zero => omega
  | succ m =>
    simp [four_pow_succ]

theorem four_pow_ge_two (k : Nat) (hk : 1 ≤ k) : 2 ≤ 4 ^ k := by
  have h1 : 1 ≤ 4 ^ (k - 1) := Nat.one_le_pow (k - 1) 4 (by decide)
  have hpow := four_pow_pred k hk
  omega

theorem pow4_strict (a b : Nat) (h : a < b) : 4 ^ a < 4 ^ b :=
  Nat.pow_lt_pow_right (by decide : 1 < 4) h

/-- `windowK (4^k) = k` for `k ≥ 1`. -/
theorem windowK_four_pow (k : Nat) (hk : 1 ≤ k) : windowK (4 ^ k) = k := by
  have hn : 2 ≤ 4 ^ k := four_pow_ge_two k hk
  have hspec := windowK_spec (4 ^ k) hn
  have hkw : 1 ≤ windowK (4 ^ k) := hspec.1
  have hlo : 4 ^ (windowK (4 ^ k) - 1) < 4 ^ k := hspec.2.1
  have hhi : 4 ^ k ≤ 4 ^ (windowK (4 ^ k)) := hspec.2.2
  have hself : 4 ^ (k - 1) < 4 ^ k := pow4_strict (k - 1) k (by omega)
  by_cases hlt : windowK (4 ^ k) < k
  · have : 4 ^ (windowK (4 ^ k)) < 4 ^ k := pow4_strict _ _ hlt
    omega
  · by_cases hgt : k < windowK (4 ^ k)
    · have : 4 ^ k ≤ 4 ^ (windowK (4 ^ k) - 1) :=
        Nat.pow_le_pow_right (by decide : 0 < 4) (by omega)
      omega
    · omega

theorem sat3Upper_four_pow (k : Nat) (hk : 1 ≤ k) :
    sat3Upper (4 ^ k) = 2 ^ k := by
  have hne : 4 ^ k ≠ 1 := by
    have : 2 ≤ 4 ^ k := four_pow_ge_two k hk
    omega
  simp [sat3Upper, hne, windowK_four_pow k hk]

/-- Interpolation: from a maximal set of size `2^k` in `[4^k]`,
adjoin at most `t` endpoints to reach `[4^k + t]`. -/
theorem sat3_interp (k t : Nat) (hk : 1 ≤ k) :
    Sat3Le (4 ^ k + t) (2 ^ k + t) := by
  have hn : 2 ≤ 4 ^ k := four_pow_ge_two k hk
  have hex : HasMaximalOfSize (4 ^ k) (2 ^ k) := by
    have h := sat3_le_two_pow (4 ^ k) hn
    simpa [windowK_four_pow k hk] using h
  exact Sat3Le_add (4 ^ k) (2 ^ k) t (Sat3Le_of_exact _ _ hex)

/-- The jump after `n=4`: `sat_3(5) ≤ 3`. -/
theorem sat3_le_five : Sat3Le 5 3 := by
  have h := sat3_interp 1 1 (by decide)
  simpa using h

/-- The jump after `n=16`: `sat_3(17) ≤ 5`. -/
theorem sat3_le_seventeen : Sat3Le 17 5 := by
  have h := sat3_interp 2 1 (by decide)
  simpa using h

theorem pairBound_two : pairBound 2 = 5 := by
  simp [pairBound]

theorem inIcc1_five {t : Int} (h : InIcc1 5 t) :
    t = 1 ∨ t = 2 ∨ t = 3 ∨ t = 4 ∨ t = 5 := by
  simp [InIcc1] at h
  omega

theorem not_formsAP3_of (a b t : Int)
    (h : ¬ (2 * a = b + t ∨ 2 * b = a + t ∨ 2 * t = a + b)) :
    ¬ FormsAP3 a b t := by
  intro hf
  exact h hf.2.2.2

/-- No two-point set is maximal in `[5]`. The pair bound only forces
size at least 2 (`pairBound 2 = 5`); the missing third is by cases. -/
theorem not_maximal_pair_five (a b : Int)
    (ha : InIcc1 5 a) (hb : InIcc1 5 b) (hne : a ≠ b) :
    ¬ MaximalAP3Free 5 (fun t => t = a ∨ t = b) := by
  intro h
  have hcov := h.2.2
  have ha' := inIcc1_five ha
  have hb' := inIcc1_five hb
  have miss : ∃ t, InIcc1 5 t ∧ t ≠ a ∧ t ≠ b ∧ ¬ FormsAP3 a b t := by
    rcases ha' with ha1 | ha2 | ha3 | ha4 | ha5
      <;> rcases hb' with hb1 | hb2 | hb3 | hb4 | hb5
    · exact (hne (ha1.trans hb1.symm)).elim
    · subst a; subst b
      refine ⟨4, by simp [InIcc1], by omega, by omega, not_formsAP3_of 1 2 4 (by omega)⟩
    · subst a; subst b
      refine ⟨4, by simp [InIcc1], by omega, by omega, not_formsAP3_of 1 3 4 (by omega)⟩
    · subst a; subst b
      refine ⟨2, by simp [InIcc1], by omega, by omega, not_formsAP3_of 1 4 2 (by omega)⟩
    · subst a; subst b
      refine ⟨2, by simp [InIcc1], by omega, by omega, not_formsAP3_of 1 5 2 (by omega)⟩
    · subst a; subst b
      refine ⟨4, by simp [InIcc1], by omega, by omega, not_formsAP3_of 2 1 4 (by omega)⟩
    · exact (hne (ha2.trans hb2.symm)).elim
    · subst a; subst b
      refine ⟨5, by simp [InIcc1], by omega, by omega, not_formsAP3_of 2 3 5 (by omega)⟩
    · subst a; subst b
      refine ⟨1, by simp [InIcc1], by omega, by omega, not_formsAP3_of 2 4 1 (by omega)⟩
    · subst a; subst b
      refine ⟨1, by simp [InIcc1], by omega, by omega, not_formsAP3_of 2 5 1 (by omega)⟩
    · subst a; subst b
      refine ⟨4, by simp [InIcc1], by omega, by omega, not_formsAP3_of 3 1 4 (by omega)⟩
    · subst a; subst b
      refine ⟨5, by simp [InIcc1], by omega, by omega, not_formsAP3_of 3 2 5 (by omega)⟩
    · exact (hne (ha3.trans hb3.symm)).elim
    · subst a; subst b
      refine ⟨1, by simp [InIcc1], by omega, by omega, not_formsAP3_of 3 4 1 (by omega)⟩
    · subst a; subst b
      refine ⟨2, by simp [InIcc1], by omega, by omega, not_formsAP3_of 3 5 2 (by omega)⟩
    · subst a; subst b
      refine ⟨2, by simp [InIcc1], by omega, by omega, not_formsAP3_of 4 1 2 (by omega)⟩
    · subst a; subst b
      refine ⟨1, by simp [InIcc1], by omega, by omega, not_formsAP3_of 4 2 1 (by omega)⟩
    · subst a; subst b
      refine ⟨1, by simp [InIcc1], by omega, by omega, not_formsAP3_of 4 3 1 (by omega)⟩
    · exact (hne (ha4.trans hb4.symm)).elim
    · subst a; subst b
      refine ⟨1, by simp [InIcc1], by omega, by omega, not_formsAP3_of 4 5 1 (by omega)⟩
    · subst a; subst b
      refine ⟨2, by simp [InIcc1], by omega, by omega, not_formsAP3_of 5 1 2 (by omega)⟩
    · subst a; subst b
      refine ⟨1, by simp [InIcc1], by omega, by omega, not_formsAP3_of 5 2 1 (by omega)⟩
    · subst a; subst b
      refine ⟨2, by simp [InIcc1], by omega, by omega, not_formsAP3_of 5 3 2 (by omega)⟩
    · subst a; subst b
      refine ⟨1, by simp [InIcc1], by omega, by omega, not_formsAP3_of 5 4 1 (by omega)⟩
    · exact (hne (ha5.trans hb5.symm)).elim
  obtain ⟨t, ht, hta, htb, hF⟩ := miss
  have hcell := hcov t ht
  cases hcell with
  | inl hA =>
    cases hA with
    | inl h => exact hta h
    | inr h => exact htb h
  | inr hC =>
    obtain ⟨x, y, hx, hy, hf⟩ := hC
    have hx' : x = a ∨ x = b := hx
    have hy' : y = a ∨ y = b := hy
    rcases hx' with hx | hx <;> rcases hy' with hy | hy
    · exact hf.1 (hx.trans hy.symm)
    · subst x; subst y
      exact hF hf
    · subst x; subst y
      have : FormsAP3 a b t := by
        rcases hf with ⟨hxy, hyt, hxt, hor⟩
        refine ⟨hxy.symm, hxt, hyt, ?_⟩
        rcases hor with h | h | h
        · exact Or.inr (Or.inl (by omega))
        · exact Or.inl (by omega)
        · exact Or.inr (Or.inr (by omega))
      exact hF this
    · exact hf.1 (hx.trans hy.symm)

theorem nodupInt_length_two (P : List Int) (hN : NodupInt P)
    (hlen : P.length = 2) :
    ∃ x y, P = [x, y] ∧ x ≠ y := by
  match P with
  | [] => cases hlen
  | [x] => cases hlen
  | [x, y] =>
    refine ⟨x, y, rfl, ?_⟩
    intro h
    subst y
    exact hN.1 (Or.inl rfl)
  | _ :: _ :: _ :: _ =>
    cases hlen

theorem memInt_pair (x y t : Int) :
    MemInt [x, y] t ↔ t = x ∨ t = y := by
  constructor
  · intro h
    rcases h with h | h | h
    · exact Or.inl h
    · exact Or.inr h
    · cases h
  · intro h
    rcases h with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)

theorem MaximalAP3Free_pair (A : Int → Prop) (x y : Int)
    (hA : MaximalAP3Free 5 A)
    (hiff : ∀ t, A t ↔ t = x ∨ t = y) :
    MaximalAP3Free 5 (fun t => t = x ∨ t = y) := by
  rcases hA with ⟨hsupp, hfree, hcov⟩
  refine ⟨?_, ?_, ?_⟩
  · intro t ht
    exact hsupp t ((hiff t).mpr ht)
  · intro u v w hu hv hw hAP
    exact hfree u v w ((hiff u).mpr hu) ((hiff v).mpr hv) ((hiff w).mpr hw) hAP
  · intro t ht
    have h := hcov t ht
    cases h with
    | inl hA => exact Or.inl ((hiff t).mp hA)
    | inr hC =>
      obtain ⟨p, q, hp, hq, hf⟩ := hC
      exact Or.inr ⟨p, q, (hiff p).mp hp, (hiff q).mp hq, hf⟩

theorem not_HasMaximalOfSize_5_2 : ¬ HasMaximalOfSize 5 2 := by
  intro h
  obtain ⟨A, P, hA, hN, hlen, hiff⟩ := h
  obtain ⟨x, y, hP, hne⟩ := nodupInt_length_two P hN hlen
  subst P
  have hiff' : ∀ t, A t ↔ t = x ∨ t = y := by
    intro t
    constructor
    · intro ht
      exact (memInt_pair x y t).mp ((hiff t).mp ht)
    · intro ht
      exact (hiff t).mpr ((memInt_pair x y t).mpr ht)
  have hx : A x := (hiff' x).mpr (Or.inl rfl)
  have hy : A y := (hiff' y).mpr (Or.inr rfl)
  have hpair := MaximalAP3Free_pair A x y hA hiff'
  exact not_maximal_pair_five x y (hA.1 x hx) (hA.1 y hy) hne hpair

theorem nodupInt_134 : NodupInt [1, 3, 4] := by
  refine ⟨?_, ⟨?_, ⟨?_, trivial⟩⟩⟩
  · intro h
    rcases h with h | h | h
    · omega
    · omega
    · cases h
  · intro h
    rcases h with h | h
    · omega
    · cases h
  · intro h
    cases h

theorem memInt_134 (t : Int) :
    ofIntList [1, 3, 4] t ↔ MemInt [1, 3, 4] t :=
  ofIntList_of_memInt [1, 3, 4] t

theorem HasMaximalOfSize_5_3 : HasMaximalOfSize 5 3 :=
  ⟨ofIntList [1, 3, 4], [1, 3, 4], maximal_of_cert_n5, nodupInt_134, rfl,
    memInt_134⟩

/-- `sat_3(5) = 3`: a maximal 3-point set exists, and no 2-point
maximal set exists. The pair bound only forces size at least 2. -/
theorem sat3_exact_5 :
    HasMaximalOfSize 5 3 ∧ ¬ HasMaximalOfSize 5 2 ∧
    ∀ m, HasMaximalOfSize 5 m → 3 ≤ m := by
  refine ⟨HasMaximalOfSize_5_3, not_HasMaximalOfSize_5_2, ?_⟩
  intro m hm
  have hn : 5 ≤ pairBound m := HasMaximalOfSize_pairBound 5 m hm
  have h2 : pairBound 2 = 5 := pairBound_two
  by_cases hle : 3 ≤ m
  · exact hle
  · have : m ≤ 2 := by omega
    have : m = 0 ∨ m = 1 ∨ m = 2 := by omega
    rcases this with hm0 | hm1 | hm2
    · subst m
      simp [pairBound] at hn
    · subst m
      have : pairBound 1 = 1 := by simp [pairBound]
      omega
    · subst m
      exact (not_HasMaximalOfSize_5_2 hm).elim

theorem pairBound_zero_eq : pairBound 0 = 0 := by
  simp [pairBound]

theorem not_HasMaximalOfSize_zero (n : Nat) (hn : 1 ≤ n) :
    ¬ HasMaximalOfSize n 0 := by
  intro h
  have := HasMaximalOfSize_pairBound n 0 h
  rw [pairBound_zero_eq] at this
  omega

/-- A nonempty family of sizes bounded by `N` has a least element. -/
theorem exists_least_maximal (n N : Nat) (h : HasMaximalOfSize n N) :
    ∃ k, k ≤ N ∧ HasMaximalOfSize n k ∧ ∀ m, HasMaximalOfSize n m → k ≤ m := by
  induction N using Nat.strongRecOn with
  | ind N ih =>
    cases Classical.em (∃ m, m < N ∧ HasMaximalOfSize n m) with
    | inl hex =>
      obtain ⟨m, hm, hM⟩ := hex
      obtain ⟨k, hkN, hkM, hmin⟩ := ih m hm hM
      exact ⟨k, Nat.le_trans hkN (Nat.le_of_lt hm), hkM, hmin⟩
    | inr hnone =>
      refine ⟨N, Nat.le_refl _, h, ?_⟩
      intro m hm
      by_cases hle : N ≤ m
      · exact hle
      · have : m < N := Nat.lt_of_not_ge hle
        exact (hnone ⟨m, this, hm⟩).elim

/-- The numerical function `sat_3(n)`: least size of a maximal set. -/
theorem sat3_min (n : Nat) (hn : 1 ≤ n) :
    ∃ k, HasMaximalOfSize n k ∧
      (∀ m, HasMaximalOfSize n m → k ≤ m) ∧
      k ≤ sat3Upper n ∧
      1 ≤ k ∧
      2 * n ≤ 3 * k * k := by
  have hU := (sat3_theta n hn).1
  obtain ⟨k, hkU, hkM, hmin⟩ := exists_least_maximal n (sat3Upper n) hU
  have hk1 : 1 ≤ k := by
    by_cases h0 : k = 0
    · subst k
      exact (not_HasMaximalOfSize_zero n hn hkM).elim
    · omega
  exact ⟨k, hkM, hmin, hkU, hk1, HasMaximalOfSize_quadratic n k hk1 hkM⟩

/-- Theorem 1.1 for the numerical least size: it is at most `sat3Upper n`,
and `(least)^2 < 4n` when `n ≥ 2`. -/
theorem sat3_min_O_sqrt (n : Nat) (hn : 1 ≤ n) :
    ∃ k, HasMaximalOfSize n k ∧
      (∀ m, HasMaximalOfSize n m → k ≤ m) ∧
      k ≤ sat3Upper n ∧
      2 * n ≤ 3 * k * k ∧
      (n = 1 ∨ k * k < 4 * n) := by
  obtain ⟨k, hkM, hmin, hkU, hk1, hquad⟩ := sat3_min n hn
  refine ⟨k, hkM, hmin, hkU, hquad, ?_⟩
  cases n with
  | zero => omega
  | succ m =>
    cases m with
    | zero => exact Or.inl rfl
    | succ m =>
      have hsq := (sat3_theta (m + 2) (by omega)).2.1
      have : sat3Upper (m + 2) * sat3Upper (m + 2) < 4 * (m + 2) := by
        cases hsq with
        | inl h =>
          have : m + 2 = 1 := h
          omega
        | inr h => exact h
      have hk2 : k * k ≤ sat3Upper (m + 2) * sat3Upper (m + 2) :=
        Nat.mul_le_mul hkU hkU
      exact Or.inr (Nat.lt_of_le_of_lt hk2 this)

/-- The numerical saturation number: least size of a maximal
3-AP-free subset of `[n]`. Noncomputable; existence is `sat3_min`. -/
noncomputable def sat3 (n : Nat) (hn : 1 ≤ n := by omega) : Nat :=
  Classical.choose (sat3_min n hn)

theorem sat3_spec (n : Nat) (hn : 1 ≤ n) :
    HasMaximalOfSize n (sat3 n hn) ∧
    (∀ m, HasMaximalOfSize n m → sat3 n hn ≤ m) ∧
    sat3 n hn ≤ sat3Upper n ∧
    1 ≤ sat3 n hn ∧
    2 * n ≤ 3 * sat3 n hn * sat3 n hn :=
  Classical.choose_spec (sat3_min n hn)

theorem sat3_le_upper (n : Nat) (hn : 1 ≤ n) :
    sat3 n hn ≤ sat3Upper n :=
  (sat3_spec n hn).2.2.1

theorem sat3_quadratic (n : Nat) (hn : 1 ≤ n) :
    2 * n ≤ 3 * sat3 n hn * sat3 n hn :=
  (sat3_spec n hn).2.2.2.2

theorem sat3_sq_lt (n : Nat) (hn : 2 ≤ n) :
    sat3 n (Nat.le_trans (by decide : 1 ≤ 2) hn) *
      sat3 n (Nat.le_trans (by decide : 1 ≤ 2) hn) < 4 * n := by
  have h := sat3_min_O_sqrt n (Nat.le_trans (by decide : 1 ≤ 2) hn)
  obtain ⟨k, hkM, hmin, hkU, _, hsq⟩ := h
  have hk : sat3 n (Nat.le_trans (by decide : 1 ≤ 2) hn) = k := by
    have hspec := sat3_spec n (Nat.le_trans (by decide : 1 ≤ 2) hn)
    have h1 := hspec.2.1 k hkM
    have h2 := hmin (sat3 n _) hspec.1
    omega
  have : n ≠ 1 := by omega
  cases hsq with
  | inl h => exact (this h).elim
  | inr h =>
    simpa [hk] using h

/-- Lemma 9.4 for the numerical function. -/
theorem sat3_succ_le (n : Nat) (hn : 1 ≤ n) :
    sat3 (n + 1) (Nat.le_succ_of_le hn) ≤ sat3 n hn + 1 := by
  have hN := sat3_spec n hn
  have hS := sat3_spec (n + 1) (Nat.le_succ_of_le hn)
  have hstep := HasMaximalOfSize_succ n (sat3 n hn) hN.1
  cases hstep with
  | inl hsame =>
    have := hS.2.1 (sat3 n hn) hsame
    omega
  | inr hplus =>
    have := hS.2.1 (sat3 n hn + 1) hplus
    exact this

/-- Theorem 1.1 as a statement about `sat3 n`. -/
theorem sat3_theta_num (n : Nat) (hn : 1 ≤ n) :
    sat3 n hn ≤ sat3Upper n ∧
    2 * n ≤ 3 * sat3 n hn * sat3 n hn ∧
    (n = 1 ∨ sat3 n hn * sat3 n hn < 4 * n) := by
  refine ⟨sat3_le_upper n hn, sat3_quadratic n hn, ?_⟩
  cases n with
  | zero => omega
  | succ m =>
    cases m with
    | zero => exact Or.inl rfl
    | succ m =>
      exact Or.inr (sat3_sq_lt (m + 2) (by omega))

theorem sat3_eq_of_pin (n : Nat) (hn : 1 ≤ n)
    (hpin : pairBound (sat3Upper n - 1) < n) :
    sat3 n hn = sat3Upper n := by
  have h := sat3_exact_when_pin n hn hpin
  have hspec := sat3_spec n hn
  have hle := hspec.2.2.1
  have hge := h.2 (sat3 n hn) hspec.1
  omega

theorem sat3_eq_one : sat3 1 (by decide) = 1 := by
  have := sat3_eq_of_pin 1 (by decide) (by decide)
  simpa [sat3Upper_one] using this

theorem sat3_eq_two : sat3 2 (by decide) = 2 := by
  have := sat3_eq_of_pin 2 (by decide) (by
    rw [sat3Upper_two]; decide)
  simpa [sat3Upper_two] using this

theorem sat3_eq_three : sat3 3 (by decide) = 2 := by
  have := sat3_eq_of_pin 3 (by decide) (by
    rw [sat3Upper_three]; decide)
  simpa [sat3Upper_three] using this

theorem sat3_eq_four : sat3 4 (by decide) = 2 := by
  have := sat3_eq_of_pin 4 (by decide) (by
    rw [sat3Upper_four]; decide)
  simpa [sat3Upper_four] using this

theorem sat3_eq_five : sat3 5 (by decide) = 3 := by
  have hspec := sat3_spec 5 (by decide)
  have hge : 3 ≤ sat3 5 (by decide) :=
    sat3_exact_5.2.2 (sat3 5 (by decide)) hspec.1
  have hle : sat3 5 (by decide) ≤ 3 := by
    have hU := sat3_le_five
    obtain ⟨m, hm, hex⟩ := hU
    have := hspec.2.1 m hex
    omega
  omega

theorem sat3_eq_sixteen : sat3 16 (by decide) = 4 := by
  have := sat3_eq_of_pin 16 (by decide) (by
    rw [sat3Upper_sixteen]; decide)
  simpa [sat3Upper_sixteen] using this

theorem sat3_eq_thirteen : sat3 13 (by decide) = 4 := by
  have := sat3_eq_of_pin 13 (by decide) (by
    rw [sat3Upper_thirteen]; decide)
  simpa [sat3Upper_thirteen] using this

theorem sat3_eq_fourteen : sat3 14 (by decide) = 4 := by
  have := sat3_eq_of_pin 14 (by decide) (by
    rw [sat3Upper_fourteen]; decide)
  simpa [sat3Upper_fourteen] using this

theorem sat3_eq_fifteen : sat3 15 (by decide) = 4 := by
  have := sat3_eq_of_pin 15 (by decide) (by
    rw [sat3Upper_fifteen]; decide)
  simpa [sat3Upper_fifteen] using this

/-- Corollary 9.5 for the numerical function. -/
theorem sat3_le_interp (k t : Nat) (hk : 1 ≤ k) :
    sat3 (4 ^ k + t)
      (Nat.le_trans (Nat.le_of_succ_le (four_pow_ge_two k hk))
        (Nat.le_add_right (4 ^ k) t)) ≤ 2 ^ k + t := by
  have hI := sat3_interp k t hk
  obtain ⟨m, hm, hex⟩ := hI
  have hn : 1 ≤ 4 ^ k + t :=
    Nat.le_trans (Nat.le_of_succ_le (four_pow_ge_two k hk))
      (Nat.le_add_right (4 ^ k) t)
  have hspec := sat3_spec (4 ^ k + t) hn
  have := hspec.2.1 m hex
  omega

theorem sat3_le_seventeen_num : sat3 17 (by decide) ≤ 5 := by
  have h := sat3_le_interp 2 1 (by decide)
  simpa using h

theorem nodupInt_length_three (P : List Int) (hN : NodupInt P)
    (hlen : P.length = 3) :
    ∃ x y z, P = [x, y, z] := by
  match P with
  | [] => cases hlen
  | [_] => cases hlen
  | [_, _] => cases hlen
  | [x, y, z] => exact ⟨x, y, z, rfl⟩
  | _ :: _ :: _ :: _ :: _ => cases hlen

theorem not_HasMaximalOfSize_3_of_any (n : Nat)
    (hfalse : anyMaximal3 n = false) :
    ¬ HasMaximalOfSize n 3 := by
  intro h
  obtain ⟨A, P, hA, hN, hlen, hiff⟩ := h
  obtain ⟨x, y, z, hP⟩ := nodupInt_length_three P hN hlen
  subst P
  have hlist := MaximalAP3Free_ofIntList n [x, y, z] A hA hiff
  have := anyMaximal3_of_list n x y z hlist
  exact Bool.false_ne_true (hfalse.symm.trans this)

theorem pairBound_two_eq : pairBound 2 = 5 := pairBound_two

theorem not_HasMaximalOfSize_2_of_gt_five (n : Nat) (hn : 6 ≤ n) :
    ¬ HasMaximalOfSize n 2 := by
  intro h
  have := HasMaximalOfSize_pairBound n 2 h
  have : pairBound 2 = 5 := pairBound_two_eq
  omega

theorem HasMaximalOfSize_6_4 : HasMaximalOfSize 6 4 := by
  refine ⟨ofIntList [1, 2, 4, 5], [1, 2, 4, 5], maximal_of_cert_n6, ?_, rfl, ?_⟩
  · -- nodup of the 4-point block
    refine ⟨?_, ⟨?_, ⟨?_, ⟨?_, trivial⟩⟩⟩⟩
    · intro h
      rcases h with h | h | h | h
      · omega
      · omega
      · omega
      · cases h
    · intro h
      rcases h with h | h | h
      · omega
      · omega
      · cases h
    · intro h
      rcases h with h | h
      · omega
      · cases h
    · intro h
      cases h
  · intro t
    exact ofIntList_of_memInt [1, 2, 4, 5] t

theorem sat3Upper_six : sat3Upper 6 = 4 := by decide

theorem sat3_eq_of_no_small (n : Nat) (hn : 1 ≤ n) (hn6 : 6 ≤ n)
    (hU : sat3Upper n = 4)
    (h2 : ¬ HasMaximalOfSize n 2)
    (h3 : ¬ HasMaximalOfSize n 3)
    (_h4 : HasMaximalOfSize n 4) :
    sat3 n hn = 4 := by
  have hspec := sat3_spec n hn
  have hle : sat3 n hn ≤ 4 := by
    have := hspec.2.2.1
    omega
  have hge : 4 ≤ sat3 n hn := by
    have hk := hspec.2.2.2.1
    have hcases : sat3 n hn = 1 ∨ sat3 n hn = 2 ∨ sat3 n hn = 3 ∨ 4 ≤ sat3 n hn := by omega
    rcases hcases with h1 | h2' | h3' | h4'
    · have hsz : HasMaximalOfSize n 1 := by simpa [h1] using hspec.1
      have hpb := HasMaximalOfSize_pairBound n 1 hsz
      have : pairBound 1 = 1 := by simp [pairBound]
      omega
    · have hsz : HasMaximalOfSize n 2 := by simpa [h2'] using hspec.1
      exact (h2 hsz).elim
    · have hsz : HasMaximalOfSize n 3 := by simpa [h3'] using hspec.1
      exact (h3 hsz).elim
    · exact h4'
  omega

theorem sat3_eq_six : sat3 6 (by decide) = 4 :=
  sat3_eq_of_no_small 6 (by decide) (by decide) sat3Upper_six
    (not_HasMaximalOfSize_2_of_gt_five 6 (by decide))
    (not_HasMaximalOfSize_3_of_any 6 anyMaximal3_6)
    HasMaximalOfSize_6_4

theorem sat3Upper_seven : sat3Upper 7 = 4 := by decide
theorem sat3Upper_eight : sat3Upper 8 = 4 := by decide
theorem sat3Upper_nine : sat3Upper 9 = 4 := by decide
theorem sat3Upper_ten : sat3Upper 10 = 4 := by decide
theorem sat3Upper_eleven : sat3Upper 11 = 4 := by decide
theorem sat3Upper_twelve : sat3Upper 12 = 4 := by decide

theorem HasMaximalOfSize_n_4_of_upper (n : Nat) (hn : 2 ≤ n)
    (hU : sat3Upper n = 4) : HasMaximalOfSize n 4 := by
  have h := sat3_le_two_pow n hn
  have : 2 ^ windowK n = 4 := by
    have hne : n ≠ 1 := by omega
    simp [sat3Upper, hne] at hU
    exact hU
  simpa [this] using h

theorem sat3_eq_seven : sat3 7 (by decide) = 4 :=
  sat3_eq_of_no_small 7 (by decide) (by decide) sat3Upper_seven
    (not_HasMaximalOfSize_2_of_gt_five 7 (by decide))
    (not_HasMaximalOfSize_3_of_any 7 anyMaximal3_7)
    (HasMaximalOfSize_n_4_of_upper 7 (by decide) sat3Upper_seven)

theorem sat3_eq_eight : sat3 8 (by decide) = 4 :=
  sat3_eq_of_no_small 8 (by decide) (by decide) sat3Upper_eight
    (not_HasMaximalOfSize_2_of_gt_five 8 (by decide))
    (not_HasMaximalOfSize_3_of_any 8 anyMaximal3_8)
    (HasMaximalOfSize_n_4_of_upper 8 (by decide) sat3Upper_eight)

theorem sat3_eq_nine : sat3 9 (by decide) = 4 :=
  sat3_eq_of_no_small 9 (by decide) (by decide) sat3Upper_nine
    (not_HasMaximalOfSize_2_of_gt_five 9 (by decide))
    (not_HasMaximalOfSize_3_of_any 9 anyMaximal3_9)
    (HasMaximalOfSize_n_4_of_upper 9 (by decide) sat3Upper_nine)

theorem sat3_eq_ten : sat3 10 (by decide) = 4 :=
  sat3_eq_of_no_small 10 (by decide) (by decide) sat3Upper_ten
    (not_HasMaximalOfSize_2_of_gt_five 10 (by decide))
    (not_HasMaximalOfSize_3_of_any 10 anyMaximal3_10)
    (HasMaximalOfSize_n_4_of_upper 10 (by decide) sat3Upper_ten)

theorem sat3_eq_eleven : sat3 11 (by decide) = 4 :=
  sat3_eq_of_no_small 11 (by decide) (by decide) sat3Upper_eleven
    (not_HasMaximalOfSize_2_of_gt_five 11 (by decide))
    (not_HasMaximalOfSize_3_of_any 11 anyMaximal3_11)
    (HasMaximalOfSize_n_4_of_upper 11 (by decide) sat3Upper_eleven)

theorem sat3_eq_twelve : sat3 12 (by decide) = 4 :=
  sat3_eq_of_no_small 12 (by decide) (by decide) sat3Upper_twelve
    (not_HasMaximalOfSize_2_of_gt_five 12 (by decide))
    (not_HasMaximalOfSize_3_of_any 12 anyMaximal3_12)
    (HasMaximalOfSize_n_4_of_upper 12 (by decide) sat3Upper_twelve)

theorem nodupInt_length_four (P : List Int) (hN : NodupInt P)
    (hlen : P.length = 4) :
    ∃ w x y z, P = [w, x, y, z] := by
  match P with
  | [] => cases hlen
  | [_] => cases hlen
  | [_, _] => cases hlen
  | [_, _, _] => cases hlen
  | [w, x, y, z] => exact ⟨w, x, y, z, rfl⟩
  | _ :: _ :: _ :: _ :: _ :: _ => cases hlen

theorem not_HasMaximalOfSize_4_of_any (n : Nat)
    (hfalse : anyMaximal4 n = false) :
    ¬ HasMaximalOfSize n 4 := by
  intro h
  obtain ⟨A, P, hA, hN, hlen, hiff⟩ := h
  obtain ⟨w, x, y, z, hP⟩ := nodupInt_length_four P hN hlen
  subst P
  have hlist := MaximalAP3Free_ofIntList n [w, x, y, z] A hA hiff
  have := anyMaximal4_of_list n w x y z hlist
  exact Bool.false_ne_true (hfalse.symm.trans this)

theorem pairBound_three_eq : pairBound 3 = 12 := pairBound_three

theorem not_HasMaximalOfSize_3_of_gt_twelve (n : Nat) (hn : 13 ≤ n) :
    ¬ HasMaximalOfSize n 3 := by
  intro h
  have := HasMaximalOfSize_pairBound n 3 h
  have : pairBound 3 = 12 := pairBound_three_eq
  omega

theorem HasMaximalOfSize_17_5 : HasMaximalOfSize 17 5 := by
  refine ⟨ofIntList [1, 7, 8, 11, 12], [1, 7, 8, 11, 12],
    maximal_of_cert_n17, ?_, rfl, ofIntList_of_memInt [1, 7, 8, 11, 12]⟩
  refine ⟨?_, ⟨?_, ⟨?_, ⟨?_, ⟨?_, trivial⟩⟩⟩⟩⟩
  · intro h
    rcases h with h | h | h | h | h
    · omega
    · omega
    · omega
    · omega
    · cases h
  · intro h
    rcases h with h | h | h | h
    · omega
    · omega
    · omega
    · cases h
  · intro h
    rcases h with h | h | h
    · omega
    · omega
    · cases h
  · intro h
    rcases h with h | h
    · omega
    · cases h
  · intro h
    cases h

theorem sat3_eq_seventeen : sat3 17 (by decide) = 5 := by
  have hspec := sat3_spec 17 (by decide)
  have hle : sat3 17 (by decide) ≤ 5 := sat3_le_seventeen_num
  have hge : 5 ≤ sat3 17 (by decide) := by
    have hk := hspec.2.2.2.1
    have hcases :
        sat3 17 (by decide) = 1 ∨ sat3 17 (by decide) = 2 ∨
        sat3 17 (by decide) = 3 ∨ sat3 17 (by decide) = 4 ∨
        5 ≤ sat3 17 (by decide) := by omega
    rcases hcases with h1 | h2 | h3 | h4 | h5
    · have hsz : HasMaximalOfSize 17 1 := by simpa [h1] using hspec.1
      have hpb := HasMaximalOfSize_pairBound 17 1 hsz
      have : pairBound 1 = 1 := by simp [pairBound]
      omega
    · have hsz : HasMaximalOfSize 17 2 := by simpa [h2] using hspec.1
      exact (not_HasMaximalOfSize_2_of_gt_five 17 (by decide) hsz).elim
    · have hsz : HasMaximalOfSize 17 3 := by simpa [h3] using hspec.1
      exact (not_HasMaximalOfSize_3_of_gt_twelve 17 (by decide) hsz).elim
    · have hsz : HasMaximalOfSize 17 4 := by simpa [h4] using hspec.1
      exact (not_HasMaximalOfSize_4_of_any 17 anyMaximal4_17 hsz).elim
    · exact h5
  omega

end Sat3
