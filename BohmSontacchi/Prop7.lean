/-
  Bohm-Sontacchi 1978 -- Proposition 7

  PROPOSITION 7. For all x in Z: x is in U if and only if
  there exists (v_0, v_1, ..., v_m) in N^{m+1} with v_{i-1} < v_i for 1 <= i < m
  such that

    (**) x = (2^{v_m} - sum_{k=0}^{m-1} 3^{m-k-1} * 2^{v_k}) / 3^m

  where U = {x in Z | exists n in P : u^n(x) = 1}.

  In particular, 1, 5, 21, 85, ... (satisfying x_{k+1} = 4*x_k + 1)
  verify the condition since they can be written as (2^{2p} - 1) / 3.
-/
import BohmSontacchi.Defs
import BohmSontacchi.Prop4
import BohmSontacchi.Prop5

namespace BohmSontacchi

/-! ## The reach-one formula

For reaching 1 under u, the relevant formula is:
  x = (2^n - sum_{k=0}^{m-1} 3^{m-k-1} * 2^{v_k}) / 3^m

where v_0 < v_1 < ... < v_{m-1} < n = v_m, and m is the number
of odd steps in the trajectory from x to 1 over n total steps. -/

/-- The numerator sum for the reach-one formula:
    sum_{k=0}^{m-1} 3^{m-k-1} * 2^{v_k}
    where v is a list [v_0, ..., v_{m-1}] of odd-step positions. -/
def reachOneSumNumerator (v : List ℕ) : ℤ :=
  let m := v.length
  (List.range m).foldl
    (fun acc k => acc + 3 ^ (m - k - 1) * 2 ^ (v.getD k 0)) 0

/-- A witness for the reach-one formula: n total steps, v the list of
    odd-step positions, satisfying v_0 < v_1 < ... < v_{m-1} < n,
    and x = (2^n - reachOneSumNumerator v) / 3^m where m = v.length. -/
structure ReachOneWitness (x : ℤ) where
  /-- Total number of steps -/
  n : ℕ
  /-- Positions of odd steps: v_0, v_1, ..., v_{m-1} -/
  v : List ℕ
  /-- There is at least one odd step -/
  v_nonempty : v ≠ []
  /-- The positions are strictly increasing -/
  v_strictMono : v.Pairwise (· < ·)
  /-- All positions are less than n -/
  v_bound : ∀ i, i ∈ v → i < n
  /-- 3^m divides the numerator -/
  divisibility : (3 : ℤ) ^ v.length ∣ (2 ^ n - reachOneSumNumerator v)
  /-- x equals the formula -/
  formula : x = (2 ^ n - reachOneSumNumerator v) / (3 : ℤ) ^ v.length

/-! ## Helper lemmas for the proofs of Proposition 7 -/

/-- foldl with addition and zero equals Finset.sum. -/
private lemma foldl_add_eq_finset_sum (m : ℕ) (f : ℕ → ℤ) :
    (List.range m).foldl (fun acc k => acc + f k) 0 =
    ∑ k ∈ Finset.range m, f k := by
  induction m with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil, ih,
        Finset.sum_range_succ]

/-- listNumSum equals the corresponding Finset.sum. -/
private lemma listNumSum_eq_finset_sum (v : List ℕ) :
    listNumSum v = ∑ k ∈ Finset.range v.length,
      (3 : ℤ) ^ (v.length - k - 1) * 2 ^ (v.getD k 0) := by
  induction v with
  | nil => simp [listNumSum]
  | cons a rest ih =>
    simp only [listNumSum, List.length_cons]
    rw [Finset.sum_range_succ']
    simp only [List.getD_cons_zero]
    rw [show rest.length + 1 - 0 - 1 = rest.length from by omega, ih]
    have hsum : ∑ k ∈ Finset.range rest.length,
        (3 : ℤ) ^ (rest.length + 1 - (k + 1) - 1) * 2 ^ ((a :: rest).getD (k + 1) 0) =
        ∑ k ∈ Finset.range rest.length,
        (3 : ℤ) ^ (rest.length - k - 1) * 2 ^ (rest.getD k 0) := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [Finset.mem_range] at hk
      rw [show rest.length + 1 - (k + 1) - 1 = rest.length - k - 1 from by omega]
      simp
    linarith

/-- reachOneSumNumerator and listNumSum compute the same value. -/
private lemma reachOneSumNumerator_eq_listNumSum (v : List ℕ) :
    reachOneSumNumerator v = listNumSum v := by
  unfold reachOneSumNumerator
  rw [foldl_add_eq_finset_sum, listNumSum_eq_finset_sum]

/-- collatzU_iterate (n+1) x = collatzU_iterate n (collatzU x). -/
private lemma collatzU_iterate_succ' (n : ℕ) (x : ℤ) :
    collatzU_iterate (n + 1) x = collatzU_iterate n (collatzU x) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    show collatzU (collatzU_iterate (n + 1) x) = collatzU (collatzU_iterate n (collatzU x))
    rw [ih]

/-- Iterating u on 2^n gives 1 (repeated halving). -/
private lemma iterate_pow2 (n : ℕ) : collatzU_iterate n ((2 : ℤ) ^ n) = 1 := by
  induction n with
  | zero => simp [collatzU_iterate]
  | succ n ih =>
    rw [collatzU_iterate_succ']
    have heven : (2 : ℤ) ^ (n + 1) % 2 = 0 := by
      have : (2 : ℤ) ^ (n + 1) = 2 * 2 ^ n := by ring
      rw [this]; omega
    have : collatzU ((2 : ℤ) ^ (n + 1)) = 2 ^ n := by
      rw [collatzU_even heven]
      have : (2 : ℤ) ^ (n + 1) = 2 * 2 ^ n := by ring
      rw [this, Int.mul_ediv_cancel_left _ (by norm_num : (2 : ℤ) ≠ 0)]
    rw [this, ih]

/-- u(1) = 2 and u(2) = 1, so u^{n+2}(x) = 1 when u^n(x) = 1. -/
private lemma iterate_plus_two (x : ℤ) (n : ℕ) (h : collatzU_iterate n x = 1) :
    collatzU_iterate (n + 2) x = 1 := by
  show collatzU (collatzU (collatzU_iterate n x)) = 1; rw [h]; decide

/-- 3^m mod 2 = 1 for all m. -/
private lemma pow3_mod2 (m : ℕ) : (3 : ℤ) ^ m % 2 = 1 := by
  induction m with
  | zero => norm_num
  | succ n ih =>
    have : (3 : ℤ) ^ (n + 1) = 3 ^ n * 3 := by ring
    rw [this, Int.mul_emod, ih]; norm_num

/-- 2^n mod 2 = 0 for n >= 1. -/
private lemma pow2_mod2 (n : ℕ) (hn : 1 ≤ n) : (2 : ℤ) ^ n % 2 = 0 := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  have : (2 : ℤ) ^ (k + 1) = 2 * 2 ^ k := by ring
  rw [this, Int.mul_emod_right]

/-- 2^n = 2 * 2^{n-1} for n >= 1. -/
private lemma pow2_factor (n : ℕ) (hn : 1 ≤ n) : (2 : ℤ) ^ n = 2 * 2 ^ (n - 1) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  simp [pow_succ]; ring

/-- If all elements of v are >= 1, then listNumSum v = 2 * listNumSum (v.map (. - 1)). -/
private lemma listNumSum_shift (v : List ℕ) (hpos : ∀ i ∈ v, 1 ≤ i) :
    listNumSum v = 2 * listNumSum (v.map (· - 1)) := by
  induction v with
  | nil => simp [listNumSum]
  | cons a rest ih =>
    simp only [listNumSum, List.map_cons, List.length_map]
    have ha : 1 ≤ a := hpos a (by simp)
    have hrest : ∀ i ∈ rest, 1 ≤ i := fun i hi => hpos i (by simp [hi])
    rw [ih hrest]
    have hpow : (2 : ℤ) ^ a = 2 * 2 ^ (a - 1) := by
      obtain ⟨k, rfl⟩ : ∃ k, a = k + 1 := ⟨a - 1, by omega⟩
      simp [pow_succ]; ring
    rw [hpow]; ring

/-- If all elements are >= 1, listNumSum is even. -/
private lemma listNumSum_even_of_pos (v : List ℕ) (hpos : ∀ i ∈ v, 1 ≤ i) :
    (listNumSum v) % 2 = 0 := by
  rw [listNumSum_shift v hpos]; omega

/-- Mapping (. - 1) over a sorted list with all elements >= 1 preserves sorting. -/
private lemma map_pred_sorted (v : List ℕ) (hv : v.Pairwise (· < ·))
    (hpos : ∀ i ∈ v, 1 ≤ i) :
    (v.map (· - 1)).Pairwise (· < ·) := by
  induction v with
  | nil => simp
  | cons a rest ih =>
    simp only [List.map_cons, List.pairwise_cons] at *
    obtain ⟨hhead, hrest_sorted⟩ := hv
    have hrest_pos : ∀ i ∈ rest, 1 ≤ i := fun i hi => hpos i (by simp [hi])
    refine ⟨?_, ih hrest_sorted hrest_pos⟩
    intro b hb
    rw [List.mem_map] at hb
    obtain ⟨c, hc_mem, rfl⟩ := hb
    have := hhead c hc_mem; have := hpos a (by simp); omega

/-- Mapping (. - 1) preserves the bound (shifted down by 1). -/
private lemma map_pred_bound (v : List ℕ) (n : ℕ) (hbound : ∀ i ∈ v, i < n)
    (hpos : ∀ i ∈ v, 1 ≤ i) :
    ∀ i ∈ v.map (· - 1), i < n - 1 := by
  intro i hi; rw [List.mem_map] at hi
  obtain ⟨j, hj_mem, rfl⟩ := hi
  have := hbound j hj_mem; have := hpos j hj_mem; omega

/-- Odd step positions of x over n+2 steps include position n when u^n(x) = 1. -/
private lemma oddSteps_nonempty_of_reach (x : ℤ) (n : ℕ)
    (h : collatzU_iterate n x = 1) :
    oddSteps x (n + 2) ≠ [] := by
  intro hempty
  have : n ∈ oddSteps x (n + 2) := by
    unfold oddSteps
    simp only [List.mem_filter, List.mem_range, decide_eq_true_eq]
    exact ⟨by omega, by rw [h]; decide⟩
  rw [hempty] at this; simp at this

/-- Odd steps elements are all < n. -/
private lemma oddSteps_bound (x : ℤ) (n : ℕ) :
    ∀ i, i ∈ oddSteps x n → i < n := by
  intro i hi; unfold oddSteps at hi
  simp only [List.mem_filter, List.mem_range, decide_eq_true_eq] at hi; exact hi.1

/-- Odd steps membership iff the iterate is odd. -/
private lemma oddSteps_compat (x : ℤ) (n : ℕ) :
    ∀ i, i < n → (i ∈ oddSteps x n ↔ collatzU_iterate i x % 2 = 1) := by
  intro i hi; unfold oddSteps
  simp only [List.mem_filter, List.mem_range, decide_eq_true_eq]
  exact ⟨fun h => h.2, fun h => ⟨hi, h⟩⟩

/-! ## The backward direction helper: strong induction on n

If 3^m * x + listNumSum v = 2^n with v sorted, nonempty, and bounded by n,
then u^n(x) = 1. The proof proceeds by strong induction on n, analyzing the
parity of x to determine whether the first step is even or odd. -/

private theorem backward_core : ∀ (n : ℕ) (x : ℤ) (v : List ℕ),
    v ≠ [] →
    v.Pairwise (· < ·) →
    (∀ i ∈ v, i < n) →
    (3 : ℤ) ^ v.length * x + listNumSum v = 2 ^ n →
    collatzU_iterate n x = 1 := by
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
    intro x v hne hsorted hbound hformula
    have hn_pos : 1 ≤ n := by
      rcases v with _ | ⟨a, _⟩
      · exact absurd rfl hne
      · have := hbound a (by simp); omega
    by_cases h0 : (0 : ℕ) ∈ v
    · -- Case: 0 ∈ v, x is odd
      rcases v with _ | ⟨a, rest⟩
      · exact absurd rfl hne
      · have ha : a = 0 := by
          rcases List.mem_cons.mp h0 with rfl | h0_rest
          · rfl
          · exact absurd ((List.pairwise_cons.mp hsorted).1 0 h0_rest) (by omega)
        subst ha
        have hrest_sorted : rest.Pairwise (· < ·) := (List.pairwise_cons.mp hsorted).2
        have hrest_pos : ∀ i ∈ rest, 1 ≤ i := by
          intro i hi
          exact Nat.pos_of_ne_zero (by
            intro heq; subst heq
            exact absurd ((List.pairwise_cons.mp hsorted).1 0 hi) (by omega))
        simp only [listNumSum, List.length_cons, pow_zero, mul_one] at hformula
        have hx_odd : x % 2 = 1 := by
          have hmod : ((3 : ℤ) ^ (rest.length + 1) * x +
              (3 ^ rest.length + listNumSum rest)) % 2 = 0 := by
            rw [hformula]; exact pow2_mod2 n hn_pos
          rw [show (3 : ℤ) ^ (rest.length + 1) * x + (3 ^ rest.length + listNumSum rest) =
              3 ^ (rest.length + 1) * x + 3 ^ rest.length + listNumSum rest from by ring] at hmod
          rw [Int.add_emod, Int.add_emod ((3 : ℤ) ^ (rest.length + 1) * x),
              Int.mul_emod, pow3_mod2 (rest.length + 1),
              listNumSum_even_of_pos rest hrest_pos,
              pow3_mod2 rest.length] at hmod
          omega
        set x' := (3 * x + 1) / 2
        have hu : collatzU x = x' := collatzU_odd' hx_odd
        have hx'_eq : 2 * x' = 3 * x + 1 := by omega
        have hshift := listNumSum_shift rest hrest_pos
        set rest' := rest.map (· - 1)
        have hrest'_len : rest'.length = rest.length := by simp [rest']
        by_cases hrest_ne : rest = []
        · -- rest = [], v = [0], m = 1: 3*x + 1 = 2^n
          subst hrest_ne
          simp [listNumSum] at hformula
          have hx'_pow : x' = 2 ^ (n - 1) := by linarith [pow2_factor n hn_pos]
          have : n = (n - 1) + 1 := by omega
          rw [this, collatzU_iterate_succ', hu, hx'_pow]
          exact iterate_pow2 (n - 1)
        · -- rest nonempty: apply IH with rest' and n - 1
          have hformula' : (3 : ℤ) ^ rest'.length * x' + listNumSum rest' = 2 ^ (n - 1) := by
            rw [hrest'_len]
            have h_eq : (2 : ℤ) * ((3 : ℤ) ^ rest.length * x' + listNumSum rest') = 2 ^ n := by
              calc (2 : ℤ) * (3 ^ rest.length * x' + listNumSum rest')
                  = 3 ^ rest.length * (2 * x') + 2 * listNumSum rest' := by ring
                _ = 3 ^ rest.length * (3 * x + 1) + listNumSum rest := by rw [hx'_eq, hshift]
                _ = 3 ^ (rest.length + 1) * x + (3 ^ rest.length + listNumSum rest) := by ring
                _ = 2 ^ n := hformula
            linarith [pow2_factor n hn_pos]
          have hrest'_ne : rest' ≠ [] := by simp [rest', List.map_eq_nil_iff, hrest_ne]
          have hrest'_sorted := map_pred_sorted rest hrest_sorted hrest_pos
          have hrest'_bound := map_pred_bound rest n
            (fun i hi => hbound i (by simp [hi])) hrest_pos
          have hih := ih (n - 1) (by omega) x' rest' hrest'_ne hrest'_sorted
            hrest'_bound hformula'
          have : n = (n - 1) + 1 := by omega
          rw [this, collatzU_iterate_succ', hu, hih]
    · -- Case: 0 not in v, x is even
      have hpos : ∀ i ∈ v, 1 ≤ i := by
        intro i hi; by_contra h; push_neg at h; interval_cases i; exact h0 hi
      have hx_even : x % 2 = 0 := by
        have hmod : ((3 : ℤ) ^ v.length * x + listNumSum v) % 2 = 0 := by
          rw [hformula]; exact pow2_mod2 n hn_pos
        rw [Int.add_emod, Int.mul_emod, pow3_mod2, listNumSum_even_of_pos v hpos] at hmod
        omega
      set x' := x / 2
      have hu : collatzU x = x' := collatzU_even hx_even
      have hx_eq : x = 2 * x' := by omega
      set v' := v.map (· - 1)
      have hv'_len : v'.length = v.length := by simp [v']
      have hshift := listNumSum_shift v hpos
      have hformula' : (3 : ℤ) ^ v'.length * x' + listNumSum v' = 2 ^ (n - 1) := by
        rw [hv'_len]
        have h_eq : (2 : ℤ) * ((3 : ℤ) ^ v.length * x' + listNumSum v') = 2 ^ n := by
          calc (2 : ℤ) * (3 ^ v.length * x' + listNumSum v')
              = 3 ^ v.length * (2 * x') + 2 * listNumSum v' := by ring
            _ = 3 ^ v.length * x + listNumSum v := by rw [← hx_eq, ← hshift]
            _ = 2 ^ n := hformula
        linarith [pow2_factor n hn_pos]
      have hv'_ne : v' ≠ [] := by simp [v', List.map_eq_nil_iff, hne]
      have hv'_sorted := map_pred_sorted v hsorted hpos
      have hv'_bound := map_pred_bound v n hbound hpos
      have hih := ih (n - 1) (by omega) x' v' hv'_ne hv'_sorted hv'_bound hformula'
      have : n = (n - 1) + 1 := by omega
      rw [this, collatzU_iterate_succ', hu, hih]

/-! ## Proposition 7: main statements -/

/-- PROPOSITION 7 (forward direction): If x reaches 1 under iteration of u,
    then there exists a reach-one witness for x. -/
theorem prop7_forward (x : ℤ) (hx : reachesOne x) :
    Nonempty (ReachOneWitness x) := by
  obtain ⟨n, hreach⟩ := hx
  -- Use n' = n + 2 to ensure oddSteps is nonempty (since u^n(x) = 1 is odd)
  set n' := n + 2
  set v := oddSteps x n' with hv_def
  have hreach' : collatzU_iterate n' x = 1 := iterate_plus_two x n hreach
  have hv_ne : v ≠ [] := oddSteps_nonempty_of_reach x n hreach
  have hv_sorted : v.Pairwise (· < ·) := oddSteps_strictMono x n'
  have hv_bound : ∀ i, i ∈ v → i < n' := oddSteps_bound x n'
  have hv_compat : ∀ i, i < n' → (i ∈ v ↔ collatzU_iterate i x % 2 = 1) :=
    oddSteps_compat x n'
  -- Apply the integer formula: 2^n' * u^n'(x) = 3^|v| * x + listNumSum v
  have hformula := collatzU_iterate_int_formula x n' v hv_sorted hv_bound hv_compat
  rw [hreach', mul_one] at hformula
  -- hformula : 2^n' = 3^|v| * x + listNumSum v
  have h3x : (3 : ℤ) ^ v.length * x = 2 ^ n' - listNumSum v := by linarith
  have hdvd : (3 : ℤ) ^ v.length ∣ (2 ^ n' - listNumSum v) := ⟨x, h3x.symm⟩
  have hform : x = (2 ^ n' - listNumSum v) / (3 : ℤ) ^ v.length := by
    rw [← h3x, Int.mul_ediv_cancel_left x (by positivity : (3 : ℤ) ^ v.length ≠ 0)]
  -- Convert listNumSum to reachOneSumNumerator
  have hrns : reachOneSumNumerator v = listNumSum v := reachOneSumNumerator_eq_listNumSum v
  refine ⟨{
    n := n'
    v := v
    v_nonempty := hv_ne
    v_strictMono := hv_sorted
    v_bound := hv_bound
    divisibility := by rwa [hrns]
    formula := by rwa [hrns]
  }⟩

/-- PROPOSITION 7 (backward direction): If there exists a reach-one witness
    for x, then x reaches 1 under iteration of u. -/
theorem prop7_backward (x : ℤ) (w : ReachOneWitness x) :
    reachesOne x := by
  -- Extract witness data into local variables to avoid dependent type issues
  set wn := w.n with hwn_def
  set wv := w.v with hwv_def
  have wv_ne := w.v_nonempty
  have wv_sorted := w.v_strictMono
  have wv_bound := w.v_bound
  have hrns : reachOneSumNumerator wv = listNumSum wv := reachOneSumNumerator_eq_listNumSum wv
  -- From divisibility: 3^m | (2^n - listNumSum v)
  have hdvd : (3 : ℤ) ^ wv.length ∣ (2 ^ wn - listNumSum wv) := by
    have := w.divisibility; rwa [hrns] at this
  -- From formula: x = (2^n - listNumSum v) / 3^m
  have hform : x = (2 ^ wn - listNumSum wv) / (3 : ℤ) ^ wv.length := by
    have := w.formula; rwa [hrns] at this
  -- So 3^m * x = 2^n - listNumSum v
  have h3x : (3 : ℤ) ^ wv.length * x = 2 ^ wn - listNumSum wv := by
    rw [hform]; exact Int.mul_ediv_cancel' hdvd
  have hformula : (3 : ℤ) ^ wv.length * x + listNumSum wv = 2 ^ wn := by linarith
  -- Apply the backward core lemma
  exact ⟨wn, backward_core wn x wv wv_ne wv_sorted wv_bound hformula⟩

/-- PROPOSITION 7 (full characterization): x is in U if and only if
    there exists a reach-one witness. -/
theorem prop7 (x : ℤ) :
    reachesOne x ↔ Nonempty (ReachOneWitness x) :=
  ⟨prop7_forward x, fun ⟨w⟩ => prop7_backward x w⟩

/-! ## The Collatz conjecture restated via formula (**)

The verification of the Collatz conjecture reduces to showing that
every positive integer admits a representation via formula (**). -/

/-- The Collatz conjecture, restated via Proposition 7:
    every positive integer has a reach-one witness. -/
def collatzConjectureViaFormula : Prop :=
  ∀ x : ℤ, 0 < x → Nonempty (ReachOneWitness x)

/-! ## Example family: numbers of the form (2^{2p} - 1) / 3

The paper notes that 1, 5, 21, 85, ... satisfy x_{k+1} = 4*x_k + 1
and can be written as (2^{2p} - 1) / 3. These verify formula (**)
with the simplest schedule: m = 1 odd step at position v_0 = 0,
and n = 2p total steps. Then:
  reachOneSumNumerator [0] = 3^0 * 2^0 = 1
  x = (2^{2p} - 1) / 3^1 = (2^{2p} - 1) / 3 -/

/-- The family of numbers (2^{2p} - 1) / 3 for p >= 1. -/
def exampleFamily (p : ℕ) : ℤ := ((2 : ℤ) ^ (2 * p) - 1) / 3

/-- 3 divides 2^{2p} - 1 for all p. -/
theorem three_dvd_pow_two_sub_one (p : ℕ) :
    (3 : ℤ) ∣ 2 ^ (2 * p) - 1 := by
  induction p with
  | zero => simp
  | succ p ih =>
    obtain ⟨k, hk⟩ := ih
    use 4 * k + 1
    have h2p1 : 2 * (p + 1) = 2 * p + 2 := by ring
    rw [h2p1, pow_add, show (2 : ℤ) ^ 2 = 4 from by norm_num]
    linarith

/-- The numerator sum for the singleton position list [0] is 1. -/
theorem reachOneSumNumerator_singleton_zero :
    reachOneSumNumerator [0] = 1 := by
  simp [reachOneSumNumerator, List.getD]

/-- Numbers of the form (2^{2p} - 1) / 3 have a reach-one witness
    with schedule [0] and n = 2p steps. -/
theorem exampleFamily_witness (p : ℕ) (hp : 1 ≤ p) :
    Nonempty (ReachOneWitness (exampleFamily p)) := by
  refine ⟨{
    n := 2 * p
    v := [0]
    v_nonempty := List.cons_ne_nil 0 []
    v_strictMono := List.pairwise_singleton _ 0
    v_bound := ?_
    divisibility := ?_
    formula := ?_
  }⟩
  · intro i hi
    simp at hi
    omega
  · simp only [List.length_singleton, pow_one, reachOneSumNumerator_singleton_zero]
    exact three_dvd_pow_two_sub_one p
  · simp only [List.length_singleton, pow_one, reachOneSumNumerator_singleton_zero,
               exampleFamily]

/-- Concrete verification: exampleFamily 1 = 1 -/
theorem exampleFamily_1 : exampleFamily 1 = 1 := by decide

/-- Concrete verification: exampleFamily 2 = 5 -/
theorem exampleFamily_2 : exampleFamily 2 = 5 := by decide

/-- Concrete verification: exampleFamily 3 = 21 -/
theorem exampleFamily_3 : exampleFamily 3 = 21 := by decide

/-- Concrete verification: exampleFamily 4 = 85 -/
theorem exampleFamily_4 : exampleFamily 4 = 85 := by decide

/-- The recurrence: 4 * exampleFamily p + 1 = exampleFamily (p + 1). -/
theorem exampleFamily_recurrence (p : ℕ) :
    4 * exampleFamily p + 1 = exampleFamily (p + 1) := by
  simp only [exampleFamily]
  obtain ⟨k, hk⟩ := three_dvd_pow_two_sub_one p
  have h2p1 : 2 * (p + 1) = 2 * p + 2 := by ring
  rw [h2p1, pow_add, show (2 : ℤ) ^ 2 = 4 from by norm_num, hk]
  omega

/-- Direct verification that 1 reaches 1 under u (trivially). -/
theorem one_reaches_one : reachesOne 1 :=
  ⟨0, rfl⟩

/-- Direct verification that 5 reaches 1 under u.
    Trajectory: 5 -> 8 -> 4 -> 2 -> 1. -/
theorem five_reaches_one : reachesOne 5 :=
  ⟨4, by decide⟩

/-- Direct verification that 21 reaches 1 under u.
    Trajectory: 21 -> 32 -> 16 -> 8 -> 4 -> 2 -> 1. -/
theorem twentyone_reaches_one : reachesOne 21 :=
  ⟨6, by decide⟩

end BohmSontacchi
