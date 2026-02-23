/-
  Bohm-Sontacchi 1978 -- Proposition 2

  PROPOSITION 2. For all l_j in {l_j}_{1 <= j <= 2^n}, there exists a unique x in Q
  such that l_j(x) = x; therefore for all n in P and for all l in L, there exist at most
  2^n rationals such that l^n(x) = x.

  Key insight: Each composed function is affine: alpha*x + beta with
  alpha = c^m * a^{n-m}. When alpha != 1, the unique fixed point is beta/(1 - alpha).

  We prove the core mathematical fact: any affine function ax + b with a != 1
  has a unique fixed point, namely b / (1 - a).
-/
import BohmSontacchi.Defs

namespace BohmSontacchi

/-! ## Unique fixed points of affine maps -/

/-- An affine function `f(x) = α * x + β` with `α ≠ 1` has `β / (1 - α)` as a fixed point. -/
theorem affine_fixed_point_val (α β : ℚ) (hα : α ≠ 1) :
    α * (β / (1 - α)) + β = β / (1 - α) := by
  have h1 : (1 : ℚ) - α ≠ 0 := sub_ne_zero.mpr (Ne.symm hα)
  field_simp
  ring

/-- An affine function `f(x) = α * x + β` with `α ≠ 1` has a unique fixed point. -/
theorem affine_fixed_point_unique (α β : ℚ) (hα : α ≠ 1) (x : ℚ)
    (hfix : α * x + β = x) : x = β / (1 - α) := by
  have h1 : (1 : ℚ) - α ≠ 0 := sub_ne_zero.mpr (Ne.symm hα)
  -- From α * x + β = x, we get β = x - α * x = x * (1 - α)
  have : β = x * (1 - α) := by linarith
  field_simp
  linarith

/-- **Proposition 2, core lemma**: An affine function `f(x) = α * x + β` with `α ≠ 1`
    has exactly one fixed point, namely `β / (1 - α)`. -/
theorem proposition2_unique_fixed_point (α β : ℚ) (hα : α ≠ 1) :
    ∃! x : ℚ, α * x + β = x := by
  refine ⟨β / (1 - α), affine_fixed_point_val α β hα, ?_⟩
  intro y hy
  exact affine_fixed_point_unique α β hα y hy

/-! ## Application to composed functions from Proposition 1

From Proposition 1, every composed function `f^{n_m} g ... g f^{n_0}` is affine.
If its leading coefficient `α = c^m * a^{sum n_i}` is not equal to 1,
then it has a unique fixed point. -/

/-- Given any affine map with slope ≠ 1, there is a unique fixed point. -/
theorem proposition2_affine_map_unique_fixpoint
    (α β : ℚ) (hα : α ≠ 1) :
    ∃! x : ℚ, α * x + β = x :=
  proposition2_unique_fixed_point α β hα

/-! ## The counting bound: at most 2^n fixed points

For an n-step iteration of a piecewise function l in L (which at each step
chooses f or g), there are 2^n possible compositions. Each such composition
is affine with a unique fixed point (when the slope ≠ 1).
Therefore there are at most 2^n periodic points of period n. -/

/-- A sequence of choices: at each step, apply either f or g. -/
def BranchChoice := Fin 2

/-- Apply a single step: if the choice is 0, apply f; if 1, apply g. -/
def applyBranch (a b c d : ℚ) (choice : Fin 2) (x : ℚ) : ℚ :=
  if choice = 0 then affineF a b x else affineG c d x

/-- Apply a sequence of n branch choices. -/
def applySequence (a b c d : ℚ) : List (Fin 2) → ℚ → ℚ
  | [], x => x
  | ch :: rest, x => applySequence a b c d rest (applyBranch a b c d ch x)

/-- Any sequence of f and g applications is an affine function. -/
theorem applySequence_is_affine (a b c d : ℚ) (choices : List (Fin 2)) :
    ∃ α β : ℚ, ∀ x : ℚ, applySequence a b c d choices x = α * x + β := by
  induction choices with
  | nil =>
    exact ⟨1, 0, fun x => by simp [applySequence]⟩
  | cons ch rest ih =>
    obtain ⟨α', β', hαβ⟩ := ih
    by_cases hch : ch = 0
    · -- Applied f first: α' * (a * x + b) + β' = (α' * a) * x + (α' * b + β')
      exact ⟨α' * a, α' * b + β', fun x => by
        simp only [applySequence, applyBranch, hch, ↓reduceIte]
        rw [hαβ]; simp [affineF]; ring⟩
    · -- Applied g first: α' * (c * x + d) + β' = (α' * c) * x + (α' * d + β')
      have : ch = 1 := by omega
      exact ⟨α' * c, α' * d + β', fun x => by
        simp only [applySequence, applyBranch, hch, ↓reduceIte]
        rw [hαβ]; simp [affineG]; ring⟩

/-- If the slope of any composed branch is not 1, it has a unique fixed point. -/
theorem applySequence_unique_fixpoint (a b c d : ℚ) (choices : List (Fin 2))
    (hslope : ∀ α β : ℚ,
      (∀ x : ℚ, applySequence a b c d choices x = α * x + β) → α ≠ 1) :
    ∃! x : ℚ, applySequence a b c d choices x = x := by
  obtain ⟨α, β, hαβ⟩ := applySequence_is_affine a b c d choices
  have hα : α ≠ 1 := hslope α β hαβ
  obtain ⟨fp, hfp_fix, hfp_unique⟩ := proposition2_unique_fixed_point α β hα
  refine ⟨fp, ?_, ?_⟩
  · change applySequence a b c d choices fp = fp
    rw [hαβ fp]; exact hfp_fix
  · intro y hy
    rw [hαβ y] at hy
    exact hfp_unique y hy

/-- Two rationals fixed by the same branch sequence (with slope ≠ 1) must be equal. -/
theorem applySequence_fixed_point_unique (a b c d : ℚ) (choices : List (Fin 2))
    (hslope : ∀ α β : ℚ,
      (∀ x : ℚ, applySequence a b c d choices x = α * x + β) → α ≠ 1)
    (x₁ x₂ : ℚ)
    (hfix₁ : applySequence a b c d choices x₁ = x₁)
    (hfix₂ : applySequence a b c d choices x₂ = x₂) :
    x₁ = x₂ := by
  obtain ⟨α, β, hαβ⟩ := applySequence_is_affine a b c d choices
  have hα : α ≠ 1 := hslope α β hαβ
  rw [hαβ] at hfix₁ hfix₂
  have h₁ := affine_fixed_point_unique α β hα x₁ hfix₁
  have h₂ := affine_fixed_point_unique α β hα x₂ hfix₂
  rw [h₁, h₂]

/-- Helper: convert a list of length n to a function Fin n → α -/
noncomputable def listToFun {α : Type*} (l : List α) (hl : l.length = n) : Fin n → α :=
  fun i => l.get (i.cast hl.symm)

/-- Two lists of the same length are equal iff their corresponding function representations
    are equal. -/
theorem list_eq_of_listToFun_eq {α : Type*} (l₁ l₂ : List α)
    (hl₁ : l₁.length = n) (hl₂ : l₂.length = n)
    (h : listToFun l₁ hl₁ = listToFun l₂ hl₂) :
    l₁ = l₂ := by
  apply List.ext_get (by omega)
  intro i hi₁ hi₂
  have hi : i < n := by omega
  have := congr_fun h ⟨i, hi⟩
  simp only [listToFun] at this
  exact this

/-- **Proposition 2** (upper bound on periodic points).
    For any piecewise affine function l in L with parameters a, b, c, d,
    and any positive integer n, the number of fixed points of l^n
    (i.e., periodic points of period n) is at most 2^n.

    This follows because there are exactly 2^n possible branch sequences of length n,
    and each branch sequence yields an affine map with at most one fixed point
    (given the slope condition that no composed branch has slope 1). -/
theorem proposition2_at_most_2n_periodic (a b c d : ℚ) (n : ℕ) (_hn : 0 < n)
    (S : Finset ℚ)
    (hS : ∀ x ∈ S, ∃ choices : List (Fin 2),
      choices.length = n ∧ applySequence a b c d choices x = x)
    (hslope : ∀ (choices : List (Fin 2)), choices.length = n →
      ∀ α β : ℚ, (∀ x, applySequence a b c d choices x = α * x + β) → α ≠ 1) :
    S.card ≤ 2 ^ n := by
  classical
  -- For each x ∈ S, pick a witnessing choice sequence using Classical.choose
  -- Define φ : ℚ → (Fin n → Fin 2) sending each x ∈ S to its choice sequence
  -- (represented as a function), and anything outside S to a default.
  let getChoices : (x : ℚ) → x ∈ S → List (Fin 2) :=
    fun x hx => (hS x hx).choose
  have getChoices_len : ∀ (x : ℚ) (hx : x ∈ S),
      (getChoices x hx).length = n :=
    fun x hx => (hS x hx).choose_spec.1
  have getChoices_fix : ∀ (x : ℚ) (hx : x ∈ S),
      applySequence a b c d (getChoices x hx) x = x :=
    fun x hx => (hS x hx).choose_spec.2
  -- Map each x to a function Fin n → Fin 2
  let φ : ℚ → (Fin n → Fin 2) :=
    fun x => if hx : x ∈ S then
      listToFun (getChoices x hx) (getChoices_len x hx)
    else
      fun _ => 0
  -- S.card ≤ |Fin n → Fin 2| = 2^n
  calc S.card
      ≤ (Finset.univ : Finset (Fin n → Fin 2)).card := by
        apply Finset.card_le_card_of_injOn φ
        · -- φ maps S into Finset.univ (trivial)
          intro x _; exact Finset.mem_univ _
        · -- φ is injective on S
          intro x₁ hx₁ x₂ hx₂ hφeq
          -- φ x₁ = listToFun (getChoices x₁ hx₁) ... since x₁ ∈ S
          have hφ₁ : φ x₁ = listToFun (getChoices x₁ hx₁) (getChoices_len x₁ hx₁) :=
            dif_pos hx₁
          have hφ₂ : φ x₂ = listToFun (getChoices x₂ hx₂) (getChoices_len x₂ hx₂) :=
            dif_pos hx₂
          have hfun_eq : listToFun (getChoices x₁ hx₁) (getChoices_len x₁ hx₁) =
              listToFun (getChoices x₂ hx₂) (getChoices_len x₂ hx₂) := by
            rw [← hφ₁, ← hφ₂]; exact hφeq
          have hlist_eq : getChoices x₁ hx₁ = getChoices x₂ hx₂ :=
            list_eq_of_listToFun_eq _ _ (getChoices_len x₁ hx₁) (getChoices_len x₂ hx₂) hfun_eq
          -- Both x₁ and x₂ are fixed points of the same choice sequence
          have hfix₁ := getChoices_fix x₁ hx₁
          have hfix₂ := getChoices_fix x₂ hx₂
          rw [hlist_eq] at hfix₁
          -- By uniqueness of fixed points (slope ≠ 1), x₁ = x₂
          exact applySequence_fixed_point_unique a b c d
            (getChoices x₂ hx₂)
            (hslope _ (getChoices_len x₂ hx₂))
            x₁ x₂ hfix₁ hfix₂
    _ = 2 ^ n := by
        simp [Finset.card_univ, Fintype.card_fin]

end BohmSontacchi
