import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Real.Basic

def IsUpperBound (A : Set ℝ) (b : ℝ) : Prop :=  --Prop后 接收命题，输出真或假的函数“谓词 predicate”
  ∀ a ∈ A, a ≤ b
--上确界

def IsSup (A : Set ℝ) (s : ℝ) : Prop :=
  -- (i) s 是 A 的一个上界
  (IsUpperBound A s) ∧
  -- (ii) 如果 b 是 A 的任意一个上界，那么 s ≤ b
  (∀ b, IsUpperBound A b → s ≤ b)

axiom CompletenessAxiom (A : Set ℝ)
(h_nonempty : A.Nonempty)
(h_bdd : ∃ b, IsUpperBound A b) :
  ∃ s, IsSup A s

theorem sup_iff_forall_epsilon (A : Set ℝ) (s : ℝ) (h_upper : IsUpperBound A s) :
    IsSup A s ↔ ∀ ε > 0, ∃ a ∈ A, s - ε < a := by
  -- constructor
  -- · rintro ⟨-, hs⟩  ε εpos
  --   by_contra!
    sorry

def ConvergesTo (s : ℕ → ℝ) (a : ℝ) :=
  ∀ ε > 0, ∃ N, ∀ n ≥ N, |s n - a| < ε



theorem monotone_increasing_bounded_converges (x : ℕ → ℝ)
    (h_mono : Monotone x) (h_bdd_above : ∃ b, IsUpperBound (Set.range x) b) :
  ∃ s, IsSup (Set.range x) s ∧ ConvergesTo x s := by
  have h_nonempty : (Set.range x).Nonempty := by
    use (x 0)
    apply Set.mem_range_self  --simp
  have hsup : ∃ s, IsSup (Set.range x) s := by
    apply CompletenessAxiom
    apply h_nonempty
    exact h_bdd_above
  rcases hsup with ⟨s, hs⟩   --看到存在，用rcases
  use s, hs
  intro ε hε
  let hup:= hs.left
  rw[sup_iff_forall_epsilon] at hs
  rcases hs ε hε with ⟨a, ha⟩   --存在的参数a，参数性质ha
  rcases ha with ⟨ ⟨ N, hN ⟩ , h₁ ⟩   --解构
  use N
  intro n hn
  have h2: x n - s ≤ 0:=by
    simp
    apply hup
    simp
  rw[abs_of_nonpos]
  rw[neg_sub]
  have h3: x n ≥ x N:=by apply h_mono hn
  apply h2
  apply hup


  --obtain = rcases
  --同构 要在双射基础上 （可逆 = 双射）
