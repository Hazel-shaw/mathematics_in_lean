--证明项：改写策略式证明—— 更简洁，可读性差


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

-- EVT

-- 定义紧集：称集合K ⊆ ℝ是紧的，若其中的每个序列都有一个收敛于K中极限的子序列。在实数域内：闭且有界。
-- 序列是无穷的
-- R、(0, 1)、[0, +∞)不是紧集; {1, 2, 3}、[0, 1]是紧集。
def SeqCompact (K : Set ℝ) : Prop :=
  ∀ (u : ℕ  → ℝ), (∀ n, u n ∈ K) →
  --数列的本质就是映射 自然数到实数
      ∃ (l : ℝ), (l ∈ K) ∧
        ( ∃ (φ : ℕ  → ℕ ), (StrictMono φ) ∧ (ConvergesTo (u ∘ φ) l))
        --∘ 表示复合映射

def IsBound (A : Set ℝ) (b : ℝ) : Prop :=  --定义有界
  ∀ a ∈ A, |a| ≤ b
-- 参考上届

-- 邻域
def V_ε (a : ℝ )(ε : ℝ ) : Set ℝ:=
  {x : ℝ | |x-a| < ε }

--开集 [0, 1]、半开半闭、有理数集不是; 全体实数集、开区间的并集、空集是开集
def IsOpenSet (O : Set ℝ): Prop:=
  ∀ a ∈ O, ∃ ε , V_ε a ε ⊆ O

--极限点x 序列本身不等于x  闭集包含自己的极限点
-- 有理数集的极限点集合=实数集
--孤立点 like 整数集没有极限点
def IsLimitPoint (A : Set ℝ) (x : ℝ) : Prop :=
  ∀ ε > 0, ∃ y, (y ≠ x) ∧ (y ∈ V_ε x ε ) ∧ (y ∈ A)


def HasConvergentSeqNeq (x : ℝ ) (A : Set ℝ ) : Prop:=
  --∃ (u : ℕ → ℝ)
  sorry

--  闭集 包含 自己的极限点
def IsClosedSet (F : Set ℝ): Prop:=
  ∀ (x : ℝ), IsLimitPoint F x → x ∈ F



def IsContinuousAt (f : ℝ → ℝ ) (A : Set ℝ ) (c : ℝ ): Prop:=
  ∀ ε > 0, ∃ δ > 0, ∀ (x : ℝ), (x ∈ A ∧ |x - c| < δ ) → |f x - f c| < ε
--连续函数
def IsContinuousOn (f : ℝ → ℝ ) (A : Set ℝ ): Prop:=
  ∀ (c : ℝ ), (c ∈ A) → (IsContinuousAt f A c)

--连续性的“序列”定义
def IsSeqContinuousAt (f :ℝ → ℝ) (A :Set ℝ) (c : ℝ): Prop:=
  ∀ (u : ℕ  → ℝ),
    (∀ n, u n ∈ A) →
    (ConvergesTo u c) →
    (ConvergesTo (f ∘ u) (f c))


theorem Heine_Borel (): Prop:=
  sorry
