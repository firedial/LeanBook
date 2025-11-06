#check Prop
#check (1 + 1 = 3 : Prop)
#check (fun n => n + 3 = 39 : Nat → Prop)

example (P : Prop) (h : P) : P := by
  exact h

example (P : Prop) (h : P) : P := by
  assumption

example (h : False) : ∀ x y z n : Nat,
    n ≥ 3 → x ^ n + y ^ n = z ^ n → x * y * z = 0 := by
  trivial

example (P Q : Prop) (h : P → Q) (hp : P) : Q := by
  apply h
  apply hp

example (P Q : Prop) (h : P → Q) (hp : P) : Q := by
  exact h hp

example (P : Prop) : (¬ P) = (P → False) := by
  rfl

example (P : Prop) (hnp : ¬ P) (hp : P) : False := by
  apply hnp
  exact hp

example (P Q : Prop) (h : P → ¬ Q) : Q → ¬ P := by
  intro hq
  intro hp
  exact h hp hq

example (P : Prop) (hnp : ¬ P) (hp : P) : False := by
  contradiction

example (P : Prop) (hnp : ¬ P) (hp : P) : False := by
  exfalso
  contradiction

example (P Q : Prop) (h1 : P → Q) (h2 : Q → P) : P ↔ Q := by
  constructor
  · apply h1
  · apply h2

example (P Q : Prop) (hq : Q) : (Q → P) ↔ P := by
  constructor <;> intro h

  case mp =>
    exact h hq

  case mpr =>
    intro hq
    exact h

example (P Q : Prop) (h : P ↔ Q) (hq : Q) : P := by
  rw [h]
  exact hq

example (P Q : Prop) (h : P ↔ Q) (hp : P) : Q := by
  rw [← h]
  exact hp

example (P Q : Prop) (hp : P) (hq : Q) : P ∧ Q := by
  exact ⟨hp, hq⟩

example (P Q : Prop) (h : P ∨ Q) : Q ∨ P := by
  cases h with
  | inl hp =>
    right
    exact hp
  | inr hq =>
    left
    exact hq

-- 練習問題
example (P Q : Prop) : (¬ P ∨ Q) → (P → Q) := by
  -- (¬ P ∨ Q) を仮定する
  intro hnpq

  -- その仮定した命題のOR条件それぞれに対して示す
  cases hnpq with
  | inl hnp => -- ¬ P の仮定
    intro hp -- P の仮定
    contradiction -- 矛盾
  | inr hq => -- Q の仮定
    intro hp -- P の仮定
    exact hq -- Q の仮定から成り立つ

example (P Q : Prop) : ¬ (P ∨ Q) ↔ ¬ P ∧ ¬ Q := by
  constructor <;> intro h1
  · constructor <;> intro h2
    · apply h1
      left
      assumption
    · apply h1
      right
      assumption
  · intro h2
    cases h2 with
    | inl hp =>
      apply h1.left
      assumption
    | inr hq =>
      apply h1.right
      assumption
