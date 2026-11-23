#check Prop

-- 命題 (proposition)　1 + 1 = 3 という主張
#check (1 + 1 = 3 : Prop)

-- 命題を返す関数。 Nat → Prop は自然数を受け取り命題を返すという記述
-- n に具体的な値を渡すと命題になる. 述語 (predicate)
#check (fun n => n + 3 = 39 : Nat → Prop)

#check True

-- trivial: 基本的なタクティクを順に試すマクロ。 assumption、rfl、apply True.intro など
example : True := by trivial

-- (P : Prop) (h : P) が前提 (ローカルコンテキスト)。(P : Prop)は何かしらの命題、(h : P)　は、 h は P　の証明
-- : P は証明したい P (命題、ゴール)
-- exact: 与えられた証明項をそのまま証明として使うタクティク
-- ゴールが P で、ローカルコンテキストに h : P があるときに exact h はゴールを閉じる
example (P : Prop) (h : P) : P := by
  exact h

-- assumption: ゴールと同じ型の仮定 （h : P） がローカルコンテキストにあるときゴールを閉じる
example (P : Prop) (h : P) : P := by
  assumption

-- False を仮定すると何でも示せる例 (爆発律)
-- True には証明 True.intro があるが False には証明を作る方法がない。 h : False は　False　の証明を持っているという仮定で矛盾した状況
-- ∀ x y z n : Nat, は 全ての自然数 x y z n について
-- n ≥ 3 →  は n が 3以上ならば
-- x ^ n + y ^ n = z ^ n → は x^n + y^n = z^n が成り立つならば
-- x * y * z = 0 は x, y, z のどれかが 0 である (全体でフェルマーの最終定理)
-- trivial の中の contradiction が h : False を見つけてゴールを閉じる
example (h : False) : ∀ x y z n : Nat,
    n ≥ 3 → x ^ n + y ^ n = z ^ n → x * y * z = 0 := by
  trivial

-- 含意 implication
example (P Q R : Prop) : (P → Q → R) = (P → (Q → R)) := by
  rfl

-- True, False は命題を表し、true, false は真偽値を表す
-- true
#eval True → True

-- false
#eval True → False

-- true
#eval False → True
#eval False → False

-- True → False が成り立たないことの証明
example : ¬ (True → False) := fun f => f True.intro

-- 含意の導入
example (P Q : Prop) (hq : Q) : P → Q := by
  -- ゴールが P → Q のとき前提の P を仮定としてローカルコンテキストに移す
  intro hp
  -- Q を示す
  exact hq

-- Not
-- false
#eval ¬ True
-- true
#eval ¬ False

-- P と仮定すると矛盾する、ということは　¬　P と等しい
example (P : Prop) : (¬ P) = (P → False) := by
  rfl

-- modus ponens (含意の除去)
-- hnp : P → False  Pならば矛盾
-- hp : P  Pである
-- False  矛盾
example (P : Prop) (hnp : ¬ P) (hp : P) : False := by
  -- False を示すには hnp に渡す P を示せばよい
  apply hnp
  -- ゴールが P, ローカルコンテキストに hp : P があるので証明が完了
  exact hp

-- P ならば Q でない　から Q ならば P でない　を導く
example (P Q : Prop) (h : P → ¬ Q) : Q  → ¬ P := by
  intro hq
  intro hp
  exact h hp hq

-- contradiction: ローカルコンテキストから矛盾を探すタクティク
example (P : Prop) (hnp :  ¬ P) (hp : P) : False := by
  contradiction

-- exfalso: 証明のどの時点でもゴールを False に置き換えるタクティク
-- exfalso の前のゴールは Q 。 後では False に変わる
-- 爆発律により、False が示せれば False.elim で Q も示せる
example (P Q : Prop) (hnp : ¬ P) (hp : P) : Q := by
  exfalso
  contradiction

-- 同値性
-- true
#eval True ↔ True
-- false
#eval True ↔ False
-- false
#eval False ↔ True
-- true
#eval False ↔ False

-- constructor: ゴールの型のコンストラクタを当てはめるタクティク。以下では P ↔ Q　に Iff.intro を当てはめ h1, h2 を新しいゴールとする
--　case mp (modus penens)  mp, mpr は Iff 構造体で定義されたもの
-- h1 : P → Q
-- h2 : Q → P
-- ⊢ P → Q
-- case mpr (mp reverse)
-- · はゴールが複数あるときに残っている先頭のゴールを取り出す記法
example (P Q : Prop) (h1 : P → Q) (h2 : Q → P) : P ↔ Q := by
  constructor
  · exact h1
  · exact h2

-- Q が成り立つと分かっている （hq : Q） なら、「Q ならば P」 は P と同じ
example (P Q : Prop) (hq : Q) : (Q → P) ↔ P := by
  constructor
  -- ゴールを · でなくケース名で選んでいる
  -- mp ゴール ⊢ (Q → P) → P
  case mp =>
    -- hq : Q
    -- h : Q → P
    -- ⊢ P
    intro h
    exact h hq
  -- mpr ゴール ⊢ P → Q → P
  case mpr =>
    -- hq✝ : Q
    -- hp : P
    -- hq : Q
    -- ⊢ P
    intro hp hq
    exact hp

-- タクティク結合子 <;>
example (P Q : Prop) (hq : Q) : (Q → P) ↔ P := by
  constructor <;> intro h

  case mp =>
    exact h hq
  case mpr =>
    intro hq
    exact h

-- rw: 同値なものに書き換えるタクティク。 rw [h] で P を Q に書き換えている
example (P Q : Prop) (h : P ↔ Q) (hq : Q) : P := by
  --　
  rw [h]
  exact hq

example (P Q : Prop) (h : P ↔ Q) (hp : P) : Q := by
  --　
  rw [← h]
  exact hp

-- 命題外延性 (propositional extensionality)
-- 同値なら等しい
example (P Q : Prop) (h : P ↔ Q) : P = Q := by
  rw [h]
