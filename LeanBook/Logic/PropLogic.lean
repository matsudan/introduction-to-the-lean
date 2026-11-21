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
