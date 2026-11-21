inductive MyNat where
  /--ゼロ-/
  | zero
  /-- 後者関数 (nに対して n+1 を返す関数)-/
  | succ (n : MyNat)

#check MyNat.zero
#check MyNat.succ
#check MyNat.succ .zero

def MyNat.one := MyNat.succ .zero
def MyNat.two := MyNat.succ .one

def MyNat.add (m n : MyNat) : MyNat :=
  match n with
  | .zero => m
  | .succ n => MyNat.succ (MyNat.add m n)

set_option pp.fieldNotation.generalized false

#check MyNat.add .one .one = .two

-- reduce: reduction(簡約) 定義を展開して式を書き換え、これ以上計算できない形まで進める
-- rfl が通るのは a, b を reduction した結果同じになるとき
-- infoview を見ると、同じ MyNat.succ (MyNat.succ MyNat.zero) になっているのを確認できる
#reduce MyNat.add .one .one

#reduce MyNat.two

-- example: 命題に名前を付けずに(後で参照する必要がないときの)証明するコマンド
-- rfl: タクティクの１つ( := rfl と書いて項とすることも可能)。reflexivity 反射律
example : MyNat.add .one .one = .two := by
  rfl
