/-!
# 変数の付け替え（renaming）

de Bruijn index を使うと、項や型を「別の環境の下」に移すときに変数の番号を付け替える必要がある。
たとえば型 `σ` を、新しい変数を 1 つ追加した環境の下に持っていくと、
`σ` 中の自由変数の番号はすべて 1 ずつ大きくなる（追加された変数が 0 番を取るため）。

番号の付け替えは関数 `ξ : Nat → Nat` で表す。このファイルでは次の 2 つを用意する。

* `upRen ξ`: 束縛子の内側に入るときに `ξ` を持ち上げたもの。
* `RenOk Γ Γ' ξ`: 「`ξ` は環境 `Γ` の変数を、同じ中身を持つ `Γ'` の変数へ移す」という性質。
  弱化補題（補題3）は、この性質を満たす付け替えで型付けが保たれる、という形で証明する。

このファイルの内容は PDF には現れない、de Bruijn index のための技術的な準備である。
-/

namespace SystemF

/-- 束縛子の内側に入るときの付け替えの持ち上げ。

束縛子の内側では、0 番はその束縛子自身が束縛する変数なので動かさない。
1 番以降（外側の変数）は、1 引いてから `ξ` で移し、1 足して元に戻す。
-/
def upRen (ξ : Nat → Nat) : Nat → Nat
  | 0 => 0
  | i + 1 => ξ i + 1

/-- 持ち上げてから合成しても、合成してから持ち上げても同じ。 -/
theorem upRen_comp (ξ ζ : Nat → Nat) :
    (fun i => upRen ζ (upRen ξ i)) = upRen (fun i => ζ (ξ i)) := by
  funext i
  cases i <;> rfl

/-- `ξ` が環境 `Γ` の各変数を、`Γ'` の同じ中身を持つ変数へ移すこと。

`Γ[i]?` は「環境 `Γ` の i 番目の要素（なければ `none`）」を表す。
環境はリストで表し、先頭（0 番）がいちばん新しく追加された変数である。
型変数の環境（カインドのリスト）と項変数の環境（型のリスト）の両方で使えるように、
要素の型 `α` について一般的に定義している。
-/
def RenOk {α : Type} (Γ Γ' : List α) (ξ : Nat → Nat) : Prop :=
  ∀ {i : Nat} {a : α}, Γ[i]? = some a → Γ'[ξ i]? = some a

namespace RenOk

variable {α : Type} {Γ Γ' : List α} {ξ : Nat → Nat}

/-- 両方の環境の先頭に同じ要素を追加したとき、持ち上げた `upRen ξ` が `RenOk` になる。 -/
theorem up {a : α} (h : RenOk Γ Γ' ξ) : RenOk (a :: Γ) (a :: Γ') (upRen ξ) := by
  intro i b hi
  cases i with
  | zero => simpa [upRen] using hi
  | succ i => simpa [upRen] using h (by simpa using hi)

/-- 環境の先頭に 1 つ要素を追加すると、すべての番号が 1 ずつずれる。 -/
theorem succ {a : α} : RenOk Γ (a :: Γ) (· + 1) := by
  intro i b hi
  simpa using hi

/-- 両方の環境の要素に同じ関数 `f` を適用しても `RenOk` は保たれる。 -/
theorem map {β : Type} (f : α → β) (h : RenOk Γ Γ' ξ) :
    RenOk (Γ.map f) (Γ'.map f) ξ := by
  intro i b hi
  simp only [List.getElem?_map, Option.map_eq_some_iff] at hi ⊢
  obtain ⟨a, ha, rfl⟩ := hi
  exact ⟨a, h ha, rfl⟩

end RenOk

end SystemF
