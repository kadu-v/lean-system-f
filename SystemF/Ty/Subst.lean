import SystemF.Syntax
import SystemF.Renaming

/-!
# 型の付け替えと代入

PDF の型代入 `[α ↦ σ']σ` を de Bruijn index の上で定義し、その性質を証明する。

## 並列代入

PDF では 1 つの変数だけを置き換える `[α ↦ σ']` を使うが、ここではまず
**すべての型変数を同時に置き換える代入** `σ : Nat → Ty`（変数番号 `i` を型 `σ i` に置き換える）
を定義し、1 変数の代入はその特殊な場合として得る。

こうすると、代入どうしの合成が「関数の合成」として 1 つの補題（`subst_subst`）で扱えるようになり、
PDF の補題5（型代入の交換）はその系として証明できる。

## このファイルの内容

* `Ty.rename ξ σ`   : 型 σ 中の変数番号を `ξ` で付け替える。
* `Ty.shift σ`      : すべての自由変数の番号を 1 増やす（環境に変数を 1 つ追加したとき）。
* `Ty.subst s σ`    : 型 σ 中の変数 `i` を `s i` で置き換える（並列代入）。
* `Ty.instantiate σ σ'` : PDF の `[α ↦ σ']σ`。`σ` の 0 番の変数を `σ'` で置き換える。
* 付け替えと代入の合成則、および補題5.1（`subst_instantiate`）。
-/

namespace SystemF
namespace Ty

/-! ## 定義 -/

/-- 型中の自由変数の番号を `ξ` で付け替える。∀ の内側では `upRen ξ` を使う。 -/
def rename (ξ : Nat → Nat) : Ty → Ty
  | var i => var (ξ i)
  | arr σ₁ σ₂ => arr (σ₁.rename ξ) (σ₂.rename ξ)
  | all κ σ => all κ (σ.rename (upRen ξ))

/-- すべての自由変数の番号を 1 増やす。

型変数を 1 つ環境に追加したとき（∀ や Λ の内側に入るとき）、
それまでの型を新しい環境で使うためにこの操作が必要になる。
-/
def shift (σ : Ty) : Ty := σ.rename (· + 1)

/-- 束縛子の内側に入るときの代入の持ち上げ。

0 番は内側の束縛子自身の変数なので、そのまま `var 0` にする。
1 番以降は元の代入 `s` で置き換え、置き換えた結果を内側で使うために `shift` する。
-/
def up (s : Nat → Ty) : Nat → Ty
  | 0 => var 0
  | i + 1 => (s i).shift

/-- 並列代入: 型中の自由変数 `i` を `s i` で同時に置き換える。 -/
def subst (s : Nat → Ty) : Ty → Ty
  | var i => s i
  | arr σ₁ σ₂ => arr (σ₁.subst s) (σ₂.subst s)
  | all κ σ => all κ (σ.subst (up s))

/-- 0 番の変数を `σ'` に置き換え、残りの変数の番号を 1 減らす代入。

0 番の変数を束縛していた束縛子が取り除かれるので、それより外側の変数の番号が 1 つ減る。
-/
def single (σ' : Ty) : Nat → Ty
  | 0 => σ'
  | i + 1 => var i

/-- PDF の `[α ↦ σ']σ`。`∀α::κ.σ` の本体 `σ` の束縛変数（0 番）を `σ'` で置き換える。 -/
def instantiate (σ σ' : Ty) : Ty := σ.subst (single σ')

/-! ## 付け替えと代入の合成則

以下の 4 つの補題は「付け替え・代入を続けて 2 回行うことは、合成した 1 回で表せる」ことを述べる。
いずれも型の構造に関する帰納法で示す。∀ の場合だけ、持ち上げた関数どうしが等しいことを
別途（番号が 0 か 1 以上かで場合分けして）確かめる必要がある。
-/

/-- 付け替えを 2 回行うのは、付け替えを合成して 1 回行うのと同じ。 -/
theorem rename_rename (σ : Ty) (ξ ζ : Nat → Nat) :
    (σ.rename ξ).rename ζ = σ.rename (fun i => ζ (ξ i)) := by
  induction σ generalizing ξ ζ with
  | var i => rfl
  | arr σ₁ σ₂ ih₁ ih₂ => simp only [rename, ih₁, ih₂]
  | all κ σ ih => simp only [rename, ih, upRen_comp]

/-- 付け替えてから代入するのは、代入を付け替えで前処理して 1 回代入するのと同じ。 -/
theorem subst_rename (σ : Ty) (ξ : Nat → Nat) (s : Nat → Ty) :
    (σ.rename ξ).subst s = σ.subst (fun i => s (ξ i)) := by
  induction σ generalizing ξ s with
  | var i => rfl
  | arr σ₁ σ₂ ih₁ ih₂ => simp only [rename, subst, ih₁, ih₂]
  | all κ σ ih =>
    simp only [rename, subst, ih]
    -- 持ち上げた関数どうしが等しいことを確かめる
    congr 2
    funext i
    cases i <;> rfl

/-- 代入してから付け替えるのは、代入の各結果を付け替えた代入を 1 回行うのと同じ。 -/
theorem rename_subst (σ : Ty) (s : Nat → Ty) (ζ : Nat → Nat) :
    (σ.subst s).rename ζ = σ.subst (fun i => (s i).rename ζ) := by
  induction σ generalizing s ζ with
  | var i => rfl
  | arr σ₁ σ₂ ih₁ ih₂ => simp only [rename, subst, ih₁, ih₂]
  | all κ σ ih =>
    simp only [rename, subst, ih]
    congr 2
    funext i
    cases i with
    | zero => rfl
    | succ i =>
      -- `(s i).shift` を付け替えたものと、付け替えたものを `shift` したものが等しい
      simp only [up, shift, rename_rename]
      rfl

/-- 代入を 2 回行うのは、代入を合成して 1 回行うのと同じ。 -/
theorem subst_subst (σ : Ty) (s t : Nat → Ty) :
    (σ.subst s).subst t = σ.subst (fun i => (s i).subst t) := by
  induction σ generalizing s t with
  | var i => rfl
  | arr σ₁ σ₂ ih₁ ih₂ => simp only [subst, ih₁, ih₂]
  | all κ σ ih =>
    simp only [subst, ih]
    congr 2
    funext i
    cases i with
    | zero => rfl
    | succ i =>
      -- `shift` してから `up t` で代入するのは、`t` で代入してから `shift` するのと同じ
      simp only [up, shift, subst_rename, rename_subst]

/-- 各変数を自分自身に置き換える代入は、何も変えない。 -/
theorem subst_var (σ : Ty) : σ.subst var = σ := by
  induction σ with
  | var i => rfl
  | arr σ₁ σ₂ ih₁ ih₂ => simp only [subst, ih₁, ih₂]
  | all κ σ ih =>
    have : up var = var := by
      funext i
      cases i <;> rfl
    simp only [subst, this, ih]

/-- 付け替えは「変数を変数に置き換える代入」の特殊な場合である。 -/
theorem rename_eq_subst (σ : Ty) (ξ : Nat → Nat) :
    σ.rename ξ = σ.subst (fun i => var (ξ i)) := by
  induction σ generalizing ξ with
  | var i => rfl
  | arr σ₁ σ₂ ih₁ ih₂ => simp only [rename, subst, ih₁, ih₂]
  | all κ σ ih =>
    simp only [rename, subst, ih]
    congr 2
    funext i
    cases i <;> rfl

/-! ## `shift` と代入の関係

型抽象 Λ の内側に入るとき、項変数の環境 Γ の各型は `shift` される（`SystemF.Typing` の TTAbs）。
次の補題は、そのように `shift` された型に対して付け替えや代入を行ったときの振る舞いを述べる。
-/

/-- `shift` してから持ち上げた付け替えを行うのは、付け替えてから `shift` するのと同じ。 -/
theorem shift_rename (σ : Ty) (ξ : Nat → Nat) :
    σ.shift.rename (upRen ξ) = (σ.rename ξ).shift := by
  simp only [shift, rename_rename]
  rfl

/-- `shift` してから持ち上げた代入を行うのは、代入してから `shift` するのと同じ。 -/
theorem shift_subst (σ : Ty) (s : Nat → Ty) :
    σ.shift.subst (up s) = (σ.subst s).shift := by
  simp only [shift, subst_rename, rename_subst]
  rfl

/-- `shift` で 1 つずらしてから 0 番を置き換えても、0 番はもともと現れないので元に戻る。 -/
theorem shift_subst_single (σ σ' : Ty) : σ.shift.subst (single σ') = σ := by
  simp only [shift, subst_rename]
  exact subst_var σ

/-! ## 補題5.1（型代入の交換） -/

/-- **補題5.1（型代入の交換）**

PDF: `α ∉ ftv(τ₂)` ならば `[α ↦ [β ↦ τ₂]τ₁]([β ↦ τ₂]σ) = [β ↦ τ₂][α ↦ τ₁]σ`。

ここでは `β ↦ τ₂` を任意の並列代入 `s` に一般化している。
左辺の `σ.subst (up s)` は「∀α の内側で s を適用する」ことを表し、
PDF の条件 `α ∉ ftv(τ₂)` は、de Bruijn index では `up` が α（0 番）を動かさないことで
自動的に満たされるので、仮定として現れない。

証明: 両辺を `subst_subst` で 1 回の代入にまとめ、各変数の行き先が一致することを確かめる。
* 0 番（PDF の α）: 両辺とも `τ₁.subst s` になる。
* i+1 番（それ以外の変数）: 左辺は `s i` を `shift` してから 0 番を置き換えるので、
  `shift_subst_single` により `s i` に戻る。右辺も `s i` である。
-/
theorem subst_instantiate (σ τ₁ : Ty) (s : Nat → Ty) :
    (σ.instantiate τ₁).subst s = (σ.subst (up s)).instantiate (τ₁.subst s) := by
  simp only [instantiate, subst_subst]
  congr 1
  funext i
  cases i with
  | zero => rfl
  | succ i => exact (shift_subst_single (s i) _).symm

/-- 補題5.1 の付け替え版。付け替えは代入の特殊な場合なので、`subst_instantiate` から従う。 -/
theorem rename_instantiate (σ τ₁ : Ty) (ξ : Nat → Nat) :
    (σ.instantiate τ₁).rename ξ = (σ.rename (upRen ξ)).instantiate (τ₁.rename ξ) := by
  have h : up (fun i => var (ξ i)) = fun i => var (upRen ξ i) := by
    funext i
    cases i <;> rfl
  simp only [rename_eq_subst, subst_instantiate, h]

end Ty
end SystemF
