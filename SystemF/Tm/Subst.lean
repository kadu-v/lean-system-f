import SystemF.Ty.Subst

/-!
# 項の付け替えと代入

項には 2 種類の変数（型変数と項変数）があるので、付け替え・代入もそれぞれに用意する。

| 操作                   | 対象     | PDF での記法   |
|------------------------|----------|----------------|
| `Tm.renameTy ξ e`      | 型変数   | ―              |
| `Tm.substTy s e`       | 型変数   | ―              |
| `Tm.instantiateTy e σ` | 型変数   | `[α ↦ σ]e`     |
| `Tm.rename ξ e`        | 項変数   | ―              |
| `Tm.subst s e`         | 項変数   | ―              |
| `Tm.instantiate e v`   | 項変数   | `[x ↦ v]e`     |

型変数と項変数は別々に番号を振っているので、
* 型の束縛子（Λ）の内側では型変数の番号だけがずれ、
* 項の束縛子（λ）の内側では項変数の番号だけがずれる。

PDF の補題5.2（項に対する型代入の交換）は、保存定理の証明には使われないので省略した。
（型の上の補題5.1 は `Ty.subst_instantiate` として証明済みで、型代入補題の中で使う。）
-/

namespace SystemF
namespace Tm

/-! ## 型変数に対する付け替えと代入 -/

/-- 項中に現れる型の自由変数の番号を `ξ` で付け替える。Λ の内側では `upRen ξ` を使う。 -/
def renameTy (ξ : Nat → Nat) : Tm → Tm
  | var i => var i
  | lam σ e => lam (σ.rename ξ) (e.renameTy ξ)
  | app e₁ e₂ => app (e₁.renameTy ξ) (e₂.renameTy ξ)
  | tlam κ e => tlam κ (e.renameTy (upRen ξ))
  | tapp e σ => tapp (e.renameTy ξ) (σ.rename ξ)

/-- 項中の型の自由変数の番号をすべて 1 増やす（型変数を 1 つ環境に追加したとき）。 -/
def shiftTy (e : Tm) : Tm := e.renameTy (· + 1)

/-- 項中に現れる型の自由変数 `i` を `s i` で置き換える。Λ の内側では `Ty.up s` を使う。 -/
def substTy (s : Nat → Ty) : Tm → Tm
  | var i => var i
  | lam σ e => lam (σ.subst s) (e.substTy s)
  | app e₁ e₂ => app (e₁.substTy s) (e₂.substTy s)
  | tlam κ e => tlam κ (e.substTy (Ty.up s))
  | tapp e σ => tapp (e.substTy s) (σ.subst s)

/-- PDF の `[α ↦ σ]e`。`Λα::κ.e` の本体 `e` の型変数 0 番を `σ` で置き換える。 -/
def instantiateTy (e : Tm) (σ : Ty) : Tm := e.substTy (Ty.single σ)

/-! ## 項変数に対する付け替えと代入 -/

/-- 項の自由変数の番号を `ξ` で付け替える。λ の内側では `upRen ξ` を使う。
Λ は項変数を束縛しないので、Λ の内側でも `ξ` のままでよい。 -/
def rename (ξ : Nat → Nat) : Tm → Tm
  | var i => var (ξ i)
  | lam σ e => lam σ (e.rename (upRen ξ))
  | app e₁ e₂ => app (e₁.rename ξ) (e₂.rename ξ)
  | tlam κ e => tlam κ (e.rename ξ)
  | tapp e σ => tapp (e.rename ξ) σ

/-- 項の自由変数の番号をすべて 1 増やす（項変数を 1 つ環境に追加したとき）。 -/
def shift (e : Tm) : Tm := e.rename (· + 1)

/-- λ の内側に入るときの代入の持ち上げ（`Ty.up` と同じ考え方）。 -/
def up (s : Nat → Tm) : Nat → Tm
  | 0 => var 0
  | i + 1 => (s i).shift

/-- Λ の内側に入るときの代入の持ち上げ。

Λ は項変数を束縛しないので番号はずれないが、型変数が 1 つ増えるので、
置き換える項 `s i` の中の型変数の番号を 1 増やしておく必要がある。
-/
def upTy (s : Nat → Tm) : Nat → Tm := fun i => (s i).shiftTy

/-- 並列代入: 項の自由変数 `i` を `s i` で同時に置き換える。 -/
def subst (s : Nat → Tm) : Tm → Tm
  | var i => s i
  | lam σ e => lam σ (e.subst (up s))
  | app e₁ e₂ => app (e₁.subst s) (e₂.subst s)
  | tlam κ e => tlam κ (e.subst (upTy s))
  | tapp e σ => tapp (e.subst s) σ

/-- 0 番の項変数を `v` に置き換え、残りの番号を 1 減らす代入。 -/
def single (v : Tm) : Nat → Tm
  | 0 => v
  | i + 1 => var i

/-- PDF の `[x ↦ v]e`。`λx:σ.e` の本体 `e` の項変数 0 番を `v` で置き換える。 -/
def instantiate (e v : Tm) : Tm := e.subst (single v)

end Tm
end SystemF
