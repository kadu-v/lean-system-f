/-!
# 構文（PDF Figure 1）

System F のカインド・型・項を定義する。

## de Bruijn index について

PDF では変数に名前（x, α など）を付けているが、ここでは **de Bruijn index** を使う。
変数を名前ではなく「自分から数えて何番目の束縛子（λ や ∀）で束縛されているか」
という自然数で表す方法である。いちばん近い束縛子が 0 番になる。

例:
* `λx:σ. x`            は `lam σ (var 0)`
* `λx:σ. λy:τ. x`      は `lam σ (lam τ (var 1))`（x は 1 つ外側の λ で束縛されている）
* `∀α::⋆. ∀β::⋆. α → β` は `all ⋆ (all ⋆ (arr (var 1) (var 0)))`

この表し方には次の利点がある。
* `λx.x` と `λy.y` のように名前だけが違う項が、はじめから同じ値になる（α 同値の問題がない）。
* 代入で変数が捕獲される（自由変数が別の束縛子に取り込まれてしまう）ことがない。

その代わりに、束縛子の内側に入ると index が 1 つずれる、という番号の計算が必要になる。
それを扱うのが `SystemF.Renaming` と `SystemF.Ty.Subst` / `SystemF.Tm.Subst` である。

型変数と項変数は **別々に** 番号を振る。
型変数の番号は型の束縛子（∀ と Λ）だけを、項変数の番号は項の束縛子（λ）だけを数える。
-/

namespace SystemF

/-- カインド `κ ::= ⋆`。PDF と同じく、カインドは `⋆`（「型」のカインド）の 1 種類だけである。 -/
inductive Kind where
  /-- `⋆` -/
  | star
  deriving DecidableEq, Repr

/-- 型 `σ ::= α | σ → σ | ∀α::κ.σ` -/
inductive Ty where
  /-- 型変数 `α`。番号 `i` は「i 個外側の型束縛子で束縛された変数」を表す。 -/
  | var (i : Nat)
  /-- 関数型 `σ₁ → σ₂` -/
  | arr (σ₁ σ₂ : Ty)
  /-- 全称型 `∀α::κ.σ`。束縛される変数 α は `σ` の中では `var 0` になる。 -/
  | all (κ : Kind) (σ : Ty)
  deriving DecidableEq, Repr

/-- 項 `e ::= x | λx:σ.e | e e | Λα::κ.e | e[σ]` -/
inductive Tm where
  /-- 項変数 `x`。番号 `i` は「i 個外側の λ で束縛された変数」を表す。 -/
  | var (i : Nat)
  /-- 関数抽象 `λx:σ.e`。束縛される x は `e` の中では `var 0` になる。 -/
  | lam (σ : Ty) (e : Tm)
  /-- 関数適用 `e₁ e₂` -/
  | app (e₁ e₂ : Tm)
  /-- 型抽象 `Λα::κ.e`。束縛される α は `e` の中の型で `Ty.var 0` になる。 -/
  | tlam (κ : Kind) (e : Tm)
  /-- 型適用 `e[σ]` -/
  | tapp (e : Tm) (σ : Ty)
  deriving DecidableEq, Repr

end SystemF
