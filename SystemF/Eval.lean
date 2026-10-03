import SystemF.Tm.Subst

/-!
# 値と評価規則（PDF Figure 1 の Value、Figure 2）

## 値について（PDF との違い）

PDF では値を `v ::= x | λx:σ.e | Λα::κ.e` と定義し、変数 `x` も値に含めている。
しかしそうすると、進行定理（定理1）が成り立たなくなる。
たとえば `x : σ₁ → σ₂, y : σ₁ ⊢ x y : σ₂` は型が付くが、
`x y` は値ではなく（関数適用は値でない）、どの評価規則も適用できない。

そこでここでは標準的な定式化に従い、**値は λ と Λ だけ** とする。
その代わりに進行定理は、項変数を含まない項（項変数の環境が空）に対して示す
（`SystemF.Progress` を参照）。

## 評価規則

規則の名前は PDF に合わせている。PDF と同じく EApp2 は `e₁` が値であることを要求しないので、
評価は決定的ではない（1 つの項から複数の評価の仕方がありうる）。保存定理はそれでも成り立つ。
-/

namespace SystemF

/-- 値 `v ::= λx:σ.e | Λα::κ.e` -/
inductive Value : Tm → Prop
  /-- `λx:σ.e` は値 -/
  | lam {σ : Ty} {e : Tm} : Value (.lam σ e)
  /-- `Λα::κ.e` は値 -/
  | tlam {κ : Kind} {e : Tm} : Value (.tlam κ e)

/-- 1 ステップの評価 `e ⟶ e'`（PDF Figure 2） -/
inductive Step : Tm → Tm → Prop
  /-- EAppAbs: `(λx:σ.e) v ⟶ [x ↦ v]e` -/
  | EAppAbs {σ : Ty} {e v : Tm} :
      Value v →
      Step (.app (.lam σ e) v) (e.instantiate v)
  /-- ETAppAbs: `(Λα::κ.e)[σ] ⟶ [α ↦ σ]e` -/
  | ETAppAbs {κ : Kind} {e : Tm} {σ : Ty} :
      Step (.tapp (.tlam κ e) σ) (e.instantiateTy σ)
  /-- EApp1: `e₁ ⟶ e₁'` ならば `e₁ e₂ ⟶ e₁' e₂` -/
  | EApp1 {e₁ e₁' e₂ : Tm} :
      Step e₁ e₁' →
      Step (.app e₁ e₂) (.app e₁' e₂)
  /-- EApp2: `e₂ ⟶ e₂'` ならば `e₁ e₂ ⟶ e₁ e₂'` -/
  | EApp2 {e₁ e₂ e₂' : Tm} :
      Step e₂ e₂' →
      Step (.app e₁ e₂) (.app e₁ e₂')
  /-- ETApp: `e ⟶ e'` ならば `e[σ] ⟶ e'[σ]` -/
  | ETApp {e e' : Tm} {σ : Ty} :
      Step e e' →
      Step (.tapp e σ) (.tapp e' σ)

@[inherit_doc] infix:50 " ⟶ " => Step

end SystemF
