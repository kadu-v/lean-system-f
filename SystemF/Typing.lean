import SystemF.Kinding
import SystemF.Tm.Subst

/-!
# 型規則（PDF Figure 4）と補題4（逆転補題）

判断 `Δ ; Γ ⊢ e : σ`（PDF の `Γ ⊢ e : σ`）を定義する。

## 環境の分け方（PDF との違い）

PDF の環境 `Γ ::= • | x : σ, Γ | α :: κ, Γ` は項変数と型変数が混ざっている。
de Bruijn index では型変数と項変数を別々に数えるので、環境も 2 つに分ける。
* `Δ : List Kind` : 型変数の環境。i 番目が型変数 i 番のカインド。
* `Γ : List Ty`   : 項変数の環境。i 番目が項変数 i 番の型。

PDF の `Γ, x : σ` は `Δ ; σ :: Γ`、`Γ, α :: κ` は `κ :: Δ ; shiftCtx Γ` に対応する。
後者で Γ を `shiftCtx` するのは、型変数が 1 つ増えると、Γ に書かれている型の中の
型変数の番号が 1 つずつずれるためである。
-/

namespace SystemF

/-- 項変数の環境中のすべての型を `shift` する。型変数を 1 つ環境に追加したときに使う。 -/
def shiftCtx (Γ : List Ty) : List Ty := Γ.map Ty.shift

/-- 型付け `Δ ; Γ ⊢ e : σ`（PDF Figure 4） -/
inductive Typing : List Kind → List Ty → Tm → Ty → Prop
  /-- TVar: `x : σ ∈ Γ` ならば `Γ ⊢ x : σ` -/
  | TVar {Δ : List Kind} {Γ : List Ty} {i : Nat} {σ : Ty} :
      Γ[i]? = some σ →
      Typing Δ Γ (.var i) σ
  /-- TAbs: `Γ, x : σ₁ ⊢ e : σ₂` ならば `Γ ⊢ λx:σ₁.e : σ₁ → σ₂` -/
  | TAbs {Δ : List Kind} {Γ : List Ty} {σ₁ σ₂ : Ty} {e : Tm} :
      Typing Δ (σ₁ :: Γ) e σ₂ →
      Typing Δ Γ (.lam σ₁ e) (.arr σ₁ σ₂)
  /-- TApp: `Γ ⊢ e₁ : σ₁ → σ₂` かつ `Γ ⊢ e₂ : σ₁` ならば `Γ ⊢ e₁ e₂ : σ₂` -/
  | TApp {Δ : List Kind} {Γ : List Ty} {σ₁ σ₂ : Ty} {e₁ e₂ : Tm} :
      Typing Δ Γ e₁ (.arr σ₁ σ₂) →
      Typing Δ Γ e₂ σ₁ →
      Typing Δ Γ (.app e₁ e₂) σ₂
  /-- TTAbs: `Γ, α :: κ ⊢ e : σ` ならば `Γ ⊢ Λα::κ.e : ∀α::κ.σ` -/
  | TTAbs {Δ : List Kind} {Γ : List Ty} {κ : Kind} {σ : Ty} {e : Tm} :
      Typing (κ :: Δ) (shiftCtx Γ) e σ →
      Typing Δ Γ (.tlam κ e) (.all κ σ)
  /-- TTApp: `Γ ⊢ e : ∀α::κ.σ` かつ `Γ ⊢ σ' :: κ` ならば `Γ ⊢ e[σ'] : [α ↦ σ']σ` -/
  | TTApp {Δ : List Kind} {Γ : List Ty} {κ : Kind} {σ σ' : Ty} {e : Tm} :
      Typing Δ Γ e (.all κ σ) →
      Kinding Δ σ' κ →
      Typing Δ Γ (.tapp e σ') (σ.instantiate σ')

@[inherit_doc] notation:50 Δ:51 " ; " Γ:51 " ⊢ " e:51 " : " σ:51 => Typing Δ Γ e σ

namespace Typing

variable {Δ : List Kind} {Γ : List Ty} {e : Tm} {σ τ : Ty} {κ κ' : Kind}

/-! ## 補題4（逆転補題）

型付けの導出の最後の規則は、項の形でほぼ決まる。
`cases h` で、項の形に合う規則だけが場合として残ることを利用して示す。
-/

/-- **補題4.1（逆転補題）**: `Γ ⊢ λx:τ.e : τ' → σ` ならば `τ = τ'` かつ `Γ, x : τ' ⊢ e : σ`。

PDF では注釈の型と関数型の引数の型を同じ τ と書いているが、
ここでは両者が等しいことも結論に含めている。
-/
theorem inv_lam {τ' : Ty} (h : Δ ; Γ ⊢ .lam τ e : .arr τ' σ) :
    τ = τ' ∧ Δ ; τ' :: Γ ⊢ e : σ := by
  cases h with
  | TAbs he => exact ⟨rfl, he⟩

/-- **補題4.2（逆転補題）**: `Γ ⊢ Λα::κ.e : ∀α::κ'.σ` ならば `κ = κ'` かつ `Γ, α :: κ' ⊢ e : σ`。 -/
theorem inv_tlam (h : Δ ; Γ ⊢ .tlam κ e : .all κ' σ) :
    κ = κ' ∧ κ' :: Δ ; shiftCtx Γ ⊢ e : σ := by
  cases h with
  | TTAbs he => exact ⟨rfl, he⟩

end Typing
end SystemF
