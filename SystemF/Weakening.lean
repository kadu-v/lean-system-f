import SystemF.Typing

/-!
# 付け替え補題と補題3（弱化補題）

PDF の補題3（弱化補題）: `Γ ⊢ e : σ` かつ `dom(Δ) # dom(Γ)` ならば `Γ, Δ ⊢ e : σ`。

de Bruijn index では、環境に変数を追加すると既存の変数の番号がずれるので、
弱化は「番号を付け替えた項が、新しい環境で同じ型を持つ」という形になる。
そこでまず、より一般的な **付け替え補題** を 2 つ示し、弱化はその特殊な場合として得る。

* `Typing.renameTy` : 型変数の付け替え。環境 Δ を変えるときに使う。
* `Typing.rename`   : 項変数の付け替え。環境 Γ を変えるときに使う。

PDF の条件 `dom(Δ) # dom(Γ)`（変数名が重ならない）は、名前を使わない de Bruijn index では不要になる。
-/

namespace SystemF

/-! ## 環境についての補助補題 -/

/-- 項変数の環境を `shiftCtx` してから付け替えるのは、付け替えてから `shiftCtx` するのと同じ。

型付けの付け替え補題の TTAbs の場合で、環境の形を揃えるために使う。
-/
theorem shiftCtx_rename (Γ : List Ty) (ξ : Nat → Nat) :
    (shiftCtx Γ).map (Ty.rename (upRen ξ)) = shiftCtx (Γ.map (Ty.rename ξ)) := by
  simp only [shiftCtx, List.map_map]
  congr 1
  funext σ
  exact Ty.shift_rename σ ξ

namespace Typing

variable {Δ Δ' : List Kind} {Γ Γ' : List Ty} {e : Tm} {σ τ : Ty} {κ : Kind}

/-! ## 型変数の付け替え -/

/-- **型変数の付け替え補題**

`ξ` が型変数の環境 `Δ` のカインドを `Δ'` で保つなら、
`Δ ; Γ ⊢ e : σ` から `Δ' ; ξ(Γ) ⊢ ξ(e) : ξ(σ)` が得られる（`ξ(·)` は型変数の付け替え）。

型付けの導出に関する帰納法で示す。
-/
theorem renameTy {ξ : Nat → Nat} (h : Δ ; Γ ⊢ e : σ) (hξ : RenOk Δ Δ' ξ) :
    Δ' ; Γ.map (Ty.rename ξ) ⊢ e.renameTy ξ : σ.rename ξ := by
  induction h generalizing Δ' ξ with
  | TVar hi =>
    -- 環境の i 番目の型も付け替えられている
    exact .TVar (by simp [hi])
  | TAbs _ ih => exact .TAbs (ih hξ)
  | TApp _ _ ih₁ ih₂ => exact .TApp (ih₁ hξ) (ih₂ hξ)
  | TTAbs _ ih =>
    -- Λ の内側では、型変数の環境に κ が加わるので `upRen ξ` で付け替える。
    -- 帰納法の仮定の環境 `(shiftCtx Γ).map …` を `shiftCtx (Γ.map …)` に書き換えて TTAbs を適用する。
    have := ih hξ.up
    rw [shiftCtx_rename] at this
    exact .TTAbs this
  | TTApp _ hσ' ih =>
    -- 結論の型 `[α ↦ σ']σ` を付け替えたものを、補題5.1 の付け替え版で書き換える
    rw [Ty.rename_instantiate]
    exact .TTApp (ih hξ) (hσ'.rename hξ)

/-- 型変数を 1 つ環境に追加する弱化。 -/
theorem weakenTy (h : Δ ; Γ ⊢ e : σ) : κ :: Δ ; shiftCtx Γ ⊢ e.shiftTy : σ.shift :=
  h.renameTy RenOk.succ

/-! ## 項変数の付け替え -/

/-- **項変数の付け替え補題**

`ξ` が項変数の環境 `Γ` の型を `Γ'` で保つなら、`Δ ; Γ ⊢ e : σ` から `Δ ; Γ' ⊢ ξ(e) : σ` が得られる。

型付けの導出に関する帰納法で示す。
-/
theorem rename {ξ : Nat → Nat} (h : Δ ; Γ ⊢ e : σ) (hξ : RenOk Γ Γ' ξ) :
    Δ ; Γ' ⊢ e.rename ξ : σ := by
  induction h generalizing Γ' ξ with
  | TVar hi => exact .TVar (hξ hi)
  | TAbs _ ih =>
    -- λ の内側では項変数の環境に 1 つ加わるので `upRen ξ` で付け替える
    exact .TAbs (ih hξ.up)
  | TApp _ _ ih₁ ih₂ => exact .TApp (ih₁ hξ) (ih₂ hξ)
  | TTAbs _ ih =>
    -- Λ の内側では項変数の番号はずれないが、環境の型が `shift` されている
    exact .TTAbs (ih (hξ.map Ty.shift))
  | TTApp _ hσ' ih => exact .TTApp (ih hξ) hσ'

/-- **補題3（弱化補題）**: 項変数を 1 つ環境に追加しても、（`shift` した）項の型は変わらない。

PDF の `Γ, Δ` のように複数の変数を一度に追加する場合は、これを繰り返し使えばよい。
また任意の付け替えについての `rename` 自体が、補題3 の一般形になっている。
-/
theorem weaken (h : Δ ; Γ ⊢ e : σ) : Δ ; τ :: Γ ⊢ e.shift : σ :=
  h.rename RenOk.succ

end Typing
end SystemF
