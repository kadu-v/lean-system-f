import SystemF.Ty.Subst

/-!
# カインド規則（PDF Figure 3）と補題2.1

判断 `Δ ⊢ σ ∷ κ`（PDF の `Γ ⊢ σ :: κ`）を定義する。
`::` は Lean ではリストの先頭への追加に使われているので、記法には `∷` を使う。

PDF の環境 Γ は項変数と型変数が混ざっているが、カインド付けに使うのは型変数だけなので、
ここでは型変数のカインドを並べたリスト `Δ : List Kind` を環境とする。
`Δ[i]? = some κ` は「型変数 i 番のカインドが κ」を意味する（PDF の `α :: κ ∈ Γ`）。

このファイルでは次を示す。
* `Kinding.rename`      : カインドを保つ付け替えで、カインド付けが保たれる（型の弱化）。
* `Kinding.subst`       : カインドを保つ代入で、カインド付けが保たれる。
* `Kinding.instantiate` : **補題2.1（型代入補題、型の部分）**。
-/

namespace SystemF

/-- カインド付け `Δ ⊢ σ ∷ κ`（PDF Figure 3） -/
inductive Kinding : List Kind → Ty → Kind → Prop
  /-- KTVar: `α :: κ ∈ Γ` ならば `Γ ⊢ α :: κ` -/
  | KTVar {Δ : List Kind} {i : Nat} {κ : Kind} :
      Δ[i]? = some κ →
      Kinding Δ (.var i) κ
  /-- KTAbs: `Γ ⊢ σ₁ :: ⋆` かつ `Γ ⊢ σ₂ :: ⋆` ならば `Γ ⊢ σ₁ → σ₂ :: ⋆` -/
  | KTAbs {Δ : List Kind} {σ₁ σ₂ : Ty} :
      Kinding Δ σ₁ .star →
      Kinding Δ σ₂ .star →
      Kinding Δ (.arr σ₁ σ₂) .star
  /-- KTTAbs: `Γ, α :: κ ⊢ σ :: ⋆` ならば `Γ ⊢ ∀α::κ.σ :: ⋆` -/
  | KTTAbs {Δ : List Kind} {κ : Kind} {σ : Ty} :
      Kinding (κ :: Δ) σ .star →
      Kinding Δ (.all κ σ) .star

@[inherit_doc] notation:50 Δ:51 " ⊢ " σ:51 " ∷ " κ:51 => Kinding Δ σ κ

namespace Kinding

variable {Δ Δ' : List Kind} {σ σ' : Ty} {κ κ' : Kind}

/-! ## 付け替え（型の弱化） -/

/-- 付け替え `ξ` が環境 `Δ` のカインドを `Δ'` で保つなら、カインド付けも保たれる。

型の構造（正確にはカインド付けの導出）に関する帰納法で示す。
∀ の場合だけ、内側の環境 `κ :: Δ` に対して `upRen ξ` が `RenOk` であること（`RenOk.up`）を使う。
-/
theorem rename {ξ : Nat → Nat} (h : Δ ⊢ σ ∷ κ) (hξ : RenOk Δ Δ' ξ) :
    Δ' ⊢ σ.rename ξ ∷ κ := by
  induction h generalizing Δ' ξ with
  | KTVar hi => exact .KTVar (hξ hi)
  | KTAbs _ _ ih₁ ih₂ => exact .KTAbs (ih₁ hξ) (ih₂ hξ)
  | KTTAbs _ ih => exact .KTTAbs (ih hξ.up)

/-- 型変数を 1 つ環境に追加しても、（`shift` した）型のカインドは変わらない。 -/
theorem weaken (h : Δ ⊢ σ ∷ κ) : (κ' :: Δ) ⊢ σ.shift ∷ κ :=
  h.rename RenOk.succ

/-! ## 代入 -/

/-- 代入 `s` が「環境 `Δ` の各型変数を、`Δ'` で同じカインドを持つ型に置き換える」こと。 -/
def SubstOk (Δ Δ' : List Kind) (s : Nat → Ty) : Prop :=
  ∀ {i : Nat} {κ : Kind}, Δ[i]? = some κ → Δ' ⊢ s i ∷ κ

/-- ∀ の内側に入るときに代入を持ち上げても `SubstOk` は保たれる。 -/
theorem SubstOk.up {s : Nat → Ty} (h : SubstOk Δ Δ' s) :
    SubstOk (κ :: Δ) (κ :: Δ') (Ty.up s) := by
  intro i κ' hi
  cases i with
  | zero =>
    -- 0 番は ∀ 自身が束縛する変数で、`var 0` のまま
    exact .KTVar (by simp_all)
  | succ i =>
    -- それ以外は `s i` を `shift` したもの。型の弱化で示す
    exact (h (by simpa using hi)).weaken

/-- `Δ ⊢ σ' ∷ κ` ならば、0 番を `σ'` で置き換える代入は `κ :: Δ` から `Δ` への `SubstOk`。 -/
theorem SubstOk.single (h : Δ ⊢ σ' ∷ κ) : SubstOk (κ :: Δ) Δ (Ty.single σ') := by
  intro i κ' hi
  cases i with
  | zero =>
    obtain rfl : κ = κ' := Option.some.inj hi
    exact h
  | succ i => exact .KTVar (by simpa using hi)

/-- `SubstOk` な代入でカインド付けが保たれる。 -/
theorem subst {s : Nat → Ty} (h : Δ ⊢ σ ∷ κ) (hs : SubstOk Δ Δ' s) :
    Δ' ⊢ σ.subst s ∷ κ := by
  induction h generalizing Δ' s with
  | KTVar hi => exact hs hi
  | KTAbs _ _ ih₁ ih₂ => exact .KTAbs (ih₁ hs) (ih₂ hs)
  | KTTAbs _ ih => exact .KTTAbs (ih hs.up)

/-- **補題2.1（型代入補題、型の部分）**

PDF: `Γ₁, α :: κ, Γ₂ ⊢ σ :: κ'` かつ `Γ₁ ⊢ σ' :: κ` ならば `Γ₁, [α ↦ σ']Γ₂ ⊢ [α ↦ σ']σ :: κ'`。

ここで示すのは **PDF で Γ₂ = •（空）とした場合**、
つまり `Γ, α :: κ ⊢ σ :: κ'` かつ `Γ ⊢ σ' :: κ` ならば `Γ ⊢ [α ↦ σ']σ :: κ'` である。
（α は最も新しい型変数なので de Bruijn index は 0 番で、環境は `κ :: Δ` になる。）

Γ₂ が空でない場合は証明していない（保存定理には不要なため）。
-/
theorem instantiate (h : (κ :: Δ) ⊢ σ ∷ κ') (h' : Δ ⊢ σ' ∷ κ) :
    Δ ⊢ σ.instantiate σ' ∷ κ' :=
  h.subst (SubstOk.single h')

end Kinding
end SystemF
