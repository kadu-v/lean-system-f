import SystemF.Weakening

/-!
# 補題1（項代入補題）と補題2.2（型代入補題）

どちらも、まず **並列代入についての一般形** を型付けの導出に関する帰納法で示し、
PDF の 1 変数の代入はその特殊な場合として得る。

一般形にしておくのは、帰納法の途中で束縛子（λ や Λ）の内側に入ると、
代入が「持ち上げた代入」（`Tm.up` / `Tm.upTy` / `Ty.up`）に変わるためである。
1 変数の代入のままでは帰納法の仮定が使えない形になってしまう。
-/

namespace SystemF

/-- 項変数の環境を `shiftCtx` してから持ち上げた型代入を行うのは、代入してから `shiftCtx` するのと同じ。 -/
theorem shiftCtx_subst (Γ : List Ty) (s : Nat → Ty) :
    (shiftCtx Γ).map (Ty.subst (Ty.up s)) = shiftCtx (Γ.map (Ty.subst s)) := by
  simp only [shiftCtx, List.map_map]
  congr 1
  funext σ
  exact Ty.shift_subst σ s

/-- `shiftCtx` で 1 つずらしてから型変数 0 番を置き換えると、元の環境に戻る。 -/
theorem shiftCtx_subst_single (Γ : List Ty) (σ' : Ty) :
    (shiftCtx Γ).map (Ty.subst (Ty.single σ')) = Γ := by
  simp only [shiftCtx, List.map_map]
  conv => rhs; rw [← List.map_id Γ]
  congr 1
  funext σ
  exact Ty.shift_subst_single σ σ'

namespace Typing

variable {Δ Δ' : List Kind} {Γ Γ' : List Ty} {e v : Tm} {σ σ' τ : Ty} {κ : Kind}

/-! ## 補題1（項代入補題） -/

/-- 代入 `s` で変数を置き換えても型が崩れないこと。

代入 `s` は「i 番の変数を項 `s i` に置き換える」関数である。
`SubstOk Δ Γ Γ' s` は次を意味する:

  古い環境 `Γ` で i 番の変数の型が σ ならば、
  置き換え先の項 `s i` も、新しい環境 `Γ'` で同じ型 σ を持つ。

変数を同じ型の項に置き換えるだけなので、項全体の型も変わらない（`Typing.subst`）。
-/
def SubstOk (Δ : List Kind) (Γ Γ' : List Ty) (s : Nat → Tm) : Prop :=
  ∀ {i : Nat} {σ : Ty}, Γ[i]? = some σ → Δ ; Γ' ⊢ s i : σ

/-- λ の内側に入るときに代入を持ち上げても `SubstOk` は保たれる。 -/
theorem SubstOk.up {s : Nat → Tm} (h : SubstOk Δ Γ Γ' s) :
    SubstOk Δ (τ :: Γ) (τ :: Γ') (Tm.up s) := by
  intro i σ hi
  cases i with
  | zero =>
    -- 0 番は λ 自身が束縛する変数で、`var 0` のまま
    exact .TVar (by simp_all)
  | succ i =>
    -- それ以外は `s i` を `shift` したもの。弱化補題（補題3）で示す
    exact (h (by simpa using hi)).weaken

/-- Λ の内側に入るときに代入を持ち上げても `SubstOk` は保たれる。 -/
theorem SubstOk.upTy {s : Nat → Tm} (h : SubstOk Δ Γ Γ' s) :
    SubstOk (κ :: Δ) (shiftCtx Γ) (shiftCtx Γ') (Tm.upTy s) := by
  intro i σ hi
  -- 環境 `shiftCtx Γ` の i 番目は、Γ の i 番目の型 σ₀ を `shift` したもの
  simp only [shiftCtx, List.getElem?_map, Option.map_eq_some_iff] at hi
  obtain ⟨σ₀, hσ₀, rfl⟩ := hi
  -- 置き換える項 `s i` を型変数について弱化する
  exact (h hσ₀).weakenTy

/-- `[x ↦ v]` で置き換えても型が崩れないこと（`v` の型が x の型 τ と同じならば）。

`Tm.single v` は PDF の `[x ↦ v]` に当たる代入で、
* 0 番の変数（x）を `v` に置き換え、
* 1 番以降の変数は番号を 1 つ詰める（x がいなくなるため）。

古い環境は x を含む `τ :: Γ`（PDF の `Γ, x : τ`）、新しい環境は x を除いた `Γ` である。
確かめることは次の 2 つ:

| 古い環境での変数 | 置き換え先 | 新しい環境 Γ での型                |
|------------------|------------|------------------------------------|
| 0 番（x）: τ     | `v`        | τ（仮定 `hv` そのもの）            |
| i+1 番: Γ[i]     | `var i`    | Γ[i]（TVar 規則でそのまま型が付く）|
-/
theorem SubstOk.single (hv : Δ ; Γ ⊢ v : τ) : SubstOk Δ (τ :: Γ) Γ (Tm.single v) := by
  intro i σ hi
  cases i with
  | zero =>
    -- x（0 番）の場合: 型は τ なので、v を置いてよいことは仮定 hv から分かる
    obtain rfl : τ = σ := Option.some.inj hi
    exact hv
  | succ i =>
    -- それ以外の変数の場合: var i に置き換わり、Γ の i 番目の型がそのまま付く
    exact .TVar (by simpa using hi)

/-- **項代入補題（一般形）**: `SubstOk` な代入で型付けが保たれる。

型付けの導出に関する帰納法で示す。PDF の補題1 の証明と同じく、
TVar の場合は代入の仮定から、それ以外は帰納法の仮定と同じ規則で示す。
-/
theorem subst {s : Nat → Tm} (h : Δ ; Γ ⊢ e : σ) (hs : SubstOk Δ Γ Γ' s) :
    Δ ; Γ' ⊢ e.subst s : σ := by
  induction h generalizing Γ' s with
  | TVar hi => exact hs hi
  | TAbs _ ih => exact .TAbs (ih hs.up)
  | TApp _ _ ih₁ ih₂ => exact .TApp (ih₁ hs) (ih₂ hs)
  | TTAbs _ ih => exact .TTAbs (ih hs.upTy)
  | TTApp _ hσ' ih => exact .TTApp (ih hs) hσ'

/-- **補題1（項代入補題）**

PDF: `Γ₁, x : τ, Γ₂ ⊢ e : σ` かつ `Γ₁ ⊢ e' : τ` ならば `Γ₁, Γ₂ ⊢ [x ↦ e']e : σ`。

ここで示すのは **PDF で Γ₁ = Γ、Γ₂ = •（空）とした場合**、
つまり `Γ, x : τ ⊢ e : σ` かつ `Γ ⊢ v : τ` ならば `Γ ⊢ [x ↦ v]e : σ` である。
（Lean のリスト `τ :: Γ` は先頭が最も新しい変数なので、PDF の `Γ, x : τ` に当たる。
x は最も新しい変数なので de Bruijn index は 0 番。）
保存定理（EAppAbs の場合）で使うのはこの形である。

Γ₂ が空でない場合は証明していない。一般形 `subst` に適切な代入を与えれば導けるはずだが、
保存定理には不要なので省略した。
-/
theorem instantiate (h : Δ ; τ :: Γ ⊢ e : σ) (hv : Δ ; Γ ⊢ v : τ) :
    Δ ; Γ ⊢ e.instantiate v : σ :=
  h.subst (SubstOk.single hv)

/-! ## 補題2.2（型代入補題） -/

/-- **型代入補題（一般形）**

型代入 `s` が型変数の環境 `Δ` のカインドを `Δ'` で保つなら、
`Δ ; Γ ⊢ e : σ` から `Δ' ; s(Γ) ⊢ s(e) : s(σ)` が得られる。

型付けの導出に関する帰納法で示す。
-/
theorem substTy {s : Nat → Ty} (h : Δ ; Γ ⊢ e : σ) (hs : Kinding.SubstOk Δ Δ' s) :
    Δ' ; Γ.map (Ty.subst s) ⊢ e.substTy s : σ.subst s := by
  induction h generalizing Δ' s with
  | TVar hi =>
    -- PDF の TVar の場合 (a)(b) に相当する。環境全体に代入するので場合分けは不要になる
    exact .TVar (by simp [hi])
  | TAbs _ ih => exact .TAbs (ih hs)
  | TApp _ _ ih₁ ih₂ => exact .TApp (ih₁ hs) (ih₂ hs)
  | TTAbs _ ih =>
    -- Λ の内側では `Ty.up s` で代入する。環境の形を `shiftCtx_subst` で揃える
    have := ih hs.up
    rw [shiftCtx_subst] at this
    exact .TTAbs this
  | TTApp _ hσ' ih =>
    -- PDF の TTApp の場合: 補題2.1 と補題5.1 を使う
    rw [Ty.subst_instantiate]
    exact .TTApp (ih hs) (hσ'.subst hs)

/-- **補題2.2（型代入補題）**

PDF: `Γ₁, α :: κ, Γ₂ ⊢ e : σ` かつ `Γ₁ ⊢ σ' :: κ` ならば
`Γ₁, [α ↦ σ']Γ₂ ⊢ [α ↦ σ']e : [α ↦ σ']σ`。

ここで示すのは **PDF で Γ₂ = •（空）とした場合**、
つまり `Γ, α :: κ ⊢ e : σ` かつ `Γ ⊢ σ' :: κ` ならば `Γ ⊢ [α ↦ σ']e : [α ↦ σ']σ` である。
（α は最も新しい型変数なので de Bruijn index は 0 番で、型変数の環境は `κ :: Δ` になる。）
保存定理（ETAppAbs の場合）で使うのはこの形である。
項変数の環境は α を追加したときに `shiftCtx Γ` になっているが、α を置き換えると元の Γ に戻る。

Γ₂ が空でない場合は証明していない（保存定理には不要なため）。
-/
theorem instantiateTy (h : κ :: Δ ; shiftCtx Γ ⊢ e : σ) (hσ' : Δ ⊢ σ' ∷ κ) :
    Δ ; Γ ⊢ e.instantiateTy σ' : σ.instantiate σ' := by
  have := h.substTy (Kinding.SubstOk.single hσ')
  rw [shiftCtx_subst_single] at this
  exact this

end Typing
end SystemF
