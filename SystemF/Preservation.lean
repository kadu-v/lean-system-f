import SystemF.Substitution
import SystemF.Eval

/-!
# 定理2（保存）

PDF: `Γ ⊢ e : σ` かつ `e ⟶ e'` ならば `Γ ⊢ e' : σ`。

PDF と同じく、型付けの導出に関する帰納法で示し、
各場合でさらに適用された評価規則で場合分けする。
-/

namespace SystemF

variable {Δ : List Kind} {Γ : List Ty} {e e' : Tm} {σ : Ty}

/-- **定理2（保存）**: 評価しても型は変わらない。 -/
theorem preservation (h : Δ ; Γ ⊢ e : σ) (hs : e ⟶ e') : Δ ; Γ ⊢ e' : σ := by
  induction h generalizing e' with
  | TVar _ =>
    -- 変数に適用できる評価規則はない
    cases hs
  | TAbs _ =>
    -- λ 抽象に適用できる評価規則はない
    cases hs
  | TApp h₁ h₂ ih₁ ih₂ =>
    -- 適用された評価規則で場合分けする
    cases hs with
    | EAppAbs _ =>
      -- e₁ = λx:τ.b。逆転補題（補題4.1）で `Γ, x : σ₁ ⊢ b : σ₂` を得て、
      -- 項代入補題（補題1）で `Γ ⊢ [x ↦ e₂]b : σ₂` を得る
      obtain ⟨rfl, hb⟩ := h₁.inv_lam
      exact hb.instantiate h₂
    | EApp1 hs₁ =>
      -- 帰納法の仮定で `Γ ⊢ e₁' : σ₁ → σ₂` を得て、TApp を適用する
      exact .TApp (ih₁ hs₁) h₂
    | EApp2 hs₂ =>
      -- EApp1 と同様
      exact .TApp h₁ (ih₂ hs₂)
  | TTAbs _ =>
    -- Λ 抽象に適用できる評価規則はない
    cases hs
  | TTApp h₁ hσ' ih =>
    cases hs with
    | ETAppAbs =>
      -- e₁ = Λα::κ.b。逆転補題（補題4.2）で `Γ, α :: κ ⊢ b : σ''` を得て、
      -- 型代入補題（補題2.2）で `Γ ⊢ [α ↦ σ']b : [α ↦ σ']σ''` を得る
      obtain ⟨rfl, hb⟩ := h₁.inv_tlam
      exact hb.instantiateTy hσ'
    | ETApp hs₁ =>
      -- 帰納法の仮定で `Γ ⊢ e₁' : ∀α::κ.σ''` を得て、TTApp を適用する
      exact .TTApp (ih hs₁) hσ'

end SystemF
