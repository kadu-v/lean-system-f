import SystemF.Typing
import SystemF.Eval

/-!
# 定理1（進行）

PDF: `Γ ⊢ e : σ` ならば、`e` は値であるか、ある `e'` について `e ⟶ e'`。

## PDF との違い

`SystemF.Eval` で述べたとおり、変数を値に含めるとこの定理は成り立たない。
そのため、値は λ と Λ だけとし、定理は **項変数の環境が空** の場合について示す。
型変数の環境 Δ は空でなくてもよい（型変数は評価に影響しないため）。

## 証明の流れ

PDF と同じく型付けの導出に関する帰納法で示す。
関数適用・型適用で「左側が値」の場合、PDF は「型が ∀α::κ.σ'' である値は TTAbs でしか導出されない」
と論じている。これを **標準形補題**（`canonical_arr`, `canonical_all`）として独立させた。
-/

namespace SystemF

variable {Δ : List Kind} {Γ : List Ty} {e : Tm} {σ σ₁ σ₂ : Ty} {κ : Kind}

/-- **標準形補題（関数型）**: 関数型を持つ値は λ 抽象である。 -/
theorem canonical_arr (hv : Value e) (h : Δ ; Γ ⊢ e : .arr σ₁ σ₂) :
    ∃ τ b, e = .lam τ b := by
  cases hv with
  | lam => exact ⟨_, _, rfl⟩
  | tlam => cases h  -- Λ 抽象の型は ∀ 型なので、関数型にはならない

/-- **標準形補題（全称型）**: 全称型を持つ値は Λ 抽象である。 -/
theorem canonical_all (hv : Value e) (h : Δ ; Γ ⊢ e : .all κ σ) :
    ∃ κ' b, e = .tlam κ' b := by
  cases hv with
  | lam => cases h  -- λ 抽象の型は関数型なので、∀ 型にはならない
  | tlam => exact ⟨_, _, rfl⟩

/-- 進行定理の本体。帰納法の途中で環境が変わるので、「Γ が空ならば」を仮定として持たせる。 -/
theorem progress_aux (h : Δ ; Γ ⊢ e : σ) : Γ = [] → Value e ∨ ∃ e', e ⟶ e' := by
  induction h with
  | TVar hi =>
    -- 空の環境には変数がないので、この場合は起こらない
    intro hΓ
    subst hΓ
    simp at hi
  | TAbs _ =>
    -- λ 抽象は値
    intro _
    exact .inl .lam
  | TApp h₁ _ ih₁ ih₂ =>
    -- 帰納法の仮定より、e₁ と e₂ はそれぞれ値か評価できる
    intro hΓ
    rcases ih₁ hΓ with hv₁ | ⟨e₁', hs₁⟩
    · rcases ih₂ hΓ with hv₂ | ⟨e₂', hs₂⟩
      · -- e₁, e₂ がともに値: 標準形補題より e₁ = λx:τ.b なので EAppAbs で評価できる
        obtain ⟨τ, b, rfl⟩ := canonical_arr hv₁ h₁
        exact .inr ⟨_, .EAppAbs hv₂⟩
      · -- e₂ ⟶ e₂' : EApp2 で評価できる
        exact .inr ⟨_, .EApp2 hs₂⟩
    · -- e₁ ⟶ e₁' : EApp1 で評価できる
      exact .inr ⟨_, .EApp1 hs₁⟩
  | TTAbs _ =>
    -- Λ 抽象は値
    intro _
    exact .inl .tlam
  | TTApp h₁ _ ih =>
    -- 帰納法の仮定より、e₁ は値か評価できる
    intro hΓ
    rcases ih hΓ with hv | ⟨e₁', hs⟩
    · -- e₁ が値: 標準形補題より e₁ = Λα::κ.b なので ETAppAbs で評価できる
      obtain ⟨κ', b, rfl⟩ := canonical_all hv h₁
      exact .inr ⟨_, .ETAppAbs⟩
    · -- e₁ ⟶ e₁' : ETApp で評価できる
      exact .inr ⟨_, .ETApp hs⟩

/-- **定理1（進行）**: 項変数を含まない型の付いた項は、値であるか、1 ステップ評価できる。 -/
theorem progress (h : Δ ; [] ⊢ e : σ) : Value e ∨ ∃ e', e ⟶ e' :=
  progress_aux h rfl

end SystemF
