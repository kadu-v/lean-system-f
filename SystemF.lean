import SystemF.Syntax
import SystemF.Renaming
import SystemF.Ty.Subst
import SystemF.Tm.Subst
import SystemF.Eval
import SystemF.Kinding
import SystemF.Typing
import SystemF.Weakening
import SystemF.Substitution
import SystemF.Progress
import SystemF.Preservation

/-!
# System F の型安全性

`2023_systemF.pdf`（Proof of System F）の内容を Lean 4 で形式化したもの。
下のモジュールを上から順に読むと、定義 → 補題 → 定理 の順に追える。

| モジュール                  | PDF との対応                              |
|-----------------------------|-------------------------------------------|
| `SystemF.Syntax`            | Figure 1（構文）                          |
| `SystemF.Renaming`          | （de Bruijn 用の補助: 変数の付け替え）    |
| `SystemF.Ty.Subst`          | 型の代入、補題5.1（型代入の交換）         |
| `SystemF.Tm.Subst`          | 項の代入                                  |
| `SystemF.Eval`              | Figure 2（評価規則）                      |
| `SystemF.Kinding`           | Figure 3（カインド規則）、補題2.1         |
| `SystemF.Typing`            | Figure 4（型規則）、補題4（逆転補題）     |
| `SystemF.Weakening`         | 補題3（弱化補題）                         |
| `SystemF.Substitution`      | 補題1（項代入補題）、補題2.2（型代入補題）|
| `SystemF.Progress`          | 定理1（進行）                             |
| `SystemF.Preservation`      | 定理2（保存）                             |

## PDF からの主な変更点

1. **変数は de Bruijn index で表す。**
   名前付き変数のままだと、代入で変数が捕獲されないよう名前を付け替える処理と、
   「名前だけが違う項は同じ」（α 同値）という扱いの両方を形式化しなければならない。
   de Bruijn index ではこの問題自体が起きない（詳しくは `SystemF.Syntax`）。
2. **環境を「型変数の環境 Δ」と「項変数の環境 Γ」の 2 つに分ける。**
   PDF の `Γ ⊢ e : σ` は `Δ ; Γ ⊢ e : σ` になる。
3. **代入は「すべての変数を一度に置き換える関数」（並列代入）として定義する。**
   PDF の `[α ↦ σ]` はその特殊な場合になる（詳しくは `SystemF.Ty.Subst`）。
4. **進行定理は項変数の環境が空（Γ = []）の項に対して示し、値から変数を除く。**
   型変数の環境 Δ は空でなくてよい（`progress : Δ ; [] ⊢ e : σ → …`）。
   PDF の定義（変数も値）のままでは、`x y`（x : A → B）が「値でもなく評価もできない」
   反例になり、定理が成り立たない（詳しくは `SystemF.Progress`）。
-/
