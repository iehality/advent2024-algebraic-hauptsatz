#import "template.typ": *
#import "@preview/curryst:0.3.0": rule, proof-tree
#show: thmrules

#show: project.with(
  title: [強制法を用いてカットを除去する],
  authors: (
    "palalansoukî",
  ),
)

これは #link("https://adventar.org/calendars/10209")[証明支援言語 Advent Calender 2024] の９日の記事です．
第2章の内容は主に #link("https://github.com/FormalizedFormalLogic/Foundation/blob/master/Foundation/IntFO/Translation.lean")[`Foundation/IntFO/Translation.lean`]に，
第3章の内容は主に #link("https://github.com/FormalizedFormalLogic/Foundation/blob/master/Foundation/FirstOrder/Hauptsatz.lean")[`Foundation/FirstOrder/Hauptsatz.lean`]
にあります． 証明の多くは省略し，その概要のみ説明しています．

#outline(indent: auto,)

= 序文
古典一階述語論理を始め，多くの論理ではカット規則
#align(center)[#proof-tree(
  rule(
    name: $script("CUT")$,
    $ Gamma $,
    $ phi, Gamma $,
    $ not phi, Gamma $,
  )
)]
の除去定理（cut elimination theorem）が成立する．
普通は証明図に関する直接の帰納法によってカットが除去された証明図を生成することで示されるが，
多くの場合証明（特に形式化されたもの）は煩雑になり，また証明体系に強く依存する．

一方で， 古典一階述語論理においては健全性定理と証明探索による完全性定理を用いればカット除去定理はほとんど自明に成り立つ．
すなわち, $proves Gamma$ と仮定すれば健全性より $models or.big Gamma$ であり， よって完全性より再び $Gamma$ が証明できる．
このとき証明探索において木を逆向きに伸ばしていく際，使用される規則にカットは含まれないため， $Gamma$ の証明からカットは除去されている．
この意味論的証明は簡単で強力に見えるが，惜しむべくはこの証明は構成的ではないことで，カット除去のアルゴリズムが得られない．

ここでは @avigad2001algebraic に則って，ある意味でこれらの中間の特徴を持つカット除去定理の証明を Lean4で 形式化する．
これは強制法 #footnote[キャッチーさのためにこれを強制法と呼ぶが， 集合論者の使用するそれとは異なるし， どの程度一般的な呼称かは分からない．]
を用いて意味論的証明から構成的部分を「抽出」することで行われる．

この証明は #link("https://github.com/FormalizedFormalLogic")[FFL] の一部であり，記法と流儀には以下のものを採用していることを注記しておく．

- 論理記号は次の記法で書く．
  #align(center)[
    #text(6pt)[
    #table(
      columns: 8,
      align: center + horizon,
      stroke: (x, y) => if y == 0 {
        (bottom: black)
      },
      inset: 8pt,
      table.header(
        [真 $top$],
        [偽 $bot$],
        [否定 $not phi$],
        [含意 $phi -> psi$],
        [連言 $ phi and psi$, $and.big Gamma$],
        [選言 $ phi or psi$, $or.big Gamma$],
        [全称量化 $(forall x) phi$],
        [存在量化 $(exists x) phi$],
      ),
      [`⊤`],
      [`⊥`],
      [`∼φ`],
      [`φ ➝ ψ`],
      [`φ ⋏ ψ`, `∧Γ`],
      [`φ ⋎ ψ`, `⋁Γ`],
      [`∀' φ`],
      [`∃' φ`],
    )
    ]
  ]
- 古典一階述語論理の論理式は常に否定標準形を取るようにする．
  - `Semiformula L ξ n` は型 `ξ : Type*` の自由変数, `n : ℕ` 未満の束縛変数を持つ言語 `L : Language` の古典一階述語論理の擬論理式 semiformula
    (cf. @buss1998introduction)．
  - `SyntacticFormula L` は `ℕ` の自由変数のみを持つ言語 `L` の論理式． `Semiformula L ℕ 0` の略記．

- 古典一階述語論理の証明体系にはTait計算を採用する． 言語 `L` の推件 `Γ : Sequent L` のTait計算による公理なし証明の型は `⊢ᵀ Γ` と表記する．

= 直観主義一階述語論理

言語を `L` として，直観主義一階述語論理の(擬)論理式を (`Semiformulaᵢ L ξ n`) `SyntacticFormulaᵢ L` と呼ぶ．
Hilbert流の直観主義一階述語論理の証明体系 `HilbertProofᵢ Λ φ` を次のように定める．

```
inductive HilbertProofᵢ (Λ : Hilbertᵢ L) : SyntacticFormulaᵢ L → Type _
  | eaxm {φ}     : φ ∈ Λ → HilbertProofᵢ Λ φ
  | mdp {φ ψ}    : HilbertProofᵢ Λ (φ ➝ ψ) → HilbertProofᵢ Λ φ → HilbertProofᵢ Λ ψ
  | gen {φ}      : HilbertProofᵢ Λ (Rewriting.free φ) → HilbertProofᵢ Λ (∀' φ)
  | verum        : HilbertProofᵢ Λ ⊤
  | imply₁ φ ψ   : HilbertProofᵢ Λ <| φ ➝ ψ ➝ φ
  | imply₂ φ ψ χ : HilbertProofᵢ Λ <| (φ ➝ ψ ➝ χ) ➝ (φ ➝ ψ) ➝ φ ➝ χ
  | and₁ φ ψ     : HilbertProofᵢ Λ <| φ ⋏ ψ ➝ φ
  | and₂ φ ψ     : HilbertProofᵢ Λ <| φ ⋏ ψ ➝ ψ
  | and₃ φ ψ     : HilbertProofᵢ Λ <| φ ➝ ψ ➝ φ ⋏ ψ
  | or₁ φ ψ      : HilbertProofᵢ Λ <| φ ➝ φ ⋎ ψ
  | or₂ φ ψ      : HilbertProofᵢ Λ <| ψ ➝ φ ⋎ ψ
  | or₃ φ ψ χ    : HilbertProofᵢ Λ <| (φ ➝ χ) ➝ (ψ ➝ χ) ➝ (φ ⋎ ψ ➝ χ)
  | all₁ φ t     : HilbertProofᵢ Λ <| ∀' φ ➝ φ/[t]
  | all₂ φ ψ     : HilbertProofᵢ Λ <| ∀' (φ/[] ➝ ψ) ➝ φ ➝ ∀' ψ
  | ex₁ t φ      : HilbertProofᵢ Λ <| φ/[t] ➝ ∃' φ
  | ex₂ φ ψ      : HilbertProofᵢ Λ <| ∀' (φ ➝ ψ/[]) ➝ ∃' φ ➝ ψ
```

ここで `Λ : Hilbertᵢ L` は最小論理 `𝐌𝐢𝐧¹`, 直観主義論理 `𝐈𝐧𝐭¹` といった論理的公理のクラスを表す．
以降 `HilbertProofᵢ Λ φ` は `Λ ⊢ φ` と表記する．

一般には最小論理では爆発律や二重否定除去は成立しないが， negative formula に限ると成立する． 
すなわち， 任意の `Λ` に関して次が証明される．

#lemma[
  `IsNegative` な論理式 `φ` に対して爆発律と二重否定除去の証明が構成できる．
  ```
  def dneOfNegative : {φ : SyntacticFormulaᵢ L} → φ.IsNegative → Λ ⊢ ∼∼φ ➝ φ
  ```
  
  ```
  def efqOfNegative : {φ : SyntacticFormulaᵢ L} → φ.IsNegative → Λ ⊢ ⊥ ➝ φ
  ```
]<efq-and-dne>
#proof[
  `φ` に関する帰納法．
]

ここで negative formula `IsNegative φ` は次のように定義される論理式のクラスである
#footnote[ここでは一般に negative formula と呼ばれているものより少し一般化した定義をしている．]．

```
inductive IsNegative : Semiformulaᵢ L ξ n → Prop
  | falsum      : IsNegative ⊥
  | and {φ ψ}   : IsNegative φ → IsNegative ψ → IsNegative (φ ⋏ ψ)
  | imply {φ ψ} : IsNegative ψ → IsNegative (φ ➝ ψ)
  | all {φ}     : IsNegative φ → IsNegative (∀' φ)
```

== Gödel-Gentzen翻訳

二重否定翻訳と呼ばれる翻訳によって古典論理の証明は直観主義論理の証明に移されることが知られている．

#definition[
  翻訳 `•ᴺ` を以下のように定義する．
  ```
  def doubleNegation {n} : Semiformula L ξ n → Semiformulaᵢ L ξ n
    | rel r v  => ∼∼(.rel r v)
    | nrel r v => ∼(.rel r v)
    | ⊤        => ∼⊥
    | ⊥        => ⊥
    | φ ⋏ ψ    => φ.doubleNegation ⋏ ψ.doubleNegation
    | φ ⋎ ψ    => ∼(∼φ.doubleNegation ⋏ ∼ψ.doubleNegation)
    | ∀' φ     => ∀' φ.doubleNegation
    | ∃' φ     => ∼(∀' ∼φ.doubleNegation)
  
  scoped[LO.FirstOrder] postfix:max "ᴺ" => Semiformula.doubleNegation
  ```
]

注意すべきなのは翻訳の像が negative であることである．
よって @efq-and-dne より次の関数が `⊢ᵀ Γ` に関する帰納法によって構成できる．

#theorem[
  ```
  def goedelGentzen {Γ : Sequent L} : ⊢ᵀ Γ → 𝐌𝐢𝐧¹ ⊢ ∧(∼Γ)ᴺ ➝ ⊥
  ```
]<gg-translation>

= 強制

== 強制擬順序 `ℙ`, `≼`

`ℙ` を古典一階述語論理の推件の集合とする．

```
local notation "ℙ" => Sequent L
```

`ℙ` 上の順序関係 `≼` を定義したい． ただし，ここでは構成的に証明を生成したいため，順序は`ℙ → ℙ → Prop`ではなく`ℙ → ℙ → Type _`として定義する．

```
structure StrongerThan (q p : ℙ) where
  val : ∼p ⟶⁺ ∼q

scoped infix:60 " ≼ " => StrongerThan
```

ここで `Ξ ⟶⁺ Γ` は 「`Ξ` を葉とする $top$-導入, $or$-導入, $exists$-導入, 弱化規則のみによる `Γ` の証明」の型である．

#definition[
  ```
  inductive PositiveDerivationFrom (Ξ : Sequent L) : Sequent L → Type _
  | verum (Γ)    : PositiveDerivationFrom Ξ (⊤ :: Γ)
  | or {Γ φ ψ}   : PositiveDerivationFrom Ξ (φ :: ψ :: Γ) → PositiveDerivationFrom Ξ (φ ⋎ ψ :: Γ)
  | ex {Γ φ} (t) : PositiveDerivationFrom Ξ (φ/[t] :: Γ) → PositiveDerivationFrom Ξ ((∃' φ) :: Γ)
  | wk {Γ Δ}     : PositiveDerivationFrom Ξ Δ → Δ ⊆ Γ → PositiveDerivationFrom Ξ Γ
  | protected id : PositiveDerivationFrom Ξ Ξ
  
  infix:45 " ⟶⁺ " => PositiveDerivationFrom
  ```
]

次が証明できる．

#lemma[
  1. `≼` は擬順序である：反射的かつ推移的.
    ```
    protected def refl (p : ℙ) : p ≼ p

    def trans {r q p : ℙ} (srq : r ≼ q) (sqp : q ≼ p) : r ≼ p
    ```
  2.
    ```
    def andLeft {p : ℙ} (φ ψ : SyntacticFormula L) : φ ⋏ ψ :: p ≼ φ :: p

    def andRight {p : ℙ} (φ ψ : SyntacticFormula L) : φ ⋏ ψ :: p ≼ ψ :: p

    def all {p : ℙ} (φ : SyntacticSemiformula L 1) (t) : (∀' φ) :: p ≼ φ/[t] :: p

    def ofSubset {q p : ℙ} (h : q ⊇ p) : q ≼ p
    ``` 
]<rel-basic>

順序関係の最大下限 `p ⊓ q` を推件の連結として定める．

```
scoped instance : Min ℙ := ⟨fun p q ↦ p ++ q⟩

lemma inf_def (p q : ℙ) : p ⊓ q = p ++ q := rfl
```

#lemma[
  ```
  def minLeLeft (p q : ℙ) : p ⊓ q ≼ p

  def minLeRight (p q : ℙ) : p ⊓ q ≼ q
  
  def leMinOfle (srp : r ≼ p) (srq : r ≼ q) : r ≼ p ⊓ q
  ```
]<inf-lemmata>

== 強制関係

#definition[
  `p : ℙ`, 直観主義一階述語論理の論理式 `φ : SyntacticFormulaᵢ L` に対して強制関係 `p ⊩ φ`, `⊩ φ` を次のように定める
  #footnote[
    この強制関係の定義は集合論などでよく見るものと異なっている（例えば `p ⊩ φ ⋎ ψ` の定義）が， 
    そもそも（古典論理の）強制とは二重否定翻訳によって Kripkeフレーム `ℙ` 上の直観主義論理の意味論で解釈したものであり，
    これはオリジナルの直観主義論理の強制と見ることができる (cf. @avigad2004forcing)．
  ]．

  ```
  abbrev Forces (p : ℙ) : SyntacticFormulaᵢ L → Type u
  | ⊤        => PUnit.{u+1}
  | ⊥        => { b : ⊢ᵀ ∼p // Derivation.IsCutFree b }
  | .rel R v => { b : ⊢ᵀ .rel R v :: ∼p // Derivation.IsCutFree b }
  | φ ⋏ ψ    => Forces p φ × Forces p ψ
  | φ ⋎ ψ    => Forces p φ ⊕ Forces p ψ
  | φ ➝ ψ    => (q : ℙ) → q ≼ p → Forces q φ → Forces q ψ
  | ∀' φ     => (t : SyntacticTerm L) → Forces p (φ/[t])
  | ∃' φ     => (t : SyntacticTerm L) × Forces p (φ/[t])
  termination_by φ => φ.complexity

  scoped infix:45 " ⊩ " => Forces

  abbrev allForces (φ : SyntacticFormulaᵢ L) := (p : ℙ) → p ⊩ φ
  
  scoped prefix:45 "⊩ " => allForces
  ```
]

`p ⊩ ⊥` は `∼p` のカットなし証明， `p ⊩ .rel R v` は `.rel R v :: ∼p` のカットなし証明を意味する．
特に `p ⊩ φ ➝ ψ` は一般的な強制関係の（または直観主義論理のKripke意味論の）定義

$ p forces phi -> psi := (forall q prec.eq p)[q forces phi -> q forces psi] $

の構成的バージョンであることが確認できる．

#lemma[
  1. 強制関係は単調
    ```
    def monotone {q p : ℙ} (s : q ≼ p) : {φ : SyntacticFormulaᵢ L} → p ⊩ φ → q ⊩ φ
    ```
  2. 爆発律
    ```
    def efq (φ : SyntacticFormulaᵢ L) : ⊩ ⊥ ➝ φ
    ```
  3. `p ⊩ φ ➝ ψ` は `(q : ℙ) → q ⊩ φ → p ⊓ q ⊩ ψ` と等価（以下では一方向しか示していないが）．
    ```
    def implyOf {φ ψ : SyntacticFormulaᵢ L} (b : (q : ℙ) → q ⊩ φ → p ⊓ q ⊩ ψ) : p ⊩ φ ➝ ψ
    ```
]<forces-basic>
#proof[
  1., 2. はいずれも`φ`に関する帰納法による． 3. は1. と @inf-lemmata の3.から従う `q ≼ p → q ≼ p ⊓ q` を用いる．
]


== カット除去

カット除去定理の証明をしていく．重要なのは以下の２つの補題である．

#lemma[
  最小論理 #footnote[@forces-basic の 2. が成り立つので実際には直観主義論理でも良い．] で `φ` が証明可能ならば強制される．
  ```
  def ofMinimalProof {φ : SyntacticFormulaᵢ L} : 𝐌𝐢𝐧¹ ⊢ φ → ⊩ φ
  ```
]<of-minimal>
#proof[
  `𝐌𝐢𝐧¹ ⊢ φ` に関する帰納法．
  modus ponens と generalization が成立することは直ちにわかるので， 各論理的公理が強制されることを確かめれば良い．
]

#lemma[
  ```
  protected def refl : (φ : SyntacticFormula L) → [φ] ⊩ φᴺ
  ```
]<refl>
#proof[
  `φ` に関して再帰的に定義する． `φ ⋏ ψ` と `φ ⋎ ψ` の場合のみ示す．
  - `φ ⋏ ψ` のとき： `[φ ⋏ ψ] ⊩ φᴺ` と `[φ ⋏ ψ] ⊩ ψᴺ` を構成すれば良い．
    `[φ] ⊩ φᴺ` と `[ψ] ⊩ ψᴺ` はすでに得ているので，単調性より `[φ ⋏ ψ] ≼ [φ]`, `[φ ⋏ ψ] ≼ [ψ]` を得られれば良い．
    これは @rel-basic の `andLeft`, `andRight` より従う．
  - `φ ⋎ ψ` のとき： `[φ ⋎ ψ] ⊩ ∼(∼φᴺ ⋏ ∼ψᴺ)` を構成すれば良い． @forces-basic の 3. より `(q : ℙ) → q ⊩ ∼φᴺ → q ⊩ ∼ψᴺ → [φ ⋎ ψ] ⊓ q ⊩ ⊥`
    を構成する． `q`, `q ⊩ ∼φᴺ`, `q ⊩ ∼ψᴺ` を固定する． `[φ] ⊩ φᴺ` と `[ψ] ⊩ ψᴺ` はすでに得ているので，
    単調性より `[φ] ⊓ q ⊩ ⊥`, `[ψ] ⊓ q ⊩ ⊥` を得る． よって $and$-導入規則から `∼φ ⋏ ∼ψ :: ∼q` のカットなし証明を得る．
    
]

最後に主定理を証明する．

#theorem([カット除去定理])[
  ```
  def main : ⊢ᵀ Γ → {d : ⊢ᵀ Γ // Derivation.IsCutFree d}
  ```
]
#proof[
  `d : ⊢ᵀ Γ` を固定する． @gg-translation より `d' : 𝐌𝐢𝐧¹ ⊢ ⋀(∼Γ)ᴺ ➝ ⊥` を得る．
  @of-minimal より `ff : ∼Γ ⊩ ⋀(∼Γ)ᴺ ➝ ⊥`, @refl より `fc : ∼Γ ⊩ ⋀(∼Γ)ᴺ` が従う．
  よって強制関係の modus ponens より `b : ∼Γ ⊩ ⊥`.
  これは `∼∼Γ` $=$ `Γ` のカット無しの証明である．
]

=== `noncomputable`について
  
上の議論は全て構成的に行えるはずだが， bytecode の生成が遅すぎるため？に`noncomputable`を付けざるを得なくなっている#footnote[だめじゃん．]．
一般にカット除去アルゴリズムは効率が悪く(feasible でなく)，証明が非常に長くなるため，これを取り除くのは本質的に困難かもしれないが，改善できそうなら試したい．

#set text(lang: "en")

#bibliography("main.bib")
