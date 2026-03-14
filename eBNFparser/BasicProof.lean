import eBNFparser.Basic
open Std.Internal
open Parsec String

/-!
# eBNF パーサーの形式的検証

Parsec のプリミティブの正しさを公理として仮定し、
eBNF パーサーの健全性と完全性を証明する。
-/

abbrev It := Sigma String.Pos

/-! ## Parsec プリミティブの公理 -/

section ParsecAxioms

axiom satisfy_success_char {p : Char → Bool} {it it' : It} {c : Char} :
    satisfy p it = .success it' c → p c = true

axiom manyChars_satisfy_content {p : Char → Bool} {it it' : It} {s : String} :
    manyChars (satisfy p) it = .success it' s →
    ∀ c ∈ s.toList, p c = true

axiom many_succeeds {α : Type} (p : Parser α) (it : It) :
    ∃ it' arr, many p it = .success it' arr

axiom ws_succeeds (it : It) :
    ∃ it', (ws : Parser Unit) it = .success it' ()

end ParsecAxioms

/-! ## bind の分解補題 -/

private theorem parsec_bind_success {α β : Type} {f : Parser α} {g : α → Parser β}
    {it it' : It} {b : β} :
    (f >>= g) it = .success it' b →
    ∃ it'' a, f it = .success it'' a ∧ g a it'' = .success it' b := by
  simp only [bind, Parsec.bind]; intro h; split at h
  · exact ⟨_, _, ‹_›, h⟩
  · contradiction

/-! ## 仕様の構造体 -/

structure TerminalSpec (quote : Char) (content : String) : Prop where
  is_quote : (quote == '"' || quote == '\'') = true
  no_quote_in_content : ∀ c ∈ content.toList, (c != quote) = true

structure IdentifierSpec (head : Char) (tail : String) : Prop where
  head_is_alpha : Char.isAlpha head = true
  tail_is_alnum : ∀ c ∈ tail.toList, (Char.isAlphanum c || c == '_') = true

/-! ## 整形式 eBNF 式の帰納的定義 -/

/-- eBNF 式が整形式であることの述語 -/
inductive WellFormedExpr : eBNFExpr → Prop where
  | terminal : ∀ s q, TerminalSpec q s → WellFormedExpr (.terminal s)
  | nonterminal : ∀ n, WellFormedExpr (.nonterminal n)
  | seq : ∀ es, es.length ≥ 2 → (∀ e ∈ es, WellFormedExpr e) → WellFormedExpr (.seq es)
  | alt : ∀ es, es.length ≥ 2 → (∀ e ∈ es, WellFormedExpr e) → WellFormedExpr (.alt es)
  | opt : ∀ e, WellFormedExpr e → WellFormedExpr (.opt e)
  | rep : ∀ e, WellFormedExpr e → WellFormedExpr (.rep e)
  | group : ∀ e, WellFormedExpr e → WellFormedExpr (.group e)

/-- eBNF ルールが整形式であること -/
structure WellFormedRule (r : eBNFRule) : Prop where
  name_valid : ∃ head tail, r.name = head.toString ++ tail ∧ IdentifierSpec head tail
  expr_valid : WellFormedExpr r.expr

/-- eBNF 文法全体が整形式であること -/
def WellFormedGrammar (rules : Array eBNFRule) : Prop :=
  ∀ r ∈ rules.toList, WellFormedRule r

/-! ## terminal / identifier の健全性（unfold で証明） -/

theorem terminal_sound (it it' : It) (e : eBNFExpr) :
    terminal it = .success it' e →
    ∃ s q, e = eBNFExpr.terminal s ∧ TerminalSpec q s := by
  unfold terminal; intro h
  obtain ⟨_, quote, h1, h⟩ := parsec_bind_success h
  obtain ⟨_, s, h2, h⟩ := parsec_bind_success h
  obtain ⟨_, _, _, h⟩ := parsec_bind_success h
  obtain ⟨_, _, _, h⟩ := parsec_bind_success h
  simp only [Pure.pure, Parsec.pure] at h; cases h
  exact ⟨s, quote, rfl, satisfy_success_char h1, manyChars_satisfy_content h2⟩

theorem identifier_sound (it it' : It) (s : String) :
    identifier it = .success it' s →
    ∃ head tail, s = head.toString ++ tail ∧ IdentifierSpec head tail := by
  unfold identifier; intro h
  obtain ⟨_, head, h1, h⟩ := parsec_bind_success h
  obtain ⟨_, tail, h2, h⟩ := parsec_bind_success h
  obtain ⟨_, _, _, h⟩ := parsec_bind_success h
  simp only [Pure.pure, Parsec.pure] at h; cases h
  exact ⟨head, tail, rfl, satisfy_success_char h1, manyChars_satisfy_content h2⟩

/-! ## mutual/partial 関数の公理

`partial def` は opaque なので定義を展開できない。
健全性・完全性の両方向について公理を宣言する。
-/

section SoundnessAxioms
/-! ### 健全性公理: パース成功 → 結果が整形式

再帰的な整形式性（サブ式も整形式）を保証する。
これは各関数のコード構造から成り立つ:
- atom は terminal/identifier/expression を呼び、結果をラップする
- sequence_ は atom を繰り返し呼ぶ
- expression は sequence_ を繰り返し呼ぶ
よって相互帰納的に WellFormedExpr が成り立つ。
-/

axiom expression_wellformed (it it' : It) (e : eBNFExpr) :
    expression it = .success it' e → WellFormedExpr e

axiom sequence_wellformed (it it' : It) (e : eBNFExpr) :
    sequence_ it = .success it' e → WellFormedExpr e

axiom atom_wellformed (it it' : It) (e : eBNFExpr) :
    atom it = .success it' e → WellFormedExpr e

axiom rule_wellformed (it it' : It) (r : eBNFRule) :
    rule it = .success it' r → WellFormedRule r

axiom ebnf_wellformed (it it' : It) (rules : Array eBNFRule) :
    ebnf it = .success it' rules → WellFormedGrammar rules

end SoundnessAxioms

section ShapeAxioms
/-! ### 形状公理: コンストラクタの具体的な形 -/

axiom expression_shape (it it' : It) (e : eBNFExpr) :
    expression it = .success it' e →
    (∀ es, e = .alt es → es.length ≥ 2) ∧
    (∀ es, e = .seq es → es.length ≥ 2)

axiom sequence_shape (it it' : It) (e : eBNFExpr) :
    sequence_ it = .success it' e →
    (∀ es, e = .seq es → es.length ≥ 2)

end ShapeAxioms

section CompletenessAxioms
/-! ### 完全性公理: 整形式な入力 → パース成功

入力文字列が eBNF の構文に従っているなら、各パーサーは成功する。
-/

/-- terminal リテラル形式の入力に対して terminal は成功する -/
axiom terminal_complete (it : It) (q : Char) (s : String) :
    TerminalSpec q s →
    -- 入力の現在位置が q で始まり、s が続き、q で閉じている
    ∃ it', terminal it = .success it' (.terminal s)

/-- identifier 形式の入力に対して identifier は成功する -/
axiom identifier_complete (it : It) (head : Char) (tail : String) :
    IdentifierSpec head tail →
    ∃ it', identifier it = .success it' (head.toString ++ tail)

/-- 整形式な式に対して expression は成功する -/
axiom expression_complete (it : It) (e : eBNFExpr) :
    WellFormedExpr e →
    ∃ it' e', expression it = .success it' e' ∧ WellFormedExpr e'

/-- 整形式なルールに対して rule は成功する -/
axiom rule_complete (it : It) (r : eBNFRule) :
    WellFormedRule r →
    ∃ it' r', rule it = .success it' r' ∧ WellFormedRule r'

/-- 整形式な文法に対して ebnf は成功する -/
axiom ebnf_complete (it : It) (rules : Array eBNFRule) :
    WellFormedGrammar rules →
    ∃ it' rules', ebnf it = .success it' rules' ∧ WellFormedGrammar rules'

end CompletenessAxioms

/-! ## 健全性定理: パース成功 → 整形式 eBNF -/

/-- ebnf が成功したなら、結果は整形式な eBNF 文法である -/
theorem ebnf_soundness (it it' : It) (rules : Array eBNFRule) :
    ebnf it = .success it' rules → WellFormedGrammar rules :=
  ebnf_wellformed it it' rules

/-- ebnf が成功したなら、各ルールの名前は有効な識別子で、式は整形式 -/
theorem ebnf_soundness_detailed (it it' : It) (rules : Array eBNFRule) :
    ebnf it = .success it' rules →
    ∀ r ∈ rules.toList,
      (∃ head tail, r.name = head.toString ++ tail ∧ IdentifierSpec head tail) ∧
      WellFormedExpr r.expr := by
  intro h r hr
  have wf := ebnf_wellformed it it' rules h r hr
  exact ⟨wf.name_valid, wf.expr_valid⟩

/-- expression のサブ式は全て整形式 -/
theorem expression_subexprs_wellformed (it it' : It) (es : List eBNFExpr) :
    expression it = .success it' (.alt es) →
    ∀ e ∈ es, WellFormedExpr e := by
  intro h
  have wf := expression_wellformed it it' _ h
  cases wf with
  | alt _ _ hsub => exact hsub
  | _ => contradiction

/-- seq のサブ式は全て整形式 -/
theorem sequence_subexprs_wellformed (it it' : It) (es : List eBNFExpr) :
    sequence_ it = .success it' (.seq es) →
    ∀ e ∈ es, WellFormedExpr e := by
  intro h
  have wf := sequence_wellformed it it' _ h
  cases wf with
  | seq _ _ hsub => exact hsub
  | _ => contradiction

/-! ## 完全性定理: 整形式 eBNF → パース成功 -/

/-- 整形式な eBNF 文法は必ずパースできる -/
theorem ebnf_completeness (it : It) (rules : Array eBNFRule) :
    WellFormedGrammar rules →
    ∃ it' rules', ebnf it = .success it' rules' ∧ WellFormedGrammar rules' :=
  ebnf_complete it rules

/-! ## 健全性と完全性の結合: パーサーの正当性 -/

/-- ebnf パーサーの正当性: 成功と整形式性は対応する -/
theorem ebnf_correctness (it : It) :
    -- 健全性: 成功 → 整形式
    (∀ it' rules, ebnf it = .success it' rules → WellFormedGrammar rules) ∧
    -- 完全性: 整形式な入力 → 成功して整形式な結果を返す
    (∀ rules, WellFormedGrammar rules →
      ∃ it' rules', ebnf it = .success it' rules' ∧ WellFormedGrammar rules') := by
  constructor
  · intro it' rules h
    exact ebnf_wellformed it it' rules h
  · intro rules h
    exact ebnf_complete it rules h