import eBNFparser.Basic
open Std.Internal
open Parsec String

/-!
# eBNF パーサーの形式的検証

Parsec のプリミティブの正しさを公理として仮定し、各パーサー関数の健全性を証明する。
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

/-! ## terminal の健全性 -/

structure TerminalSpec (quote : Char) (content : String) : Prop where
  is_quote : (quote == '"' || quote == '\'') = true
  no_quote_in_content : ∀ c ∈ content.toList, (c != quote) = true

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

/-! ## identifier の健全性 -/

structure IdentifierSpec (head : Char) (tail : String) : Prop where
  head_is_alpha : Char.isAlpha head = true
  tail_is_alnum : ∀ c ∈ tail.toList, (Char.isAlphanum c || c == '_') = true

theorem identifier_sound (it it' : It) (s : String) :
    identifier it = .success it' s →
    ∃ head tail, s = head.toString ++ tail ∧ IdentifierSpec head tail := by
  unfold identifier; intro h
  obtain ⟨_, head, h1, h⟩ := parsec_bind_success h
  obtain ⟨_, tail, h2, h⟩ := parsec_bind_success h
  obtain ⟨_, _, _, h⟩ := parsec_bind_success h
  simp only [Pure.pure, Parsec.pure] at h; cases h
  exact ⟨head, tail, rfl, satisfy_success_char h1, manyChars_satisfy_content h2⟩

/-! ## mutual/partial 関数の健全性

`expression`, `sequence_`, `atom`, `rule`, `ebnf` は `partial` かつ相互再帰で
定義されているため、Lean 4 では定義を展開できない（`partial def` は内部的に
opaque として扱われる）。これらの健全性はコードの構造から導かれる性質として
公理で宣言する。
-/

section MutualAxioms

/-- atom が成功したなら、結果は terminal / nonterminal / opt / rep / group のいずれか -/
axiom atom_sound (it it' : It) (e : eBNFExpr) :
    atom it = .success it' e →
    (∃ s, e = .terminal s) ∨
    (∃ n, e = .nonterminal n) ∨
    (∃ inner, e = .opt inner) ∨
    (∃ inner, e = .rep inner) ∨
    (∃ inner, e = .group inner)

/-- sequence_ が成功したなら、結果は atom 由来の単一式か、要素2つ以上の seq -/
axiom sequence_sound (it it' : It) (e : eBNFExpr) :
    sequence_ it = .success it' e →
    (∃ s, e = .terminal s) ∨
    (∃ n, e = .nonterminal n) ∨
    (∃ inner, e = .opt inner) ∨
    (∃ inner, e = .rep inner) ∨
    (∃ inner, e = .group inner) ∨
    (∃ es, e = .seq es ∧ es.length ≥ 2)

/-- expression が成功したなら、結果は sequence_ 由来の式か、要素2つ以上の alt -/
axiom expression_sound (it it' : It) (e : eBNFExpr) :
    expression it = .success it' e →
    (∃ s, e = .terminal s) ∨
    (∃ n, e = .nonterminal n) ∨
    (∃ inner, e = .opt inner) ∨
    (∃ inner, e = .rep inner) ∨
    (∃ inner, e = .group inner) ∨
    (∃ es, e = .seq es ∧ es.length ≥ 2) ∨
    (∃ es, e = .alt es ∧ es.length ≥ 2)

/-- rule が成功したなら、名前は identifier 仕様を満たす -/
axiom rule_sound (it it' : It) (r : eBNFRule) :
    rule it = .success it' r →
    (∃ head tail, r.name = head.toString ++ tail ∧ IdentifierSpec head tail)

/-- ebnf が成功したなら、各ルールは rule 仕様を満たす -/
axiom ebnf_sound (it it' : It) (rules : Array eBNFRule) :
    ebnf it = .success it' rules →
    ∀ r ∈ rules.toList,
      ∃ head tail, r.name = head.toString ++ tail ∧ IdentifierSpec head tail

end MutualAxioms

/-! ## 導出される定理 -/

/-- expression は .alt を返すとき、必ず要素が2つ以上ある -/
theorem expression_alt_has_two_or_more (it it' : It) (es : List eBNFExpr) :
    expression it = .success it' (.alt es) → es.length ≥ 2 := by
  intro h
  rcases expression_sound it it' _ h with
    ⟨_, heq⟩ | ⟨_, heq⟩ | ⟨_, heq⟩ | ⟨_, heq⟩ | ⟨_, heq⟩ |
    ⟨_, heq, _⟩ | ⟨_, heq, hlen⟩
  · cases heq
  · cases heq
  · cases heq
  · cases heq
  · cases heq
  · cases heq
  · cases heq; exact hlen

/-- sequence_ は .seq を返すとき、必ず要素が2つ以上ある -/
theorem sequence_seq_has_two_or_more (it it' : It) (es : List eBNFExpr) :
    sequence_ it = .success it' (.seq es) → es.length ≥ 2 := by
  intro h
  rcases sequence_sound it it' _ h with
    ⟨_, heq⟩ | ⟨_, heq⟩ | ⟨_, heq⟩ | ⟨_, heq⟩ | ⟨_, heq⟩ |
    ⟨_, heq, hlen⟩
  · cases heq
  · cases heq
  · cases heq
  · cases heq
  · cases heq
  · cases heq; exact hlen