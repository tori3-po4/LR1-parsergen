import eBNFparser.Basic

/-! # LR(0) 項目集合の構築 -/

/-- 文法記号 -/
inductive Symbol where
  | terminal : String → Symbol
  | nonterminal : String → Symbol
  deriving BEq, Repr, Inhabited

instance : ToString Symbol where
  toString
    | .terminal s => s!"'{s}'"
    | .nonterminal s => s

/-- 生成規則 -/
structure Production where
  lhs : String
  rhs : List Symbol
  deriving BEq, Repr

instance : ToString Production where
  toString p :=
    let rhsStr := if p.rhs.isEmpty then "ε"
      else " ".intercalate (p.rhs.map toString)
    s!"{p.lhs} → {rhsStr}"

/-- 文法 -/
structure Grammar where
  productions : List Production
  startSymbol : String
  deriving Repr

/-- LR(0) 項目: [A → α · β] -/
structure LR0Item where
  prod : Production
  dot : Nat
  deriving BEq, Repr

instance : ToString LR0Item where
  toString item :=
    let before := item.prod.rhs.take item.dot |>.map toString
    let after := item.prod.rhs.drop item.dot |>.map toString
    let lhs := item.prod.lhs
    let rhs := " ".intercalate (before ++ ["·"] ++ after)
    s!"[{lhs} → {rhs}]"

/-- ドットの次の記号 -/
def LR0Item.nextSymbol (item : LR0Item) : Option Symbol :=
  item.prod.rhs[item.dot]?

/-- ドットを一つ進める -/
def LR0Item.advance (item : LR0Item) : LR0Item :=
  { item with dot := item.dot + 1 }

/-- 項目集合 -/
abbrev ItemSet := List LR0Item

/-! ## eBNF → BNF 変換 -/

/-- eBNFExpr を生成規則の右辺（代替のリスト）に変換する。
    ネストした opt / rep は新しい非終端記号と追加の生成規則を生成する。 -/
partial def exprToAlts (e : eBNFExpr) (nextId : Nat) :
    List (List Symbol) × List Production × Nat :=
  match e with
  | .terminal s => ([[.terminal s]], [], nextId)
  | .nonterminal n => ([[.nonterminal n]], [], nextId)
  | .group inner => exprToAlts inner nextId
  | .alt es =>
    es.foldl (fun (alts, prods, id) e =>
      let (newAlts, newProds, id) := exprToAlts e id
      (alts ++ newAlts, prods ++ newProds, id)
    ) ([], [], nextId)
  | .seq es =>
    es.foldl (fun (rhsList, prods, id) e =>
      let (alts, newProds, id) := exprToAlts e id
      match alts with
      | [single] => (rhsList.map (· ++ single), prods ++ newProds, id)
      | _ =>
        let name := s!"_alt{id}"
        let altProds := alts.map fun rhs => ({ lhs := name, rhs } : Production)
        (rhsList.map (· ++ [.nonterminal name]),
         prods ++ newProds ++ altProds, id + 1)
    ) (([[]], ([], nextId)) : List (List Symbol) × List Production × Nat)
  | .opt inner =>
    let name := s!"_opt{nextId}"
    let (alts, prods, id) := exprToAlts inner (nextId + 1)
    let altProds := alts.map fun rhs => ({ lhs := name, rhs } : Production)
    ([[.nonterminal name]],
     prods ++ altProds ++ [{ lhs := name, rhs := [] }], id)
  | .rep inner =>
    let name := s!"_rep{nextId}"
    let (alts, prods, id) := exprToAlts inner (nextId + 1)
    let altProds := alts.map fun rhs =>
      ({ lhs := name, rhs := .nonterminal name :: rhs } : Production)
    ([[.nonterminal name]],
     prods ++ altProds ++ [{ lhs := name, rhs := [] }], id)

/-- eBNFRule 配列を Grammar に変換 -/
def eBNFToGrammar (rules : Array eBNFRule) : Grammar :=
  let (prods, _) := rules.foldl (fun (prods, id) rule =>
    let (alts, extraProds, id) := exprToAlts rule.expr id
    let mainProds := alts.map fun rhs => ({ lhs := rule.name, rhs } : Production)
    (prods ++ extraProds ++ mainProds, id)
  ) ([], 0)
  let startSymbol := if h : 0 < rules.size then rules[0].name else ""
  { productions := prods, startSymbol }

/-- 拡張文法を作成（S' → S を追加） -/
def Grammar.augment (g : Grammar) : Grammar :=
  let startProd : Production := {
    lhs := g.startSymbol ++ "'"
    rhs := [.nonterminal g.startSymbol]
  }
  { productions := startProd :: g.productions
    startSymbol := g.startSymbol ++ "'" }

/-! ## LR(0) 項目集合の構築アルゴリズム -/

/-- closure: 項目集合の閉包を計算する。
    ドットの直後に非終端記号 A がある場合、A の全生成規則の初期項目を追加する。 -/
partial def closure (g : Grammar) (items : ItemSet) : ItemSet :=
  let rec go (worklist : ItemSet) (result : ItemSet) : ItemSet :=
    match worklist with
    | [] => result
    | item :: rest =>
      match item.nextSymbol with
      | some (.nonterminal nt) =>
        let newItems := g.productions
          |>.filter (·.lhs == nt)
          |>.map (fun p => ({ prod := p, dot := 0 } : LR0Item))
          |>.filter (fun i => !result.any (· == i))
        go (rest ++ newItems) (result ++ newItems)
      | _ => go rest result
  go items items

/-- goto: 項目集合 I と記号 X に対して、
    I 中のドットが X の直前にある項目のドットを進めた集合の閉包を返す。 -/
def goto_ (g : Grammar) (items : ItemSet) (sym : Symbol) : ItemSet :=
  let kernel := items
    |>.filter (fun item => item.nextSymbol == some sym)
    |>.map LR0Item.advance
  closure g kernel

/-- 文法中に出現する全記号を収集 -/
def Grammar.allSymbols (g : Grammar) : List Symbol :=
  g.productions.flatMap (·.rhs)
    |>.foldl (fun acc s => if acc.any (· == s) then acc else acc ++ [s]) []

/-- 項目集合の同値判定（順序を無視） -/
def itemSetEq (s1 s2 : ItemSet) : Bool :=
  s1.length == s2.length && s1.all (fun i => s2.any (· == i))

/-- 正規 LR(0) 項目集合族を構築する。
    初期状態 I₀ から始めて、全記号に対する goto を繰り返し新しい状態がなくなるまで拡張する。 -/
partial def canonicalCollection (g : Grammar) : List ItemSet :=
  let startItems := g.productions
    |>.filter (·.lhs == g.startSymbol)
    |>.map (fun p => ({ prod := p, dot := 0 } : LR0Item))
  let i0 := closure g startItems
  let allSyms := g.allSymbols
  let rec go (worklist : List ItemSet) (collection : List ItemSet) : List ItemSet :=
    match worklist with
    | [] => collection
    | items :: rest =>
      let newSets := allSyms.foldl (fun acc sym =>
        let next := goto_ g items sym
        if next.isEmpty then acc
        else if collection.any (itemSetEq next) || acc.any (itemSetEq next) then acc
        else acc ++ [next]
      ) []
      go (rest ++ newSets) (collection ++ newSets)
  go [i0] [i0]

/-! ## 表示ユーティリティ -/

def printGrammar (g : Grammar) : IO Unit := do
  IO.println s!"開始記号: {g.startSymbol}"
  IO.println "生成規則:"
  for p in g.productions do
    IO.println s!"  {p}"

def printItemSets (sets : List ItemSet) : IO Unit := do
  for h : i in [:sets.length] do
    IO.println s!"I{i}:"
    for item in sets[i] do
      IO.println s!"  {item}"
    IO.println ""

/-! ## 動作確認 -/

#eval do
  let input := "E = E, '+', T | T; T = T, '*', F | F; F = '(', E, ')' | 'id';"
  match ebnf.run input with
  | .error msg => IO.println s!"Parse error: {msg}"
  | .ok rules =>
    let g := (eBNFToGrammar rules).augment
    printGrammar g
    IO.println ""
    let sets := canonicalCollection g
    IO.println s!"状態数: {sets.length}"
    IO.println ""
    printItemSets sets