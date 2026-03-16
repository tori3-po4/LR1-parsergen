import eBNFparser.Basic

/-! # LR(1) 項目集合の構築 -/

/-- 文法記号 -/
inductive Symbol where
  | terminal : String → Symbol
  | nonterminal : String → Symbol
  deriving BEq, Repr, Inhabited

instance : ToString Symbol where
  toString
    | .terminal s => s!"'{s}'"
    | .nonterminal s => s

/-- 先読み記号 -/
inductive Lookahead where
  | terminal : String → Lookahead
  | endMarker : Lookahead  -- $
  deriving BEq, Repr

instance : ToString Lookahead where
  toString
    | .terminal s => s!"'{s}'"
    | .endMarker => "$"

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

/-- LR(1) 項目: [A → α · β, a] -/
structure LR1Item where
  prod : Production
  dot : Nat
  lookahead : Lookahead
  deriving BEq, Repr

instance : ToString LR1Item where
  toString item :=
    let before := item.prod.rhs.take item.dot |>.map toString
    let after := item.prod.rhs.drop item.dot |>.map toString
    let rhs := " ".intercalate (before ++ ["·"] ++ after)
    s!"[{item.prod.lhs} → {rhs}, {item.lookahead}]"

/-- ドットの次の記号 -/
def LR1Item.nextSymbol (item : LR1Item) : Option Symbol :=
  item.prod.rhs[item.dot]?

/-- ドットより後の記号列（ドット直後を含まない） -/
def LR1Item.afterNext (item : LR1Item) : List Symbol :=
  item.prod.rhs.drop (item.dot + 1)

/-- ドットを一つ進める -/
def LR1Item.advance (item : LR1Item) : LR1Item :=
  { item with dot := item.dot + 1 }

/-- 項目集合 -/
abbrev ItemSet := List LR1Item

/-! ## eBNF → BNF 変換 -/

/-- eBNFExpr を生成規則の右辺（代替のリスト）に変換する -/
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

/-! ## FIRST 集合の計算 -/

/-- 非終端記号が空列を導出できるかの判定（nullable） -/
partial def computeNullable (g : Grammar) : List String :=
  let rec go (nullable : List String) : List String :=
    let newNullable := g.productions.foldl (fun acc p =>
      if acc.any (· == p.lhs) then acc
      else if p.rhs.all (fun s => match s with
        | .nonterminal n => acc.any (· == n)
        | .terminal _ => false)
      then acc ++ [p.lhs]
      else acc
    ) nullable
    if newNullable.length == nullable.length then nullable
    else go newNullable
  go []

/-- 記号列の FIRST 集合を計算する -/
def firstOfSymbols (g : Grammar) (nullable : List String)
    (firstMap : List (String × List Lookahead)) (syms : List Symbol)
    (trailing : Lookahead) : List Lookahead :=
  match syms with
  | [] => [trailing]
  | .terminal t :: _ => [.terminal t]
  | .nonterminal n :: rest =>
    let nFirst := match firstMap.find? (fun (k, _) => k == n) with
      | some (_, fs) => fs
      | none => []
    if nullable.any (· == n) then
      let restFirst := firstOfSymbols g nullable firstMap rest trailing
      (nFirst ++ restFirst).foldl (fun acc x =>
        if acc.any (· == x) then acc else acc ++ [x]) []
    else nFirst

/-- 文法全体の FIRST 集合を固定点計算で求める -/
partial def computeFirstMap (g : Grammar) (nullable : List String) :
    List (String × List Lookahead) :=
  let nts := g.productions.map (·.lhs)
    |>.foldl (fun acc n => if acc.any (· == n) then acc else acc ++ [n]) []
  let initMap := nts.map (·, [])
  let rec go (fm : List (String × List Lookahead)) : List (String × List Lookahead) :=
    let newFm := g.productions.foldl (fun fm p =>
      let rhsFirst := match p.rhs with
        | [] => []
        | .terminal t :: _ => [Lookahead.terminal t]
        | .nonterminal n :: rest =>
          let nFirst := match fm.find? (fun (k, _) => k == p.lhs) with
            | some _ =>
              match fm.find? (fun (k, _) => k == n) with
              | some (_, fs) => fs
              | none => []
            | none => []
          if nullable.any (· == n) then
            -- n は nullable なので rest の FIRST も含める
            let restSyms := rest
            let restFirst := restSyms.foldl (fun acc sym =>
              match sym with
              | .terminal t => if acc.1 then (false, acc.2 ++ [Lookahead.terminal t]) else acc
              | .nonterminal m =>
                if !acc.1 then acc
                else
                  let mFirst := match fm.find? (fun (k, _) => k == m) with
                    | some (_, fs) => fs
                    | none => []
                  if nullable.any (· == m) then (true, acc.2 ++ mFirst)
                  else (false, acc.2 ++ mFirst)
            ) (true, nFirst)
            restFirst.2
          else nFirst
      -- rhsFirst を p.lhs の FIRST に追加
      fm.map fun (k, fs) =>
        if k == p.lhs then
          (k, (fs ++ rhsFirst).foldl (fun acc x =>
            if acc.any (· == x) then acc else acc ++ [x]) [])
        else (k, fs)
    ) fm
    let changed := fm.zip newFm |>.any fun ((_, fs1), (_, fs2)) => fs1.length != fs2.length
    if changed then go newFm else newFm
  go initMap

/-! ## LR(1) 項目集合の構築アルゴリズム -/

/-- closure: LR(1) 項目集合の閉包を計算する。
    [A → α · B β, a] に対して、FIRST(βa) の各 b について [B → · γ, b] を追加する。 -/
partial def closure (g : Grammar) (nullable : List String)
    (firstMap : List (String × List Lookahead)) (items : ItemSet) : ItemSet :=
  let rec go (worklist : ItemSet) (result : ItemSet) : ItemSet :=
    match worklist with
    | [] => result
    | item :: rest =>
      match item.nextSymbol with
      | some (.nonterminal nt) =>
        let beta := item.afterNext
        let lookaheads := firstOfSymbols g nullable firstMap beta item.lookahead
        let newItems := g.productions
          |>.filter (·.lhs == nt)
          |>.flatMap (fun p =>
            lookaheads.map fun la =>
              ({ prod := p, dot := 0, lookahead := la } : LR1Item))
          |>.filter (fun i => !result.any (· == i))
        go (rest ++ newItems) (result ++ newItems)
      | _ => go rest result
  go items items

/-- goto: 項目集合 I と記号 X に対して、
    I 中のドットが X の直前にある項目のドットを進めた集合の閉包を返す。 -/
def goto_ (g : Grammar) (nullable : List String)
    (firstMap : List (String × List Lookahead))
    (items : ItemSet) (sym : Symbol) : ItemSet :=
  let kernel := items
    |>.filter (fun item => item.nextSymbol == some sym)
    |>.map LR1Item.advance
  closure g nullable firstMap kernel

/-- 文法中に出現する全記号を収集 -/
def Grammar.allSymbols (g : Grammar) : List Symbol :=
  g.productions.flatMap (·.rhs)
    |>.foldl (fun acc s => if acc.any (· == s) then acc else acc ++ [s]) []

/-- 項目集合の同値判定（順序を無視） -/
def itemSetEq (s1 s2 : ItemSet) : Bool :=
  s1.length == s2.length && s1.all (fun i => s2.any (· == i))

/-- 正規 LR(1) 項目集合族を構築する -/
partial def canonicalCollection (g : Grammar) : List ItemSet :=
  let nullable := computeNullable g
  let firstMap := computeFirstMap g nullable
  let startItems := g.productions
    |>.filter (·.lhs == g.startSymbol)
    |>.map (fun p => ({ prod := p, dot := 0, lookahead := .endMarker } : LR1Item))
  let i0 := closure g nullable firstMap startItems
  let allSyms := g.allSymbols
  let rec go (worklist : List ItemSet) (collection : List ItemSet) : List ItemSet :=
    match worklist with
    | [] => collection
    | items :: rest =>
      let newSets := allSyms.foldl (fun acc sym =>
        let next := goto_ g nullable firstMap items sym
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