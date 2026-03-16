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

/-! ## LR(1) 遷移表の構築 -/

/-- パース動作 -/
inductive Action where
  | shift : Nat → Action
  | reduce : Nat → Production → Action  -- 生成規則番号と規則
  | accept : Action
  deriving BEq, Repr

instance : ToString Action where
  toString
    | .shift n => s!"s{n}"
    | .reduce n p => s!"r{n}({p})"
    | .accept => "acc"

/-- 衝突の種類 -/
inductive Conflict where
  | shiftReduce : Nat → Lookahead → Action → Action → Conflict
  | reduceReduce : Nat → Lookahead → Action → Action → Conflict
  deriving Repr

instance : ToString Conflict where
  toString
    | .shiftReduce state la a1 a2 =>
      s!"shift/reduce 衝突 状態{state}, {la}: {a1} vs {a2}"
    | .reduceReduce state la a1 a2 =>
      s!"reduce/reduce 衝突 状態{state}, {la}: {a1} vs {a2}"

/-- LR(1) 遷移表 -/
structure ParseTable where
  actionTable : List (Nat × Lookahead × Action)
  gotoTable : List (Nat × String × Nat)
  conflicts : List Conflict
  numStates : Nat
  deriving Repr

/-- 項目集合族から状態番号を検索 -/
def findStateIndex (collection : List ItemSet) (target : ItemSet) : Option Nat :=
  let rec go (sets : List ItemSet) (idx : Nat) : Option Nat :=
    match sets with
    | [] => none
    | s :: rest => if itemSetEq s target then some idx else go rest (idx + 1)
  go collection 0

/-- 生成規則の番号を検索 -/
def findProdIndex (g : Grammar) (p : Production) : Nat :=
  let rec go (prods : List Production) (idx : Nat) : Nat :=
    match prods with
    | [] => idx
    | q :: rest => if q == p then idx else go rest (idx + 1)
  go g.productions 0

/-- LR(1) 遷移表を構築する -/
def buildParseTable (g : Grammar) (collection : List ItemSet) : ParseTable :=
  let nullable := computeNullable g
  let firstMap := computeFirstMap g nullable
  -- 各状態について ACTION と GOTO のエントリを生成
  let (actions, gotos, _) := collection.foldl (fun (acts, gts, i) items =>
    -- ACTION: 各項目から動作を決定
    let acts := items.foldl (fun acts item =>
      match item.nextSymbol with
      | some (.terminal t) =>
        let target := goto_ g nullable firstMap items (.terminal t)
        match findStateIndex collection target with
        | some j => acts ++ [(i, Lookahead.terminal t, Action.shift j)]
        | none => acts
      | some (.nonterminal _) => acts
      | none =>
        if item.prod.lhs == g.startSymbol then
          acts ++ [(i, item.lookahead, Action.accept)]
        else
          let prodIdx := findProdIndex g item.prod
          acts ++ [(i, item.lookahead, Action.reduce prodIdx item.prod)]
    ) acts
    -- GOTO: 非終端記号による遷移
    let gts := g.allSymbols.foldl (fun gts sym =>
      match sym with
      | .nonterminal nt =>
        let target := goto_ g nullable firstMap items (.nonterminal nt)
        match findStateIndex collection target with
        | some j => gts ++ [(i, nt, j)]
        | none => gts
      | .terminal _ => gts
    ) gts
    (acts, gts, i + 1)
  ) (([], [], 0) : List (Nat × Lookahead × Action) × List (Nat × String × Nat) × Nat)
  -- 重複を除去して衝突を検出
  let (uniqueActions, conflicts) := actions.foldl (fun acc entry =>
    let (unique, confs) := acc
    let (s, la, act) := entry
    match unique.find? (fun (s', la', _) => s == s' && la == la') with
    | some (_, _, existing) =>
      if existing == act then (unique, confs)
      else
        let conflict := match existing, act with
          | .shift _, .reduce .. | .reduce .., .shift _ =>
            Conflict.shiftReduce s la existing act
          | _, _ => Conflict.reduceReduce s la existing act
        (unique, confs ++ [conflict])
    | none => (unique ++ [(s, la, act)], confs)
  ) ((([] : List (Nat × Lookahead × Action)), ([] : List Conflict)))
  { actionTable := uniqueActions
    gotoTable := gotos
    conflicts := conflicts
    numStates := collection.length }

/-- 状態の ACTION エントリを取得 -/
def ParseTable.getAction (t : ParseTable) (state : Nat) (la : Lookahead) : Option Action :=
  t.actionTable.find? (fun (s, l, _) => s == state && l == la) |>.map (·.2.2)

/-- 状態の GOTO エントリを取得 -/
def ParseTable.getGoto (t : ParseTable) (state : Nat) (nt : String) : Option Nat :=
  t.gotoTable.find? (fun (s, n, _) => s == state && n == nt) |>.map (·.2.2)

/-! ## 表示ユーティリティ -/

def printGrammar (g : Grammar) : IO Unit := do
  IO.println s!"開始記号: {g.startSymbol}"
  IO.println "生成規則:"
  let mut i := 0
  for p in g.productions do
    IO.println s!"  ({i}) {p}"
    i := i + 1

def printItemSets (sets : List ItemSet) : IO Unit := do
  for h : i in [:sets.length] do
    IO.println s!"I{i}:"
    for item in sets[i] do
      IO.println s!"  {item}"
    IO.println ""

/-- 遷移表を状態ごとに表示する -/
def printParseTable (table : ParseTable) : IO Unit := do
  for i in [:table.numStates] do
    let stateActions := table.actionTable.filter (·.1 == i)
    let stateGotos := table.gotoTable.filter (·.1 == i)
    if !stateActions.isEmpty || !stateGotos.isEmpty then
      IO.println s!"状態 {i}:"
      for (_, la, act) in stateActions do
        IO.println s!"  ACTION[{la}] = {act}"
      for (_, nt, target) in stateGotos do
        IO.println s!"  GOTO[{nt}] = {target}"
  if !table.conflicts.isEmpty then
    IO.println ""
    IO.println s!"⚠ 衝突 {table.conflicts.length} 件:"
    for c in table.conflicts do
      IO.println s!"  {c}"
  else
    IO.println ""
    IO.println "衝突なし — LR(1) 文法です"

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
    let table := buildParseTable g sets
    printParseTable table