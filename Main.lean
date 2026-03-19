import LR1Generator
import eBNFparser
import lexer

def usage : String :=
  "Usage: lr1-generator <grammar.ebnf> <lexer.lex> [output.c]\n\n" ++
  "eBNF 文法ファイルとレキサー定義ファイルから\n" ++
  "LR(1) パーサーの C コードを生成します。\n" ++
  "出力ファイルを省略した場合は parser.c に出力します。"

def main (args : List String) : IO UInt32 := do
  match args with
  | inputPath :: lexerPath :: rest =>
    let outputPath := match rest with
      | outPath :: _ => outPath
      | [] => "parser.c"

    -- 1. 文法ファイルの読み込み
    let content ← IO.FS.readFile inputPath
    IO.println s!"[1/5] 文法ファイル {inputPath} を読み込みました ({content.length} bytes)"

    -- 2. eBNF パース
    match ebnf.run content with
    | .error msg =>
      IO.eprintln s!"パースエラー: {msg}"
      return 1
    | .ok rules =>
      IO.println s!"[2/5] eBNF パース完了 — {rules.size} 個のルール"
      for r in rules do
        IO.println s!"  {r.name} = {repr r.expr}"

      -- 3. BNF 変換 + 拡張文法
      let g := (eBNFToGrammar rules).augment
      IO.println s!"[3/5] BNF 変換完了 — {g.productions.length} 個の生成規則"
      let mut i := 0
      for p in g.productions do
        IO.println s!"  ({i}) {p}"
        i := i + 1

      -- 4. LR(1) 項目集合と遷移表の構築
      let sets := canonicalCollection g
      let table := buildParseTable g sets
      IO.println s!"[4/5] LR(1) 遷移表構築完了 — {sets.length} 状態"

      if !table.conflicts.isEmpty then
        IO.eprintln s!"警告: {table.conflicts.length} 件の衝突があります"
        for c in table.conflicts do
          IO.eprintln s!"  {c}"

      -- レキサー定義ファイルの読み込み
      let lexContent ← IO.FS.readFile lexerPath
      IO.println s!"  レキサー定義 {lexerPath} を読み込みました ({lexContent.length} bytes)"
      match (lexerDefParser.run lexContent : Except String LexerDef) with
      | Except.error msg =>
        IO.eprintln s!"レキサー定義パースエラー: {msg}"
        return 1
      | Except.ok lexerDef =>
        IO.println s!"  トークンルール: {lexerDef.tokens.size} 個、スキップルール: {lexerDef.skips.size} 個"

        -- 5. レキサー + パーサーの C コード生成
        let terminals := collectTerminals g
        let toTokName := fun t => s!"TOK_{toCIdentifier t.toUpper}"
        let lexerCode := generateLexerC terminals toTokName lexerDef
        writeCFile outputPath g table (middleCode := "\n" ++ lexerCode ++ "\n")
        IO.println s!"[5/5] 完了: {outputPath}"

        return 0
  | _ =>
    IO.eprintln usage
    return 1
