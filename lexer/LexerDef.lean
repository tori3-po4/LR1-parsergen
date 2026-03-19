import Std.Internal.Parsec
import Std.Internal.Parsec.String
open Std.Internal
open Parsec String

/-! # Lexer 定義ファイルのパーサー

lexer ファイルから LexerDef を構築する。

## ファイル形式

```
# コメント
NUMBER = [0-9]+ ;
ID     = [a-zA-Z_] [a-zA-Z0-9_]* ;
STRING = '"' [^"]* '"' ;
skip   = [ \t\r\n]+ ;
```

- `[chars]` : 文字集合 (`a-z` で範囲指定、`^` で否定)
- `+` : 1回以上
- `*` : 0回以上
- `'c'` : リテラル文字
- `"str"` : リテラル文字列
- `skip` : スキップパターン（空白・コメント等）
-/

/-- 文字範囲 -/
inductive CharRange where
  | range : Char → Char → CharRange
  | single : Char → CharRange
  deriving Repr

/-- 文字集合 -/
structure CharSet where
  ranges : List CharRange
  negated : Bool := false
  deriving Repr

/-- パターンの1ステップ -/
inductive PatternStep where
  | one : CharSet → PatternStep
  | oneOrMore : CharSet → PatternStep
  | zeroOrMore : CharSet → PatternStep
  | litChar : Char → PatternStep
  | litStr : String → PatternStep
  deriving Repr

/-- レキサールール -/
structure LexRule where
  name : String
  pattern : List PatternStep
  deriving Repr

/-- レキサー定義 -/
structure LexerDef where
  tokens : Array LexRule
  skips : Array (List PatternStep)
  deriving Repr

-- パーサー内部

private inductive LexEntry where
  | token : LexRule → LexEntry
  | skip : List PatternStep → LexEntry

private def escChar : Parser Char := do
  let _ ← pchar '\\'
  let c ← any
  match c with
  | 'n' => return '\n'
  | 't' => return '\t'
  | 'r' => return '\r'
  | '\\' => return '\\'
  | ']' => return ']'
  | '-' => return '-'
  | '\'' => return '\''
  | '"' => return '"'
  | ' ' => return ' '
  | _ => fail s!"不明なエスケープ: \\{c}"

private def classChar : Parser Char :=
  attempt escChar <|> satisfy (fun c => c != ']' && c != '\\')

private def charRange_ : Parser CharRange := do
  let lo ← classChar
  (attempt do
    let _ ← pchar '-'
    let hi ← classChar
    return .range lo hi) <|> return .single lo

private def charSet_ : Parser CharSet := do
  let _ ← pchar '['
  let neg ← (attempt (pchar '^' *> pure true)) <|> pure false
  let first ← charRange_
  let rest ← many charRange_
  let _ ← pchar ']'
  return { ranges := first :: rest.toList, negated := neg }

private def litChar_ : Parser PatternStep := do
  let _ ← pchar '\''
  let c ← attempt escChar <|> satisfy (· != '\'')
  let _ ← pchar '\''
  return .litChar c

private def litStr_ : Parser PatternStep := do
  let _ ← pchar '"'
  let s ← manyChars (attempt escChar <|> satisfy (fun c => c != '"' && c != '\\'))
  let _ ← pchar '"'
  return .litStr s

private def charSetStep : Parser PatternStep := do
  let cs ← charSet_
  (attempt (pchar '+' *> pure (.oneOrMore cs)))
  <|> (attempt (pchar '*' *> pure (.zeroOrMore cs)))
  <|> pure (.one cs)

private def patternStep_ : Parser PatternStep :=
  charSetStep <|> litChar_ <|> litStr_

private def pattern_ : Parser (List PatternStep) := do
  let first ← patternStep_
  let rest ← many (attempt do ws; patternStep_)
  return first :: rest.toList

private def wsComments : Parser Unit := do
  ws
  let _ ← many (attempt do
    let _ ← pchar '#'
    let _ ← manyChars (satisfy (· != '\n'))
    ws)

private def lexEntry_ : Parser LexEntry := do
  wsComments
  let head ← satisfy Char.isAlpha
  let tail ← manyChars (satisfy (fun c => Char.isAlphanum c || c == '_'))
  let name := head.toString ++ tail
  ws
  let _ ← pchar '='
  ws
  let p ← pattern_
  ws
  let _ ← pchar ';'
  if name == "skip" then
    return .skip p
  else
    return .token { name, pattern := p }

def lexerDefParser : Parser LexerDef := do
  let entries ← many (attempt lexEntry_)
  wsComments
  eof
  let tokens := entries.filterMap fun e => match e with
    | .token r => some r | _ => none
  let skips := entries.filterMap fun e => match e with
    | .skip p => some p | _ => none
  return { tokens, skips }
