import Std.Internal.Parsec
import Std.Internal.Parsec.String
open Std.Internal
open Parsec String

inductive eBNFExpr
  | terminal : String →  eBNFExpr
  | nonterminal : String →  eBNFExpr
  | seq : List eBNFExpr →  eBNFExpr
  | alt : List eBNFExpr →  eBNFExpr
  | opt : eBNFExpr →  eBNFExpr
  | rep : eBNFExpr →  eBNFExpr
  | group : eBNFExpr →  eBNFExpr
  deriving Repr

structure eBNFRule where
  name : String
  expr : eBNFExpr
  deriving Repr

def terminal : Parser eBNFExpr := do
  let quote ← satisfy (λ c=>c =='"' || c =='\'')
  let s ← manyChars (satisfy (· != quote))
  let _ ← satisfy (· == quote)
  ws
  return eBNFExpr.terminal s

def identifier : Parser String := do
  let head ← satisfy Char.isAlpha
  let tail ← manyChars (satisfy (λ c => Char.isAlphanum c || c == '_'))
  ws
  return head.toString ++ tail

mutual

partial def expression : Parser eBNFExpr := do
  let first ← sequence_
  let rest ← many (attempt do skipChar '|' ; ws ; sequence_)
  if rest.isEmpty then return first
  else return .alt (first :: rest.toList)

partial def sequence_ : Parser eBNFExpr := do
  let first ← atom
  let rest ← many (attempt do skipChar ','; ws; atom)
  if rest.isEmpty then return first
  else return .seq (first :: rest.toList)

partial def atom : Parser eBNFExpr :=
  terminal
  <|> (do skipChar '['; ws; let e ← expression; skipChar ']'; ws; return .opt e)
  <|> (do skipChar '{'; ws; let e ← expression; skipChar '}'; ws; return .rep e)
  <|> (do skipChar '('; ws; let e ← expression; skipChar ')'; ws; return .group e)
  <|> (do let n ← identifier; return .nonterminal n)

partial def rule : Parser eBNFRule := do
  ws
  let name ← identifier
  skipChar '='
  ws
  let e ← expression
  skipChar ';'
  ws
  return { name, expr := e}

partial def ebnf : Parser (Array eBNFRule) := do
  ws
  let rules ←  many rule
  eof
  return rules

end

#eval do
  match ebnf.run "digit = \"0\" | \"1\" | \"2\";" with
  | .ok result  => IO.println (repr result)
  | .error msg  => IO.println s!"Parse error: {msg}"
