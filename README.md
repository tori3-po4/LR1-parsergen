# LR1-generator

## このコードの概要
このコードは学習のためにyaccやbisonのようなLR(1)パーサージェネレータを実装したのものです。
Lean言語を用いて実装されており、形式的証明によって動作が保証されることを目的としています。
ソースコードは基本的にClaude Codeによって書かれています。
今の所、eBNFをパースする部位のみ形式的証明がされています。

## 使い方

### ビルド

[Lean 4](https://lean-lang.org/) と Lake が必要です。

```bash
lake build
```

### 実行

```bash
lake exe lr1-generator <文法ファイル.ebnf> <レキサー定義.lex> [出力ファイル.c]
```

出力ファイルを省略した場合は `parser.c` に出力されます。

### 例

```bash
lake exe lr1-generator examples/expr.ebnf examples/expr.lex parser.c
cc -o parser parser.c
./parser 'x + y * (z + w)'
```

### 文法ファイル（eBNF）

終端記号はクォートで囲み、非終端記号はそのまま書きます。連接は `,`、選択は `|` で区切り、各ルールは `;` で終わります。

```
E = E, '+', T | T;
T = T, '*', F | F;
F = '(', E, ')' | 'id';
```

- `[ expr ]` — 省略可能（0回または1回）
- `{ expr }` — 繰り返し（0回以上）
- `( expr )` — グループ化

### レキサー定義ファイル

文法の終端記号をどのようにマッチさせるかを定義します。

```
# トークンパターン（文法の終端記号名に対応）
id = [a-zA-Z_] [a-zA-Z0-9_]* ;

# スキップパターン（空白など）
skip = [ \t\r\n]+ ;
```

- `[chars]` — 文字集合（`a-z` で範囲指定、`^` で否定）
- `+` — 1回以上の繰り返し
- `*` — 0回以上の繰り返し
- `'c'` — リテラル文字
- `"str"` — リテラル文字列
- `#` — 行コメント

レキサー定義に名前がある終端記号はパターンでマッチされます。定義がない終端記号はリテラル文字列として扱われます（記号 `+`, `*` 等はそのまま、英字の `if`, `while` 等はキーワードとして認識）。

## プロジェクト構成

```
LR1-generator/
├── Main.lean                  # エントリーポイント（引数処理・全体の制御フロー）
├── eBNFparser/
│   ├── Basic.lean             # eBNF パーサー（文法ファイルの読み取り）
│   └── BasicProof.lean        # eBNF パーサーの形式的証明
├── lexer/
│   ├── LexerDef.lean          # レキサー定義ファイルのデータ型とパーサー
│   └── Basic.lean             # レキサー C コード生成
├── LR1Generator/
│   └── Basic.lean             # LR(1) 項目集合・遷移表構築・パーサー C コード生成
├── examples/
│   ├── expr.ebnf              # サンプル文法ファイル
│   └── expr.lex               # サンプルレキサー定義ファイル
└── lakefile.toml              # Lake ビルド設定
```

### 処理の流れ

1. **eBNF パース** (`eBNFparser`) — 文法ファイルを読み込み、構文木 (`eBNFExpr`) に変換
2. **BNF 変換** (`LR1Generator`) — eBNF の繰り返し・省略等を展開し、BNF の生成規則 (`Grammar`) に変換。開始記号を拡張
3. **LR(1) 構築** (`LR1Generator`) — 正準 LR(1) 項目集合を構築し、ACTION/GOTO 遷移表を生成
4. **レキサー定義パース** (`lexer/LexerDef`) — レキサー定義ファイルを読み込み、トークンパターンとスキップパターンに変換
5. **C コード生成** (`lexer/Basic` + `LR1Generator`) — レキサーとパーサーを含む単一の C ファイルを出力
