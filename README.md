# 項書換えシステムの簡単な実装

## ファイル構成

- `trs.pl` - 項書換えシステム本体
- `test.pl` - テストプログラム
- `rules/de_morgan.rule` - ド・モルガンの定理
- `rules/propositional.rule` - 命題論理
- `rules/calc.rule` - 積・和の計算

## ルール記述方法

ファイルに以下の文法でルールを記述します。

```prolog
'ルール名(アトム)' @ 書き換え前リスト <=> 書き換え後リスト.
```

ルール適用条件（ガード条件）を指定することもできます。

```prolog
'ルール名(アトム)' @ 書き換え前リスト <=> ガード条件 | 書き換え後リスト.
```

また、以下の場合には '\' の前に記述された条件に合致するものがある場合にのみ書き換えを行います。

```prolog
'ルール名(アトム)' @ 条件リスト \ 書き換え前リスト <=> 書き換え後リスト.
'ルール名(アトム)' @ 条件リスト \ 書き換え前リスト <=> ガード条件 | 書き換え後リスト.
```

### 説明
- 書き換え前リスト、書き換え後リストは、カンマ区切りで項を列挙します
- 項とガード条件の記述方法は Prolog と同じです
- ガード条件に記述する述語をルールファイル内で定義する場合は、`assert/1` を利用可能です
- 複数回ルールファイルを読み込む場合、前回 `assert` した内容の重複を防ぐために `abolish/1` も利用可能です

詳細な記述例は `rules/` ディレクトリのファイルを参照ください。

## 実行例

1. `trs.pl` と `test.pl` が存在するディレクトリで `swipl` を起動します
2. テストプログラムを読み込みます：

```prolog
?- [test].
```

3. ルールファイルを読み込みます：

```prolog
?- setup.
```

4. テストを実行します：

```prolog
?- test.
```

実行結果の詳細は `example.txt` を参照ください。

## 動作環境

- SWI-Prolog version 9.0.4 for x86_64-linux での動作を確認しています

## API

- `trs_load_rules(File)` - ルールファイルの内容を読み込む。
- `trs_dump_all_rules` - 読み込んだルール全てを表示する。
- `trs_abolish_all_rules` - 読み込んだルール全てを破棄する。
- `trs_loop(InTerms, OutTerms, Rules, MaxSteps)` - InTerms (list) に対してルールを最大 MaxSteps (integer) 回適用し、結果を OutTerms (list)、適用ルール履歴を Rules (list) として得る。
- `trs_dump_history(InTerms, Rules)` - `trs_loop/4` 実行の履歴をダンプする。
- `max_depth_of_terms(Terms, Depth)` - 項の最大深さを返す。
- `trs_resolve(InTerms, OutTerms, MaxSteps, MaxDepth)` - 最終結果の項の最大深さを MaxDepth (integer) に制限したうえで `trs_loop/4` を使ってルール適用を行い、その結果を `trs_dump_history/2` で表示する。
- `trs_resolve(InTerms, OutTerms)` - MaxSteps=100, MaxDepth=2 でデフォルト実行する。