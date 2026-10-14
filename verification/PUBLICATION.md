# 公開までの手順

FCの v4.33.1 固定環境でprivate CIが成功しました。対象はコミット
`e2732a7961dc6b1ffeb42fe036a6d2561428bdd1`、run `38573608382` のattempt 1です。
証明の全量検証・Comparator・独立再検証・算術チェックをすべて通過しています。
[成功記録](private-ci/README.md)を保存し、同じ証明とchecker設定をpublicで再検証します。
public CIの成功は、その実行結果を確認してから記録します。

## 1. ローカルで確認する

このフォルダで次を実行します。

```sh
python3 lean/comparator/check-inputs.py
```

ファイル一覧とハッシュ、976個の元のLeanモジュール、定理文、固定したバージョンを
確認します。これはLean証明の実行ではありません。数学の有限検算は
`python3 -m verification` で再計算できます。再計算すると日時を含む結果ファイルが
更新されるため、公開候補のハッシュ一覧も更新してから次へ進みます。

意図した修正後のハッシュ更新は次のコマンドです。検証済みという状態には変更しません。

```sh
python3 lean/comparator/refresh-manifest.py
```

## 2. privateのci-test-sandboxで試す

`KitaKen1/ci-test-sandbox` には別プロジェクトの履歴があります。
Kalai用の `kalai-publication-test` ブランチを新しく用意し、この候補のファイルを
置いてpushします。既存のmainは書き換えません。workflowはこのブランチ名でも動きます。

Actionsで `Kalai target verification` を開き、最後の `verification_status` を確認します。
buildだけが緑でも完了ではありません。Comparator、fresh replay、arithmeticの
すべてのジョブが成功している必要があります。途中で失敗したら、そのブランチで修正し、
もう一度実行します。各run・attemptで全量ビルドを実行し、その成功後にだけ
同じattemptのビルドを後続のComparatorと独立再検証へ渡します。

成功したrunのURL、run ID、attempt、コミットを記録します。privateのURLは外部の人には
見えません。公開用の実行結果の代わりには使いません。

## 3. publicのkalai-three-pow-fiveで再検証する

privateで通った証明、定理文、checkerの版と設定を、同じ内容で
`KitaKen1/kalai-three-pow-five` に持っていきます。このpublicリポジトリにはPDF版の
既存履歴があるので、そのmainを取得してからファイルを反映します。
既存履歴をforce-pushで置き換える作業は不要です。

publicのmainへpushして、同じworkflowを実行します。公開先でも全ジョブが成功したら、
そのrunをREADMEからリンクします。privateの成功だけで「public CI passed」とは書きません。

## 4. ログを保存する

workflowはbuild、comparator、replay、arithmeticの4つのartifactを90日保存します。
各artifactに実際のログ、公理一覧、入力ハッシュなどが入ります。
GitHub側の保持期間の上限が短い場合は、その設定が優先します。

public成功後に、実際のrun ID、attempt、40文字のコミットを指定して保存します。
次の大文字の部分は実値へ置き換えます。

```sh
python3 verification/archive-run.py \
  --repo KitaKen1/kalai-three-pow-five \
  --run RUN_ID --attempt ATTEMPT \
  --expected-commit COMMIT_SHA \
  --output ComparatorLogYYYYMMDD \
  --public-success-only
```

保存先は新しいフォルダを指定します。スクリプトはGitHubの認証情報を使って取得し、
元のZIP、artifactのGitHub digest、jobログ、runの情報、検証receiptを照合します。
成功の照合が終わってから保存先を確定します。認証情報は保存しません。

## 5. FCの証明リンクを更新する

`FClikelean/Kalai.lean` の5次元の定理には、以前検証済みの固定コミットへの
証明リンクを付けています。新しいpublic CIが通った後、そのpublicコミットでの
`lean/Kalai5/FormalConjectures.lean` の最終定理へリンクを更新します。

一般次元と6以上の定理はopen、4以下は文献でsolvedという分類を維持します。
今回Comparatorが検査するのは、5次元の `Kalai.three_pow_five` だけです。
FCへのissue投稿・PR作成は、このCI検証とは別の作業です。
