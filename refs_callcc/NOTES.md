(公開版の注: 作業中に保存した記事の写し、Hackage の各版のソース(`hackage/`)は、このリポジトリには入れていません。`momo_hs/` は JRF が 2011 年に配布したソースです。)

# callCC の定義の変遷メモ (2026-11-23 調査)

記事《Haskell の callCC で goto を作る》(2011-01-20) は HaskellPlatform-2010.2.0.0 の WinGHCi(GHC 6.12.3)で実行。

| 版 | Cont の定義 | callCC |
|---|---|---|
| mtl-1.1.0.2(2010 年ごろの標準) | `newtype Cont r a = Cont { runCont :: (a -> r) -> r }` | `callCC f = Cont $ \c -> runCont (f (\a -> Cont $ \_ -> c a)) c` |
| transformers-0.2.2.0(mtl-2.0 系、2010-11 に Platform 採用が合意) | `type Cont r = ContT r Identity`、構築は `cont` | `callCC f = ContT $ \c -> runContT (f (\a -> ContT $ \_ -> c a)) c` |
| transformers-0.6.1.2(現行) | 同上 | 同上(変数名だけ違う) |

- callCC の意味は 2010 年から現在まで同一。`hackage/` に各版のソースを保存。
- 変わったのは周辺: mtl-2 で `Cont` データ構築子が消えた(記事のコードは使っていないので影響なし)。GHC 7.2 以降 `import System`(haskell98)が既定で使えない → 今のGHCでは記事のコードはこの行で止まる。この行をコメントにするだけで GHC 9.10.3 で通ることを確認した(callcc/hs/README.md)。
- GHC 7.6 までは既定の最大スタックが 8M(+RTS -K)、7.8 から物理メモリの 80%(GHC #8189)。stop の無限ループが当時「止まらない」か「Stack space overflow」になるかは、ループがスタックを伸ばすかどうか次第で、GHC が無いので未確認。
- callcc/goto3_cps.py は上の callCC の定義をそのまま Python に写したもの。

## GHC 9.10.3 での実測(callcc/hs/README.md)

- stop を送ると、出力なし・CPU 100%・メモリ一定のまま終わらない。スタックもヒープも伸びないので、当時の 8M のスタック上限にも当たらず、2011 年の GHC でも同じく「黙って固まる」はず(当時の GHC では未確認)(JRF の「値も出さずに止まった」という記憶と合う)。
- JRF 自身、`momo_hs` の example_goto_3.hs 末尾に stop を送る別の main を残し、`{- The code blow fails into infinite loop. -}` と書いていた。
- 記事本文のコードの LoopStart にある `case input of` は、記事に写すときに紛れ込んだ誤り(添付ソースには無い)。
