# example_goto_3 / 4 を GHC で動かした記録 (2026-11-23)

- ソースは記事添付の `momo_hs-20110214.shar` のもの(`../../refs_callcc/momo_hs/v20110214/`)。
  記事本文のコードは LoopStart の行に余分な `case input of` があり、今の GHC では構文エラーになる(記事に写すときの誤り。実際のソースには無い)。
- 変更は `import System` をコメントにしただけ(GHC 7.2 以降は haskell98 の `System` が既定で使えない)。
- 環境: GHC 9.10.3(ghcup で一時的に導入、実験後に削除)、mtl/transformers は GHC 付属。

| ファイル | 入力 | 結果 |
|---|---|---|
| example_goto_3.hs / _4.hs | a b c d e | 記事と同じ出力、即終了 |
| example_goto_3_stop.hs / _4_stop.hs | a b **stop** d e | 何も出力せず、CPU 100%・メモリ一定(約 7.6MB)のまま終わらない(timeout で停止) |
| example_goto_3_jrfstop.hs | JRF がソース末尾にコメントで残した main(`{- The code blow fails into infinite loop. -}`) | 同上 |
| example_goto_3_stop_trace.hs | stop 版に `Debug.Trace` を足したもの | `[server got stop; output= slse  slend  clmn a sm1n a cr1n b clmn stop]` が同じ内容で延々と出る |

GHCi(`ghc --interactive -e main`)でも同じ(15 秒で CPU 15 秒、出力なし)。

再現手順:

```
ghcup install ghc 9.10.3
ghc -O0 example_goto_3_stop.hs && timeout 5 ./example_goto_3_stop +RTS -s
```

(Debian/Ubuntu で `-lgmp` が見つからないときは `libgmp-dev` を入れるか、`libgmp.so.10` へのリンクを置いて `-L` で渡す。)
