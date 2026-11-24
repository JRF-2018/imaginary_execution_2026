# report0 参考文献の照合記録 (2026-11-24)

記号: ✔ = Web で書誌(巻・号・頁または DOI)を照合した。◯ = 標準的な文献で記憶の書誌に問題は見当たらないが、今回は個別に照合していない。△ = 一部未確認(注を参照)。

## 追加した文献(0.2.0)

| 文献 | 状態 | 照合結果 |
|---|---|---|
| Alglave, Maranget, Tautschnig, "Herding cats: modelling, simulation, testing, and data mining for weak memory", ACM TOPLAS 36(2), 2014 | ✔ | Article 7, DOI 10.1145/2627752(PLDI 2014 版もある) |
| Chalupa, Chatterjee, Pavlogiannis, Sinha, Vaidya, "Data-centric dynamic partial order reduction", PACMPL 2(POPL), Article 31, 2018 | ✔ | DOI 10.1145/3158119。観測同値(各 read が同じ write を観測)で探索 |
| Abdulla, Atig, Jonsson, Lång, Ngo, Sagonas, "Optimal stateless model checking for reads-from equivalence under sequential consistency", PACMPL 3(OOPSLA), Article 150, 2019 | ✔ | DOI 10.1145/3360576 |
| R. J. Lipton, "Reduction: a method of proving properties of parallel programs", CACM 18(12), 717–721, 1975 | ✔ | DOI 10.1145/361227.361234 |
| S. V. Adve, M. D. Hill, "Weak ordering — a new definition", ISCA 1990, 2–14 | ✔ | DOI 10.1145/325164.325100。DRF(データ競合のないプログラムには逐次一貫に見える) |
| P. Godefroid, "Model checking for programming languages using VeriSoft", POPL 1997, 174–186 | ✔ | DOI 10.1145/263699.263717 |
| M. Musuvathi, S. Qadeer, T. Ball, G. Basler, P. A. Nainar, I. Neamtiu, "Finding and reproducing Heisenbugs in concurrent programs", OSDI 2008, 267–280 | ✔ | CHESS |

## 既存の文献

| 文献 | 状態 | 注 |
|---|---|---|
| Coffman, Elphick, Shoshani, "System deadlocks", ACM Computing Surveys 3(2), 67–78, 1971 | ✔ | 頁を追記 |
| Gibbons, Korach, "Testing shared memories", SIAM J. Computing 26(4), 1208–1244, 1997 | ✔ | 頁を追記 |
| Mazières, Shasha, "Building secure file systems out of Byzantine storage", PODC 2002, 108–117 | ✔ | 頁を追記 |
| Flanagan, Qadeer, "Thread-modular model checking", SPIN 2003, LNCS 2648 | ✔ | DOI 10.1007/3-540-44829-2_14(Springer)。頁は確認できなかったので DOI で示す(0.4.0) |
| Kauffman, "Imaginary values in mathematical logic", Proc. 17th ISMVL, 282–289, 1987 | ✔ | 頁を追記 |
| Friedman, Morris, Novikov, Echeverria, Klinkhammer, Thorne, Yurtsever, "Cauchy problem in spacetimes with closed timelike curves", Phys. Rev. D 42(6), 1915–1930, 1990 | ✔ | DOI 10.1103/PhysRevD.42.1915。著者の並びは文献の参照リストで確認(0.4.0) |
| ホフスタッター『ゲーデル，エッシャー，バッハ』白揚社 | △ | NDL で 1985 年版(765p)を確認。0.1.0 に書いた「20周年記念版 2005」は確認できなかったので 1985 年版の書誌に改めた |
| Dijkstra EWD123; Lamport 1979; Herlihy & Wing 1990; Mazurkiewicz 1977; Godefroid 1996; Flanagan & Godefroid 2005; Musuvathi & Qadeer 2007; Burckhardt ら 2010; Cousot & Cousot 1977; Clarke ら 2000; Owicki & Gries 1976; Jones 1983; Shapiro ら 2011; Milner 1999; Fajstrup ら 2016 | ◯ | |
| Girard 1987; Wootters & Zurek 1982; Bombelli 1572; Spencer-Brown 1969; Feynman 1987; Renou ら 2021; Coleman 1977; Deutsch 1991; Wainwright & Jordan 2008 | ◯ | |
| JRF の記事・ひとこと・『宗教学雑考集』 | ✔ | report0/refs/ に本文を保存済み |
| de Moura, Ullrich, "The Lean 4 theorem prover and programming language", CADE-28, LNCS 12699, 2021; The mathlib Community, "The Lean mathematical library", CPP 2020 | ◯ | 付録で使用。個別には照合していない |
| Boehm, Demsky, "Outlawing ghosts: avoiding out-of-thin-air results", MSPC 2014 | ✔ | DOI 10.1145/2618128.2618134(0.3.1 で追加) |
| Batty, Memarian, Nienhuis, Pichon-Pharabod, Sewell, "The problem of programming language concurrency semantics", ESOP 2015, LNCS 9032, 283–307 | ✔ | DOI 10.1007/978-3-662-46669-8_12。候補実行ごとの条件では thin-air 問題が解けないことを示す(0.3.1 で追加) |
| OEIS A027907・A002426・A082758 | ✔ | OEIS の検索で 1, 3, 19, 141, 1107, 8953 が A082758 に一致することを確認(0.4.2)。A002426 の偶数番目との一致と A027907 との一致は計算で確認 |
