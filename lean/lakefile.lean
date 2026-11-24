import Lake
open Lake DSL

package imaginary_execution

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.34.1"

/-- 各レポートの定理(ファイルごとに独立したモジュール)。 -/
@[default_target]
lean_lib ImagExec where
  srcDir := "."
  roots := #[`Thm1, `Thm23, `Thm4, `R1Merge, `R2Parts, `R2Abstract, `R2Mem, `R3Loop]
