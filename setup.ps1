# Run in PowerShell from the repo folder, after installing elan + git.
# 1) use the same Lean version as current Mathlib
Invoke-WebRequest https://raw.githubusercontent.com/leanprover-community/mathlib4/master/lean-toolchain -OutFile lean-toolchain
# 2) fetch Mathlib and its prebuilt cache, then build
lake update
lake exe cache get
lake build
