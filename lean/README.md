# Lean project

This project contains deterministic semantic checkers for the autoformalization benchmark.

## Build
```bash
lake exe cache get
lake build
```

## Structure
- `AutoformalizationEval/Checks.lean`: shape guard + checker dispatch
- `AutoformalizationEval/Families/*.lean`: family-specific checkers
- `AutoformalizationEval/Template/*.template`: rendered files for Test1/Test2
