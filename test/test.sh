#!/usr/bin/env bash
set -euo pipefail

# define your command once, including the no-prelude flag
# the first “--” is for dune exec, the second “--” is for neon itself
NEON_CMD="dune exec -- neon -no-prelude"

# good fixtures must exit 0
pwd

for f in ok/*.neon; do
  echo "✅ OK-fixture: $f"
  $NEON_CMD "$f"
done

# bad fixtures must exit non-zero
for f in error/*.neon; do
  echo "⚠️  ERROR-fixture: $f"
  if $NEON_CMD "$f"; then
    echo "    ✗ Expected failure but got success on $f" >&2
    exit 1
  fi
done

echo "🎉  All fixtures behaved as expected!"