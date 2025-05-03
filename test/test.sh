#!/usr/bin/env bash
set -u pipefail

# ANSI color codes
GREEN="\e[32m"
RED="\e[31m"
YELLOW="\e[33m"
BLUE="\e[34m"
RESET="\e[0m"

NEON_CMD="dune exec -- neon -no-prelude"

echo -e "\n${BLUE}🌟 Starting Neon CLI test suite${RESET}\n"

total=0
passed=0
failures=()

run_fixture () {
  local should_succeed=$1
  local file=$2
  (( total++ ))
  # capture output
  out=$($NEON_CMD "$file" 2>&1)
  code=$?

  if [ $should_succeed -eq 1 ] && [ $code -eq 0 ]; then
    (( passed++ ))
    echo -e "\t${GREEN}✅ OK${RESET}        $file"
  elif [ $should_succeed -eq 0 ] && [ $code -ne 0 ]; then
    (( passed++ ))
    echo -e "\t${GREEN}✅ ERR${RESET}       $file"
  else
    echo -e "\t${RED}❌ FAIL${RESET}      $file"
    failures+=("$file|$code|$out")
  fi
}

echo -e "${YELLOW}→ Running OK‐fixtures (must exit 0)${RESET}"
for f in ok/*.neon; do
  run_fixture 1 "$f"
done

echo ""
echo -e "${YELLOW}→ Running ERROR‐fixtures (must exit non-zero)${RESET}"
for f in error/*.neon; do
  run_fixture 0 "$f"
done

echo ""
echo -e "${BLUE}===== Summary: $passed/$total passed =====${RESET}"

if [ ${#failures[@]} -ne 0 ]; then
  echo -e "\n${RED}❗ ${#failures[@]} failure(s) detail:${RESET}\n"
  for record in "${failures[@]}"; do
    IFS="|" read -r file code out <<< "$record"
    echo -e "${RED}── Failure:${RESET} $file exited with code $code"
    echo -e "\t${YELLOW}Output:${RESET}"
    while IFS= read -r line; do
      echo -e "\t  $line"
    done <<< "$out"
    echo ""
  done
else
  echo -e "${GREEN}🎉 All fixtures behaved as expected!${RESET}"
fi

exit 0