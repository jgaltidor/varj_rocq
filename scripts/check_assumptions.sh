#!/bin/sh
# Fail if any lemma depends on an assumption outside the known list below.
# Run after `make`, from the repository root, where `rocq` is available.
set -eu

# Global parameters of the calculus, plus the lemmas still left Admitted.
ALLOWED="this Object CT classTableOK weakening_subtyping context_movement"

files=$(grep -E '^[A-Za-z_]+\.v$' _CoqProject)
tmp=$(mktemp -d)
trap 'rm -rf "$tmp"' EXIT

{
  for f in $files; do echo "From VarJ Require ${f%.v}."; done
  for f in $files; do
    grep -oE '^[[:space:]]*(Lemma|Theorem|Fact|Corollary|Remark|Proposition|Example)[[:space:]]+[A-Za-z0-9_'"'"']+' "$f" |
      awk -v m="${f%.v}" '{ print "Print Assumptions VarJ." m "." $2 "." }'
  done
} > "$tmp/Assumptions.v"

rocq c -Q . VarJ "$tmp/Assumptions.v" > "$tmp/out.txt"

used=$(grep -oE "^[A-Za-z_][A-Za-z0-9_'.]* :" "$tmp/out.txt" | sed -e 's/ :$//' -e 's/.*\.//' | sort -u)
bad=""
for a in $used; do
  case " $ALLOWED " in *" $a "*) ;; *) bad="$bad $a" ;; esac
done

checked=$(grep -c '^Print Assumptions' "$tmp/Assumptions.v")
if [ -n "$bad" ]; then
  echo "Unexpected assumptions:$bad"
  echo "(Prove them, or add them to ALLOWED in $0 if intended.)"
  exit 1
fi
echo "Checked $checked lemmas; assumptions used: $(echo $used)"
