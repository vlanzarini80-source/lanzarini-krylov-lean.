
name: P83 Local Fourth Bridge

on:
  push:
    branches:
      - research/p75-centered-derivative
  workflow_dispatch:

jobs:
  verify:
    runs-on: ubuntu-latest

    steps:
      - name: Checkout
        uses: actions/checkout@v4

      - name: Install Lean
        run: |
          set -euo pipefail
          curl -sSf https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh | sh -s -- -y --default-toolchain none
          echo "$HOME/.elan/bin" >> "$GITHUB_PATH"

      - name: Fetch mathlib
        run: |
          set -euo pipefail
          lake update
          lake exe cache get

      - name: Compile local fourth bridge
        run: |
          set -euo pipefail
          LEAN_PATH=".:${LEAN_PATH:-}" lake env lean \
            P83_LocalFourthBridge_Probe.lean \
            2>&1 | tee p83-local-fourth.log

      - name: Audit theorem axioms
        run: |
          set -euo pipefail

          python3 - <<'PY'
          from pathlib import Path
          import re

          source = Path(
              "P83_LocalFourthBridge_Probe.lean"
          ).read_text()

          log = Path(
              "p83-local-fourth.log"
          ).read_text()

          source = re.sub(
              r"/-.*?-/", "", source, flags=re.S
          )
          source = re.sub(
              r"--[^\n]*", "", source
          )

          assert not re.search(
              r"\b(sorry|admit|axiom|sorryAx)\b",
              source
          ), "Forbidden proof token"

          name = "p83_local_product_smoothness"

          assert len(re.findall(
              r"\btheorem\s+" + name + r"\b",
              source
          )) == 1

          assert source.count(
              "#print axioms " + name
          ) == 1

          prefix = (
              "'Lanzarini." + name +
              "' depends on axioms:"
          )

          reports = [
              line.strip()
              for line in log.splitlines()
              if line.strip().startswith(prefix)
          ]

          assert len(reports) == 1, (
              "Missing axiom report"
          )

          payload = reports[0][len(prefix):].strip()

          assert (
              payload.startswith("[")
              and payload.endswith("]")
          )

          found = {
              x.strip()
              for x in payload[1:-1].split(",")
              if x.strip()
          }

          allowed = {
              "propext",
              "Classical.choice",
              "Quot.sound",
          }

          assert found <= allowed, (
              f"Unexpected axioms: {found - allowed}"
          )

          print("PASS: local product smoothness")
          print("Axioms:", sorted(found))
          PY
