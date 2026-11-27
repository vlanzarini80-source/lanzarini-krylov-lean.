
from pathlib import Path
import hashlib
import sympy as sp

SOURCE = Path(
    "P85_4_PhysicalInitialJetEvaluation.lean"
)

original = SOURCE.read_text(encoding="utf-8")

print(
    "ORIGINAL_SHA256:",
    hashlib.sha256(original.encode()).hexdigest(),
    flush=True
)

p, q, r, d, e, f = sp.symbols(
    "p q r d e f", real=True
)

H = sp.Matrix([
    [0, p, 0, 0],
    [p, d, q, 0],
    [0, q, e, r],
    [0, 0, r, f]
])

A = -sp.I * H

# Generate physical state jets.
# No deficit coefficients are supplied.

jets = [sp.Matrix([1, 0, 0, 0])]

for k in range(1, 10):
    jets.append(
        (A * jets[-1]).applyfunc(sp.expand)
    )

    print(
        f"STATE_JET_GENERATED: {k}",
        flush=True
    )


def lean_real(x):

    x = sp.expand(x)

    if x.is_Integer or x.is_Symbol:
        return str(x)

    if x.is_Add:
        return "(" + " + ".join(
            lean_real(a) for a in x.args
        ) + ")"

    if x.is_Mul:
        return "(" + " * ".join(
            lean_real(a) for a in x.args
        ) + ")"

    if x.is_Pow:
        b, n = x.args

        if not n.is_Integer or n < 0:
            raise ValueError(x)

        return (
            "(" + lean_real(b)
            + " ^ " + str(n) + ")"
        )

    raise ValueError(
        f"Unsupported expression: {x}"
    )


def lean_complex(x):

    re = lean_real(sp.re(x))
    im = lean_real(sp.im(x))

    return (
        f"(({re} : ℝ) : ℂ) + "
        f"(({im} : ℝ) : ℂ) * Complex.I"
    )


lemmas = []
audit_names = []
state_names = []
prob_names = []
moment_names = []

for k, z in enumerate(jets):

    name = f"p85_4_cached_state_{k}"

    state_names.append(name)
    audit_names.append(name)

    vector = ",\n    ".join(
        lean_complex(x) for x in z
    )

    if k == 0:

        proof = """
  ext i
  fin_cases i <;>
    simp [p85_4_stateJet, p81_e0]
"""

    else:

        proof = f"""
  rw [p85_4_stateJet]
  rw [p85_4_cached_state_{k-1}]
  rw [p85_4_generator_action]
  ext i
  fin_cases i <;>
    apply Complex.ext <;>
    simp [
      Complex.add_re,
      Complex.add_im,
      Complex.mul_re,
      Complex.mul_im,
      Complex.neg_re,
      Complex.neg_im
    ] <;> ring
"""

    lemmas.append(f"""
theorem {name}
    (p q r d e f : ℝ) :
    p85_4_stateJet p q r d e f {k} =
    ![
    {vector}
    ] := by
{proof}

#print axioms {name}
""")

# Generate probability derivatives
# from the exact Leibniz formula.

prob = {}

state_rules = ",\n      ".join(
    state_names
)

for k in range(10):

    for j in range(4):

        value = sp.expand(sum(
            sp.binomial(k, l)
            * sp.conjugate(jets[l][j])
            * jets[k-l][j]
            for l in range(k+1)
        ))

        value = sp.expand(sp.re(value))

        prob[j, k] = value

        name = f"p85_4_cached_prob_{j}_{k}"

        prob_names.append(name)
        audit_names.append(name)

        lemmas.append(f"""
theorem {name}
    (p q r d e f : ℝ) :
    p85_4_probabilityJet
      p q r d e f ({j} : Fin 4) {k} =
    {lean_real(value)} := by

  simp [
    p85_4_probabilityJet,
    p85_4_complexPair,
    {state_rules},
    Complex.add_re,
    Complex.add_im,
    Complex.mul_re,
    Complex.mul_im
  ] <;> ring

#print axioms {name}
""")

    print(
        f"PROBABILITY_ORDER_GENERATED: {k}",
        flush=True
    )

# Generate normalized moment derivatives.

for k in range(10):

    rules = ",\n      ".join(
        f"p85_4_cached_prob_{j}_{k}"
        for j in range(4)
    )

    for label, power in [
        ("K", 1),
        ("M2", 2)
    ]:

        value = sp.expand(sum(
            j**power * prob[j, k]
            for j in range(4)
        ))

        name = f"p85_4_cached_{label}_{k}"

        moment_names.append(name)
        audit_names.append(name)

        lemmas.append(f"""
theorem {name}
    (p q r d e f : ℝ) :
    p85_4_{label} p q r d e f {k} =
    {lean_real(value)} := by

  simp [
    p85_4_{label},
    Fin.sum_univ_succ,
    {rules}
  ] <;> ring

#print axioms {name}
""")

    print(
        f"MOMENT_ORDER_GENERATED: {k}",
        flush=True
    )

# Replace only the inefficient evaluator.
# Preserve all original theorem statements.

start_marker = 'macro "p85_eval" : tactic =>'

end_marker = (
    "/-- Initial variance coefficient. -/"
)

if original.count(start_marker) != 1:
    raise SystemExit(
        "ORIGINAL_MACRO_NOT_UNIQUE"
    )

if original.count(end_marker) != 1:
    raise SystemExit(
        "ORIGINAL_THEOREM_BOUNDARY_NOT_UNIQUE"
    )

start = original.index(start_marker)
end = original.index(end_marker, start)

moment_rules = ",\n      ".join(
    moment_names
)

macro = f"""
macro "p85_eval" : tactic =>
  `(tactic|
    (simp [
      p85_4_F,
      p85_4_V,
      p85_4_realPair,
      {moment_rules}
    ] <;> ring))

"""

optimized = (
    original[:start]
    + "\n".join(lemmas)
    + "\n"
    + macro
    + original[end:]
)

# Bound each theorem's elaboration budget.

optimized = optimized.replace(
    "set_option maxHeartbeats 20000000",
    "set_option maxHeartbeats 1000000"
)

# Verify that all original theorem names remain.

import re

old_names = set(re.findall(
    r"(?m)^theorem\s+(\w+)",
    original
))

new_names = set(re.findall(
    r"(?m)^theorem\s+(\w+)",
    optimized
))

if not old_names.issubset(new_names):
    raise SystemExit(
        "ORIGINAL_THEOREM_REMOVED"
    )

SOURCE.write_text(
    optimized,
    encoding="utf-8"
)

Path("p85-4-generated-theorems.txt").write_text(
    "\n".join(
        "Lanzarini." + name
        for name in audit_names
    ) + "\n",
    encoding="utf-8"
)

print(
    "ORIGINAL_THEOREMS_PRESERVED:",
    len(old_names),
    flush=True
)

print(
    "GENERATED_INTERMEDIATE_THEOREMS:",
    len(audit_names),
    flush=True
)

print(
    "OPTIMIZED_SHA256:",
    hashlib.sha256(
        SOURCE.read_bytes()
    ).hexdigest(),
    flush=True
)

print(
    "P85_4_OPT_GENERATION_COMPLETE",
    flush=True
)

print(
    "LEAN_VERIFICATION_PENDING",
    flush=True
)
