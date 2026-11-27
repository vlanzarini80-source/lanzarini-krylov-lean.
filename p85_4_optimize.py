from pathlib import Path
import hashlib
import math
import re
import sympy as sp

source = Path('P85_4_PhysicalInitialJetEvaluation.lean')
original = source.read_text(encoding='utf-8')
p,q,r,d,e,f = sp.symbols('p q r d e f', real=True)
H = sp.Matrix([[0,p,0,0],[p,d,q,0],[0,q,e,r],[0,0,r,f]])
x = [sp.Matrix([1,0,0,0])]
for k in range(1,10):
    x.append((H*x[-1]).applyfunc(sp.expand))
z = [v*(-sp.I)**k for k,v in enumerate(x)]
def real(v):
    return str(sp.expand(v)).replace('**','^')
def cx(v):
    return f'⟨{real(sp.re(v))}, {real(sp.im(v))}⟩'
args='p q r d e f'
params='(p q r d e f : ℝ)'
blocks=[]
names=[]
def add(name, statement, proof):
    names.append(name)
    blocks.append(f'theorem {name} {params} :\n  {statement} := by\n{proof}\n\n#print axioms {name}\n')
# Explicit real/imaginary projections; never simplify complex powers.
projection='Matrix.cons_val_zero, Matrix.cons_val_succ, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.neg_re, Complex.neg_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im'
for k in range(10):
    name=f'p85_4_cached_state_{k}'
    vec='!['+', '.join(cx(v) for v in z[k])+']'
    if k==0:
        proof='  ext i\n  fin_cases i <;> apply Complex.ext <;> simp [p85_4_stateJet, p81_e0]'
    else:
        proof=f'''  rw [p85_4_stateJet, p85_4_cached_state_{k-1}, p85_4_generator_action]
  ext i
  fin_cases i <;> apply Complex.ext <;>
    simp only [{projection}] <;> ring'''
    add(name,f'p85_4_stateJet {args} {k} = {vec}',proof)
# Prove a finite Leibniz identity once per order, with abstract inputs.
# No physical coefficient appears in these identities.
for k in range(10):
    terms=' + '.join(f'({math.comb(k,l)} : ℝ) * ((X {l}).re * (Y {k-l}).re + (X {l}).im * (Y {k-l}).im)' for l in range(k+1))
    blocks.append(f'''theorem p85_4_opt_pair_{k} (X Y : ℕ → ℂ) :
  (p85_4_complexPair X Y {k} 0 0).re = {terms} := by
  simp [p85_4_complexPair, Complex.add_re, Complex.mul_re] <;> ring
#print axioms p85_4_opt_pair_{k}
''')
prob={}
for k in range(10):
    for j in range(4):
        value=sp.expand(sp.re(sum(math.comb(k,l)*sp.conjugate(z[l][j])*z[k-l][j] for l in range(k+1))))
        prob[j,k]=value
        rules=', '.join(f'p85_4_cached_state_{l}' for l in range(k+1))
        add(f'p85_4_cached_prob_{j}_{k}',f'p85_4_probabilityJet {args} ({j} : Fin 4) {k} = {real(value)}',f'''  unfold p85_4_probabilityJet
  rw [p85_4_opt_pair_{k}]
  simp only [{rules}, Matrix.cons_val_zero, Matrix.cons_val_succ] <;> ring''')
for k in range(10):
    rules=', '.join(f'p85_4_cached_prob_{j}_{k}' for j in range(4))
    for label,power in [('K',1),('M2',2)]:
        value=sum(j**power*prob[j,k] for j in range(4))
        add(f'p85_4_cached_{label}_{k}',f'p85_4_{label} {args} {k} = {real(value)}',f'  simp [p85_4_{label}, Fin.sum_univ_succ, {rules}] <;> ring')
for k in range(9):
    terms=' + '.join(f'({math.comb(k,l)} : ℝ) * X {l} * Y {k-l}' for l in range(k+1))
    blocks.append(f'''theorem p85_4_opt_real_pair_{k} (X Y : ℕ → ℝ) :
  p85_4_realPair X Y {k} 0 0 = {terms} := by
  simp [p85_4_realPair] <;> ring
#print axioms p85_4_opt_real_pair_{k}
''')
rules=', '.join([f'p85_4_opt_real_pair_{k}' for k in range(9)]+[n for n in names if '_cached_K_' in n or '_cached_M2_' in n])
macro=f'''macro "p85_eval" : tactic =>
  `(tactic| (simp [p85_4_F, p85_4_V, {rules}] <;> ring))

'''
a=original.index('macro "p85_eval" : tactic =>')
b=original.index('/-- Initial variance coefficient. -/',a)
optimized=original[:a]+'\n'.join(blocks)+macro+original[b:]
optimized=optimized.replace('set_option maxHeartbeats 20000000','set_option maxHeartbeats 1000000\nset_option linter.unusedSimpArgs false')
assert len(names)==70
assert set(re.findall(r'(?m)^theorem\s+(\w+)',original)).issubset(set(re.findall(r'(?m)^theorem\s+(\w+)',optimized)))
source.write_text(optimized,encoding='utf-8')
Path('p85-4-generated-theorems.txt').write_text('\n'.join('Lanzarini.'+n for n in names)+'\n')
print('OPT2_SOURCE_SHA256:',hashlib.sha256(source.read_bytes()).hexdigest(),flush=True)
print('P85_4_OPT_GENERATION_COMPLETE',flush=True)
print('LEAN_VERIFICATION_PENDING',flush=True)
