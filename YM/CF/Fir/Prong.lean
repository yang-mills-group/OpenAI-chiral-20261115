import YM.CF.Fir.Side
/-! Open ends, filled alias correction even at zero. Inverses are of the high-mode folding, not of physical overlap. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.Fir
open Function Filter Lattice Laurent Bloch Next.Free Metric Finset Set WilsonFrame
open scoped Topology Matrix BigOperators Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra

def angle (u:Bool) : Op SpinIdx:= if u then Aop else 1-Aop
def bent (u:Bool)(j:ℕ)(N:Side)(p:Momentum) : Op SpinIdx := if u then bar j N p else 1-bar j N p
lemma zenAngle (u:Bool)(p:Momentum): zen p * angle u=(1-angle u)*zen p:=by cases u <;> simp [angle,zenAA,zenA]
lemma aspect (u:Bool)(j N){p:Momentum}(hp:p∈realCube zone): angle u * bent u j N p = shell j N p • (angle u*(1+zen (mixL j N p))):=by cases u; exact (bar_side j N hp).2; exact (bar_side j N hp).1
lemma aspTrace (u:Bool)(j N)(h:Odd N.val){p:Momentum}(hp:p∈realCube zone)(hx:p≠0): bent u j N p = shell j N p • ((1-zen (mixL j N p))*angle u*(1+zen (mixL j N p))):=by
  have he:=bar_full j N hp hx (graphs_ne (phys_mix j N h _ hp.1)); cases u; exact he.2; exact he.1
variable (u:Bool) (j:ℕ)(L M:Side)(p:Momentum)
lemma nChip : narrow M (narrow L p)=narrow (L*M) p:=by simp only [narrow,smul_smul, mul_side_complex, mul_inv,mul_comm (_⁻¹ : ℂ) (_⁻¹ : ℂ)] -- inspect
lemma eChip: (L.val:ℂ) • ds M (narrow L p)=ds (L*M) p:=by rw [ds, ds, nChip, mul_side_complex,smul_smul]
lemma bChip: (L.val:ℂ)^2*D M (narrow L p)=D (L*M) p:=by rw [D,D,nChip,mul_side_complex]; ring
lemma zChip: ((L.val:ℂ)*bloom j M (narrow L p)*(D (L*M) p)⁻¹) • zen (ds (L*M) p)= (bloom j M (narrow L p)*(D M (narrow L p))⁻¹) • zen (ds M (narrow L p)):=by rw [← bChip,← eChip,zenS,smul_smul]; congr 1; rw [mul_inv,← inv_pow]; field_simp -- D ne
include u j in
lemma foray (hp:p∈realCube zone)(hx:p≠0):
   zen (ds M p)*angle u*bent u j M p = (shell j M p) • (zen (ds M p)*angle u*(1+zen (extras j M p))- (bloom j M p*Cminus M p) • (1-angle u)):=by
  let F:= mass j M p; let k:=D M p; let A:=angle u; let Z:=zen (ds M p); let H:=zen (extras j M p); let s:=bloom j M p
  have he:k≠0:=by intro h; have hx:= noGhost M hp hx; change 0<k.re at hx; rw [h] at hx; exact lt_irrefl 0 hx
  rw [mul_assoc,aspect _ _ _ hp,mix_com,zenP,zenS]
  change Z*(shell j M p • (A*(1+(H+(s*k⁻¹) • Z))))=_
  have hh : Z*A*Z= -(k*Cminus M p) • ((1:Op SpinIdx)-A):=by
    have hb: prodM (ds M p) (ds M p)=k*Cminus M p:=by simpa only [sq, prodM] using ds_sq M p
    rw [show Z*A=(1-A)*Z from zenAngle ..,mul_assoc,show Z*Z=_ from zenSq _,hb,Matrix.mul_smul,mul_one]
  rw [Matrix.mul_smul,← mul_assoc Z A,← add_assoc,mul_add, Matrix.mul_smul, hh, smul_smul]; congr 1
  rw [show s*k⁻¹ * -(k*Cminus M p)= -(s*Cminus M p) by field_simp]; module -- inspect

/-- alias arm before spline factor -/
def ray (l:Site L): Op SpinIdx := (1-zen (mixL j M (aliasAt p l))) * angle u * bent u j (L*M) p
/-- analytic formula at fundamental patch -/
def chief : Op SpinIdx:= (1-zen (extras j M (narrow L p)))*angle u * bent u j (L*M) p -
 ( (L.val:ℂ)*bloom j M (narrow L p)*(mass j (L*M) p)⁻¹ ) • (zen (ds (L*M) p)*angle u*(1+zen (extras j (L*M) p))-(bloom j (L*M) p*Cminus (L*M) p) • (1-angle u))
lemma chief_eq (hp:p∈realCube zone)(hx:p≠0): chief u j L M p=ray u j L M p 0:=by
  have hk:D (L*M) p≠0:=by intro h; have he:=noGhost (L*M) hp hx; rw [h] at he; exact lt_irrefl 0 he
  rw [ray,alias_zero_eq,mix_com,zenP,zenS,← zChip]
  let k:=D (L*M) p
  rw [← sub_sub,sub_mul,sub_mul,Matrix.smul_mul, Matrix.smul_mul,foray u j (L*M) p hp hx,smul_smul,shell]; unfold chief
  rw [show (L.val:ℂ)*bloom j M (narrow L p)* (D (L*M) p)⁻¹ * (D (L*M) p/mass j (L*M) p)=(L.val:ℂ)*bloom j M (narrow L p)*(mass j (L*M) p)⁻¹ by rw [div_eq_mul_inv]; ring_nf; field_simp]; -- check occurrences
end YM.CF.Fir
