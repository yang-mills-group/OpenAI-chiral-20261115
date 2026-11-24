import YM.CF.Hove.Out
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Hove
open Function Filter Metric Fir Lattice Laurent Next.Free Bloch Finset Lat Stationary Rush Cube Scroll SU Drapes Fir Peaks Dial Paige Brace Vault Fock Tulip Font Spire Nacre Ember Pec
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix Matrix.Norms.L2Operator Kronecker MatrixOrder Classical
attribute [local instance] opCStarAlgebra
open Tap Hake Urn Yaw Levier Proa Rill

variable {ι:Type*}[Fintype ι] -- drop
variable (U W:ι→ℝ)(a b a' b':ι→ℂ)
def dishV (a b:ι→ℂ)(i:ι×ι):ℂ:=star (a i.1)*b i.2
lemma dish_l:dishV (a+a') b= dishV a b+dishV a' b:=by ext x:1; simp [dishV,add_mul]
lemma dish_r:dishV a (b+b')= dishV a b+dishV a b':=by ext x:1; simp [dishV,mul_add]
lemma dish_u (t:ℂ): dishV (t • a) b= star t • dishV a b:=by ext x:1; simp [dishV, mul_assoc]
lemma dish_v(t:ℂ): dishV a (t • b)= t • dishV a b:=by ext x:1; simp [dishV, mul_left_comm]
lemma dish₀L: dishV (0:ι→ℂ) b=0:=by ext; simp [dishV]
lemma dish₀R: dishV a (0:ι→ℂ)=0:=by ext; simp [dishV]
lemma dishSL{J:Type*}[DecidableEq J](S:Finset J)(A:J→ι→ℂ): dishV (∑ i∈S,A i) b=∑ i∈S,dishV (A i) b:=by induction S using Finset.induction with | empty=> simp [dish₀L] | insert _ _ e ih=> simp [e,ih,dish_l]
lemma dishSR{J:Type*}[DecidableEq J](S:Finset J)(A:J→ι→ℂ): dishV a (∑ i∈S,A i)=∑ i∈S,dishV a (A i):=by induction S using Finset.induction with | empty=> simp [dish₀R] | insert _ _ e ih=> simp [e,ih,dish_r]
def coyF (w:ι→ℝ)(i:ι×ι):ℝ:=w i.1+w i.2
def coilF (w u:ι→ℝ)(i:ι×ι):ℝ:=w i.1*u i.2
lemma dish_p: paidX (coilF U W) (dishV a b) = paidX U a * paidX W b:=by
 unfold paidX; rw [Fintype.sum_prod_type,sum_mul]; apply Finset.sum_congr rfl; intro i _; rw [mul_sum]; apply sum_congr rfl; intro j _; unfold coilF dishV; simp only [norm_mul,norm_star]; ring
lemma coy_p(z:ι×ι):coyF U z = coilF U 1 z+coilF 1 U z:=by simp [coyF,coilF]
lemma fork_p(Q:ι×ι→ℂ): paidX (coyF U) Q=paidX (coilF U 1) Q+paidX (coilF 1 U) Q:=by unfold paidX; simp_rw [coy_p, add_mul]; rw [sum_add_distrib]
end YM.CF.Hove
