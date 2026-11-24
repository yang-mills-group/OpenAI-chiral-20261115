import YM.CF.BProof.Solar.Cast
import YM.CF.BProof.Solar.Local
import YM.CF.BProof.Fog.Fro
set_option autoImplicit false
noncomputable section
set_option synthInstance.maxSize 28000
namespace YM.CF.BProof.Bide
open Function Filter Metric NormedSpace Finset Fock Lattice Wilson Laurent Lat Rush SU Drapes Fir Peaks Dial Paige Brace Vault Tulip Tenant Phase Broc Matrix Scroll Thera Branch Laic Cube
open scoped Matrix.Norms.L2Operator Matrix Topology ContDiff MatrixOrder BigOperators InnerProductSpace Kronecker
attribute [local instance] opCStarAlgebra
open Urn Hake Levier Spire Scree Stilo Hive
attribute [local instance] opCStarAlgebra
open MeasureTheory Skye


variable {N:Side} (s t:Sweep N)
namespace Chalk
open RG Law Window.Unfit
open scoped ComplexOrder
variable {R:Support (More N)}{F G:Obs N}{K C:ℝ} (i:Axis)
attribute [local instance] BProof.Bide.mCast BProof.Bide.bCast
variable {X:Orbit N→Phys N}
lemma lit_right (e: Envelope X)(h:∀ F:Obs N, Allowed R F→ Continuous F→ 0≤ Fixed.functional X (un i F))(u:Allowed R F): 0≤Fixed.functional X (un i F):=by
 let B: Set ℂ:=Set.Ici 0; have hb:IsClosed B:=(isClosed_le (continuous_const (y:=(0:ℝ))) Complex.continuous_re).inter (isClosed_eq (continuous_const (y:=(0:ℝ))) Complex.continuous_im)
 change Fixed.functional X _∈ B; rw [←hb.closure_eq]
 apply Metric.mem_closure_iff.mpr; intro ε hε; obtain ⟨v,p⟩:=e.cost; obtain ⟨z,k⟩:= u.bounded.cost; let C:=max 1 z; let K:=max 1 v; have hk:0<C:= zero_lt_one.trans_le (le_max_left ..); have hK:0<K:=zero_lt_one.trans_le (le_max_left ..)
 have hf:Paid F C:=fun i=> (k i).trans (le_max_right ..); let a:=2*C*K; have ha:0<a:=by unfold a; positivity
 obtain ⟨G,v,g,p',u'⟩:= probe u (div_pos (half_pos hε) ha) hk hf
 refine ⟨Fixed.functional X (un i G),h G g v,?_⟩; rw [dist_eq_norm]; refine (price i e hK (fun i=>(p i).trans (le_max_right ..)) hk.le u.bounded g.bounded hf p').trans_lt ?_; refine (mul_le_mul_of_nonneg_left u' ha.le).trans_lt ?_; change a * (ε/2/a) < ε; rw [mul_comm,div_mul_cancel₀] -- lemma name; tune
 linarith
 positivity
end Chalk
end YM.CF.BProof.Bide
