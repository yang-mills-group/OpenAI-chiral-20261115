import YM.CF.Moto.Rune
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
noncomputable section
namespace YM.CF.Moto
open Function Filter Metric Fir Lattice Laurent Next.Free Bloch Finset Lat Stationary Rush Cube Scroll SU Drapes Fir Peaks Dial Paige Brace Vault Fock Tulip Font Spire Nacre Ember Pec
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix Matrix.Norms.L2Operator Kronecker MatrixOrder Classical
attribute [local instance] opCStarAlgebra
open Tap Hake Urn Yaw Levier Proa Rill
open Hove Haro
variable {n:Side}(o x y:Site n)(a b:Pal)(S T:Matrix (Single n) Kt ℂ)(P:Op (Single n))(k:ℕ)(g:SU.E)(r:Bool)(i:Axis)
open Skye Precision Jet Scree
variable(X:Hub n)(F:InkD n){B:RG.BudgetPoint}{h v:ℝ}(p:PressB B X F h v)
variable (Q:Finset (Dwell n)→ℝ)(hp:∀ i,0 ≤ Q i)(pT:X.val.1=node o)
local notation "V_"=> orbitPH (F 1)
local notation "nκ"=> B.power
local notation "Pp"=> B
local notation "ΘP"=> paid_M o V_ B.power
variable (p1:∀ i j:Single n, ‖orbitPH (F 1) i j‖≤ Q (Haro.tray i j))(hx:0 ≤ h)
include p1 pT hp hx
local notation "KΦ"=> joinV
lemma pinM(T:ℝ)(p: (∑ i:Finset (Dwell n), Scree.tariff B (X.val.1) h i * Q i)≤ T):ΘP*h^2 ≤2*T:=by
 have hL:0≤ B.power:=by omega
 let Z:= Q; let A:= Scree.tariff B (X.val.1) h; let W(i:Finset (Dwell n)):= A i*Q i; let M(i:Single n):=nook_T o B.power i; have hv(i):0≤ W i:=mul_nonneg (by unfold A Scree.tariff; positivity) (hp _)
 have he(i j:Single n) : (M i+M j)*‖V_ i j‖*h^2 ≤ 2*W (Haro.tray i j):=by
    have hz(t a: Single n): M t ≤ amt nκ (node o) t.1 a.1:=by unfold M nook_T amt; gcongr; exact le_max_left ..
    have hT:amt nκ (node o) j.1 i.1=amt nκ (node o) i.1 j.1:=by unfold amt; rw [max_comm]
    let v:= amt nκ (node o) i.1 j.1; have hm:M i + M j ≤ 2*v:= (add_le_add (hz _ _) ((hz j i).trans_eq hT)).trans_eq (two_mul v).symm
    refine (mul_le_mul_of_nonneg_right (mul_le_mul hm (p1 i j) (norm_nonneg _) (show 0≤2*v from (by unfold v amt; positivity))) (sq_nonneg _)).trans_eq ?_; unfold W A; rw [pT,rope nκ (node o) i.1 j.1 i.2 j.2 h B rfl]; unfold v; ring -- tuning exact terms
 unfold paid_M paidX; refine le_trans ?_ (mul_le_mul_of_nonneg_left p (by norm_num))
 let I:= univ.image (fun i:Single n ×Single n=> tray i.1 i.2); rw [sum_mul, mul_sum]; refine le_trans ?_ (sum_le_sum_of_subset_of_nonneg (s:=I) (f:=fun i =>2*W i) (subset_univ _) (fun i _ _=>mul_nonneg (by norm_num) (hv i))); unfold I; rw [sum_image (Haro.tray_in).injOn]; exact sum_le_sum fun z _=> he z.1 z.2
end YM.CF.Moto
