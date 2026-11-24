import YM.CF.Milo.Seed
import YM.Extra.ITERATION_NO_LOSS.Sums
import YM.CF.Milo.Leg
import YM.CF.Sour.Rate
import YM.CF.Sour.Millet
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Sour
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open Skye Scree Cadre Palot
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
open Cube Lat Tulip Fock Rush Scroll Paige Vault Phase Acorn Spire
open Pastry Vow Rue
attribute [local instance] opCStarAlgebra
variable {n:Side}
local notation "SA"=> Seat n
local notation "VX"=> Aura n
local notation "Hk"=> hook SA
open Hake Jet Sault Stax
attribute [local instance] loreM loreN
variable {P:BudgetPoint}{X Y Z:Aura n}{V W:Firing n}{D:Support (More n)}
open Branch Tenant Drapes Rill Sault
attribute [local instance] Rill.boreKSpace Rill.boreXN
local notation "JS"=> Single n
local notation "SO"=> Support (More n)
local notation "Γ"=> (FC (Dwell n))
open Push.AbsoluteSums Nor Tenant
variable (P:BudgetPoint)(S:Support (More n))
abbrev coinK(o k:ℕ):= k*(o+1)
def gown(o k:ℕ):ℝ:= (Nat.factorial o:ℝ)^2 *2^o * ((100*(Fief.tileN 0:ℝ))^k)^(o+1)
open ConnectedActivityE6.Raw
lemma fare_b (U:Grove (terr (More n)) S): surgeL P S 1≤(100*(Fief.tileN 0:ℝ))^P.power * (S.card+1:ℝ)^P.power:=by
 let V:=atOne (More n); have he:=Fief.surgeK V S 1 0 U one_pos; rw [show (V.count.val:ℕ)=1 from rfl, show S.image V.parent=S from (by rw [show V.parent=id from funext fun x=>parent_one x,image_id]),zero_mul] at he
 have hX:coverNumber 1 S ≤ coverNumber 1 (halo 0 S):= Corona.cover_mono (halo_subset 0 _) _
 rw [←mul_pow]; unfold surgeL; norm_num; push_cast; gcongr; norm_num [V,Fief.tileN] at *; exact_mod_cast (by omega) -- tune
lemma moneyP (U:Grove (terr (More n)) S): Vow.fareX 1 P S ≤ gown P.order P.power*(S.card+1:ℝ)^coinK P.order P.power:=by
 let A:=surgeL P S 1; let B:=(100*(Fief.tileN 0:ℝ))^P.power; let V:=(S.card+1:ℝ); let n:=P.order
 have hx:A ≤ B*V^P.power:=fare_b P S U; have ht:A≥1:=by unfold A surgeL; apply one_le_pow₀; apply le_add_of_nonneg_right; positivity
 have h0:0 ≤ A:= by linarith
 have hf:A*(1+A)^n ≤ 2^n * (B^(n+1) * (V^(P.power*(n+1)))):=by
    calc
      _ ≤ A*(2*A)^n:=by gcongr; linarith
      _ = 2^n*A^(n+1):=by rw [pow_succ,mul_pow]; ring
      _ ≤ 2^n*(B*V^P.power)^(n+1):=by gcongr
      _ = _:=by rw [mul_pow,pow_mul]
 let F:ℝ:=n.factorial
 calc
    _ = F^2*(A*(1+A)^n):=by unfold F fareX Nor.liftR Jet.composeCost n A; ring
    _ ≤ _:=mul_le_mul_of_nonneg_left hf (sq_nonneg _)
    _ = gown P.order P.power*(S.card+1:ℝ)^coinK P.order P.power:=by unfold gown F B coinK; unfold n V; ring
variable (a:ℝ)(p:0<a)(h:a≤1)
abbrev fernL(n:ℕ):ℝ:=4^n*Real.exp 1*n.factorial
local notation "Dv"=> a/4
include p h
lemma task(v:ℕ)(j:ℕ): Real.exp (-a/2*j)*(j+1:ℝ)^v ≤ fernL v * (a⁻¹)^v * Real.exp (-a/4*j) :=by
 have ht:0 < a/4:= div_pos p (by positivity); have hv:Real.exp (a/4)≤Real.exp 1:=Real.exp_le_exp.mpr (by linarith)
 have hk:Extra.Iteration.momentPrice v Dv ≤ fernL v * (a⁻¹)^v:=by unfold Extra.Iteration.momentPrice fernL; rw [div_eq_mul_inv,div_pow,inv_div]; apply le_trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hv (Nat.cast_nonneg _)) (show (0:ℝ)≤4^v/a^v from by positivity)); exact le_of_eq (by rw [inv_pow]; ring)
 have hu:(j+1:ℝ)^v≤ (fernL v*(a⁻¹)^v)*Real.exp (a/4*j):=by rw [add_comm]; exact (Extra.Iteration.spendMoment _ ht (Nat.cast_nonneg _)).trans (mul_le_mul_of_nonneg_right hk (Real.exp_pos ..|>.le))
 apply (mul_le_mul_of_nonneg_left hu (Real.exp_pos ..|>.le)).trans_eq; rw [mul_left_comm,←Real.exp_add]; congr 2; ring
lemma pea(v k:ℕ): (∑ i∈range k,Real.exp (-a/2*i)*(i+1:ℝ)^v)≤ 16*fernL v*(a⁻¹)^(v+1):=by
 let c:=Real.exp (-a/4); have ht:0<c:=Real.exp_pos _; have hv:c<1:=by unfold c; rw [Real.exp_lt_one_iff]; linarith
 let P:= fernL v *(a⁻¹)^v; refine (sum_le_sum (fun i _=>task a p h v i)).trans ?_; rw [←mul_sum]; have hr(i:ℕ):Real.exp (-a/4*i)= c^i:=by rw [mul_comm,Real.exp_nat_mul]
 simp_rw [hr]; have hp:0 ≤P:=by unfold P fernL; positivity
 have hy:= (summable_geometric_of_lt_one ht.le hv).sum_le_tsum (range k) (fun i _=> pow_nonneg ht.le i); have hs:∑ i∈range k,c^i ≤ 16*a⁻¹:=by
    refine hy.trans ?_; rw [tsum_geometric_of_lt_one ht.le hv]; apply (inv_le_iff_one_le_mul₀ ?_).mpr; rotate_left; · exact sub_pos.mpr hv
    have hu: 1-c ≥ a/8:=by
       have h':0<a/4:= by linarith
       have he:= Real.add_one_le_exp (a/4); have h₁:c=(Real.exp (a/4))⁻¹:=by unfold c; rw [neg_div, Real.exp_neg]
       have hw:(Real.exp (a/4))⁻¹ ≤ (a/4+1)⁻¹:=inv_anti₀ (by positivity) he; rw [h₁]; have h2:(a/4+1)⁻¹ ≤ 1-a/8:=by rw [←one_div,div_le_iff₀ (by positivity)]; nlinarith
       linarith
    calc
       _ ≤ (16*a⁻¹)*(a/8):=by field_simp; linarith
       _ ≤_:=by gcongr
 refine (mul_le_mul_of_nonneg_left hs hp).trans_eq ?_; ring
end YM.CF.Sour
