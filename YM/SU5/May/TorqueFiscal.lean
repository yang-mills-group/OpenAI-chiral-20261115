import YM.SU5.May.TorqueStep
import YM.SU5.May.TorqueK
import YM.SU5.Thin.Press.Lilt
/-! # Torque. Earlier-than-buoy high tilt estimator. Adapt MeasureLane, Climate. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Py.Rate
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open CF.Appel CF.Newt CF.Char CF.Neige CF.Summit Next Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Wisps Next.SectorChange.Schur MultiNext.SignedSource Lyre Banjo Analysis Pressure AnalyticBridge.MarginalMultiplier3b1d PatchReads SectorNext.Remainder SectorNext.Remainder.Scales Planned.AtomRegular Extra.Iteration Extra.Iteration.Scales
open Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
open AnalyticBridge.Annulus1AD Ac Esti
open Atala Forge Cloak Rill Hive Fock Stilo Palot Scion
open Cube Lat Tenant Tulip
open Pastry Hake Levier Urn Peaks Fock Laic Branch Drapes
attribute [local instance] opCStarAlgebra
open Rush Scroll Paige Vault Phase Acorn Spire
attribute [local instance] opCStarAlgebra
open Tarn Cay Slate Esti Cour Hest Arena Reine Kennel Facet Broc Pec Push.SectorMeasure.Oriented
open Hom Vale Vale.Grace Next.Free Thera Nacre Dial Fock
open Tye Lich Stake Pail Pail.Dew
open Ione Beau Haro Cascade Fief
open scoped Mew

open Wray Oath Feu Feu.Corset Nor Yaw Pig Oise Jade Plume Push.AbsoluteSums
open Trees Lich.Muster Jet
set_option linter.flexible false
namespace LocalLimit

open Branch
open Preparation
namespace Harbour
open FullBill Marks Intermediate Donor
variable {Λ: Preparation} {Φ : (s:Side)→Scree.Loom s→ Prop} (Y:Course Λ Φ) (i k:ℕ)
local notation "G" => Y.voyage i
local notation "L" => Λ.R.L
local notation "B" => Λ.block
local notation "℘" => (G).CapeT
local notation "s₀" => Y.uv k
local notation "ν" => Y.ivory k
local notation "m" => Y.ir i
local notation "M" s:max=> cell (m) B L s
local notation "𝔸" => projectA Y i k
local notation "𝐴" => (Y.voyage i).X (Y.uv k)
variable (s:ℕ) (F:Intermediate.Room s→ Corr (Λ.Ctor (Y.ir i) s))(t:Intermediate.Room s)
local notation "X" j:max => (screen Y i k s F t) j
-- actual certified physics schedule. prior destiny slope positive.P.Last.
local notation "Qué" i:max => |Λ.R0 (hat Λ.R.L Λ.x i)|
variable (Λ)
open Sleigh
lemma orb_save {u:ℝ}(hv:0<u): Summable fun i:ℕ=> |Λ.R0 (hat Λ.R.L Λ.x i)| *(i:ℝ)^(-u):=by
 let a:= min (1/2) (u/2); have ha:0<a:= lt_min (by norm_num) (half_pos hv); have hy:a ≤ 1/2:= min_le_left ..; have ht:a<u:=(min_le_right ..).trans_lt (half_lt_self hv)
 obtain ⟨C,hC,v⟩ := (skca Λ.R.L 2 Λ.app.fiscal ha).agrees (b:= -1+a) (by push_cast; ring)
 let b:=billX Λ.R.L; let d:=b/2; have hb:0<b:= mul_pos (Gauge.slopeConstant_pos Thera.yet_one) (Real.log_pos (by exact_mod_cast (show 1<Λ.R.L.val by have he:=Λ.V.tallX; omega))); have hd:0<d:= half_pos hb
 have zz : Tendsto (hat Λ.R.L Λ.x) atTop atTop:=by
    unfold hat; refine tendsto_atTop.2 fun t=> ((tendsto_natCast_atTop_atTop (R:=ℝ)).eventually_ge_atTop ((t-Λ.x)/b)).mono (fun i p=>?_); have hg:(t-Λ.x) ≤ (i:ℝ)*b := (div_le_iff₀ hb).1 p; change t ≤ Λ.x+(i:ℝ)*b; linarith
 have ht':= Real.summable_nat_rpow.mpr (show -1+a+(-u)< -1 from by linarith)
 apply summable_of_isBigO_nat ht'; rw [Asymptotics.isBigO_iff]; refine ⟨C*d^(-1+a),?_⟩
 filter_upwards [eventually_gt_atTop (0:ℕ),zz.eventually v,(tendsto_natCast_atTop_atTop (R:=ℝ)).eventually_gt_atTop ((-Λ.x)/d)] with i ih p t
 let j:ℝ:= i; have he:0<j:= by change 0<(i:ℝ); exact_mod_cast ih
 have hm:d*j≤hat Λ.R.L Λ.x i:=by unfold hat; change d*j ≤ Λ.x+j*b; have hg:j*d > -Λ.x:= (div_lt_iff₀ hd).1 t; unfold d at *; linarith
 rw [Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (by positivity)]; erw [Real.rpow_add he (-1+a) (-u)]; apply le_trans (mul_le_mul_of_nonneg_right p (Real.rpow_nonneg he.le (-u))); refine (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_nonpos (mul_pos hd he) hm (by linarith : -1+a≤0)) hC.le) (Real.rpow_nonneg he.le (-u))).trans_eq ?_; rw [Real.mul_rpow hd.le he.le]; ring
open Buffered.Stent.Purchase
noncomputable def feesT (i:ℕ):= lockPrice*(∑ x∈Finset.range i,|Λ.R0 (hat Λ.R.L Λ.x x)|)
lemma fee_up : Monotone (feesT Λ):= fun _ _ h=> mul_le_mul_of_nonneg_left (sum_le_sum_of_subset_of_nonneg (Finset.range_mono h) fun _ _ _=> abs_nonneg _) (Finset.sum_nonneg fun _ _=> norm_nonneg _)
lemma earlyPrice {u:ℝ}(h:0<u):∃ C:ℝ,0 ≤ C ∧ ∀ i:ℕ,feesT Λ i ≤ C*(i:ℝ)^u:=by
 let r(i:ℕ):= Qué i; let K:= orb_save Λ h; let q(x:ℕ):= r x*(x:ℝ)^(-u); let Q:= ∑' x,q x
 have hh(x:ℕ): 0≤ q x:= mul_nonneg (abs_nonneg _) (by positivity); have hp:0 ≤ lockPrice:= Finset.sum_nonneg fun _ _=> norm_nonneg _; have hQ:0≤ Q:= tsum_nonneg hh
 let D':= r 0; have hs:0 ≤ D':= abs_nonneg _; refine ⟨lockPrice*(Q+r 0),mul_nonneg hp (add_nonneg hQ hs),fun i=>?_⟩
 unfold feesT; rw [mul_assoc]; apply mul_le_mul_of_nonneg_left _ hp
 by_cases z:i=0; · simp [z,Real.rpow_zero, Real.zero_rpow h.ne']
 set b':=(i:ℝ)^u; let S:= Finset.range i; let E:= S.erase 0; have e:0∈ S:= mem_range.mpr (Nat.pos_of_ne_zero z); have hk:1 ≤ b':= Real.one_le_rpow (by exact_mod_cast (Nat.pos_of_ne_zero z)) h.le
 change (∑ j ∈ S,r j) ≤ (Q+r 0)*b'; rw [←Finset.sum_erase_add _ _ e,add_mul]; refine add_le_add ?_ (le_mul_of_one_le_right hs hk); change _ ≤ Q * b'; refine (sum_le_sum (g:=fun j=>q j*b') fun j p=>?_).trans (le_of_eq_of_le ((sum_mul ..).symm) (mul_le_mul_of_nonneg_right (K.sum_le_tsum _ fun j _=> hh j) (by positivity))) -- tune
 have hv:1≤ j:= Nat.pos_of_ne_zero (mem_erase.mp p).1; have hy:0<(j:ℝ):=by exact_mod_cast hv
 change _≤ r j* (j:ℝ)^(-u)*b'; rw [Real.rpow_neg hy.le,mul_assoc]; refine le_mul_of_one_le_right (abs_nonneg _) ((inv_mul_cancel₀ (Real.rpow_pos_of_pos hy u).ne').ge.trans (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hy.le (by exact_mod_cast (mem_range.mp (mem_of_mem_erase p)).le) h.le) (by positivity))) -- .ge eq is 1≤?
variable {Λ Y i k s F}
-- order in torque prototypes.
lemma salary_fee {j:ℕ} (z:s ≤ Y.uv k)(p:campus Y i k s F)(g:j<s) : ‖(Harbour.earns Y i k s F t j).val‖ ≤ |Λ.R0 (hat Λ.R.L Λ.x j)|:= (((Intermediate.earns Λ.P (projectA Y i k) s (money Y i k) F Λ.H Λ.response z Λ.height p j g).2.2.2 t).2.1).trans (le_abs_self _)
#print axioms fee_up
#print axioms salary_fee
#print axioms earlyPrice
end Harbour
end LocalLimit
end YM.CF.Py.Rate
