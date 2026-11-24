import YM.CF.Vp929.Canon.Gnaw
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option linter.flexible false
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

open Taxi RG.PathData Next.Scheduling UVNext.PricedKernels Work.F03 WilsonStartup
open Jet Yaw Nor Prism Font Push.AbsoluteSums Wray
open Next.Foundations Push.Local AnalyticBridge.VerifiedReset Vow Rue
namespace Test
namespace TestW
open Fir
open SU Bloch Tap
variable {n L:Side} {M:Male} {j:ℕ} {q C d a b v A t:ℝ}
variable {F:RegBudget n}{P:BudgetPoint}{s:Finset (Scree.Hub n)} (vS:liveB s)
local notation "E0"=> Op (Single n)
local notation "E2"=> SpinIdx × SU.Slot
local notation "WW" u:max=> heroP u
local notation "Ψ"=> StackL F s
local notation "μX"=> (1:Pane n)
local notation "ρX"=> spar j M (1:Pane n)
open YM.Push.Loops
variable {T:Momentum→ Pal}{Z:Cover→Pal}
local notation "Ω" => Axis→ Bool
local notation "I_"=>Complex.I
variable {A':Op (Single n)}
private def χf (f:Ω)(x:Cover):ℂ:= ∑ i:Axis, (signs (f i):ℂ)*(x i:ℂ)
private lemma radish (q:ℝ)(f:Ω)(x:Cover): mode (song q f) x= Complex.exp ((q:ℂ)*I_*χf f x):=by
 unfold mode; apply congrArg; unfold song χf; push_cast; rw [mul_sum,mul_sum]; apply sum_congr rfl; intro i _; ring
private lemma chibill (f:Ω)(x:Cover):‖χf f x‖ ≤ 4*(1+Laurent.size x):=by
 have hp(i:Axis):‖(signs (f i):ℂ)*(x i:ℂ)‖≤1+Laurent.size x:=by
    rw [norm_mul,show ‖(signs (f i):ℂ)‖=(1:ℝ) from (by cases h:f i <;> simp [signs,h]), one_mul]; exact (axis_le_size ..).trans (by linarith [Nat.cast_nonneg (α:=ℝ) (Laurent.size x)])
 refine (norm_sum_le ..).trans ((sum_le_sum fun i _=> hp i).trans_eq ?_); simp [Axis]; ring
lemma phase_tail (p:0 ≤q)(η:Ω)(x:Cover): ‖mode (song q η) x-1-(q:ℂ)*I_*χf η x‖ ≤ 48 * q^2 * tweight 2 x:=by
 let z:ℂ:=q*I_*χf η x; let a:ℝ:=1+Laurent.size x; have hv:‖z‖≤ q*(4*a):=by unfold z; rw [norm_mul,norm_mul,Complex.norm_I,mul_one,Complex.norm_real,Real.norm_of_nonneg p]; exact mul_le_mul_of_nonneg_left (chibill η x) p
 let W:=mode (song q η) x; have he:‖W‖=1:= Laurent.mode_real _ _ (by ext i; simp [song])
 suffices ‖W-1-z‖ ≤ 3*‖z‖^2 by
    apply le_trans this; refine (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hv _) (by norm_num : (0:ℝ)≤3)).trans_eq ?_; unfold tweight a; ring
 by_cases h: ‖z‖ ≤ 1
 · apply le_trans (show ‖W-1-z‖ ≤ ‖z‖^2 from (by unfold W; rw [radish]; exact Complex.norm_exp_sub_one_sub_id_le h)); nlinarith
 apply (norm_sub_le ..).trans; apply (add_le_add_left (norm_sub_le W 1) ‖z‖).trans; rw [he,norm_one]; push_neg at h; nlinarith
lemma tier1 (p:Frequency L n q)(η:Ω)(Zs:RailP 2 Z v)(p':Reads Z T)(t:AxisP T):
 ‖T (song q η)-T 0-∑ i:Axis,(q*signs (η i)) • deriv (fun x=>T (bout i x)) 0‖ ≤ ξP * (48*q^2*v):=by
 apply ζP; intro a b; let f(x:Cover):= Z x a b; have hh:Cp 2 f v:= Zs a b
 let D(i):= deriv (fun x=>T (bout i x)) 0; let Q:=song q η; have hT:= sung p η; have hv:=bout_h 0 0 (by norm_num)
 simp only [Matrix.sub_apply,Matrix.sum_apply,Matrix.smul_apply]; change ‖T Q a b-T 0 a b - ∑ i:Axis,(q*signs (η i)) • D i a b‖ ≤ _
 have hz:T 0 a b=∑' x,f x:=by rw [←p'.readK 0 (by simpa [bout_zero] using hv), Laurent.read]; simp [f]
 let A(i:Axis)(x:Cover):ℂ:=q*I_*((signs (η i):ℂ)*(x i:ℂ))*f x; let B(i:Cover):ℂ:= mode Q i * f i; let D'(i:Cover):ℂ:=∑ j:Axis,A j i
 have hq(i:Axis) : A i= fun x:Cover=> ((q:ℂ)*(signs (η i):ℂ)*I_)*((x i:ℂ)*f x):= by funext x; unfold A; ring
 have hp(i): Summable (A i):=by rw [hq]; exact (moments hh (by decide) i).1.mul_left _
 have ht: ∀ i,(q*signs (η i)) • D i a b=∑' x,A i x:=by
    intro i; have hg:= moments hh (by decide) i; have he:= (op_deriv.mp (t.age i).hasDerivAt) a b; rw [show D i a b=_ from (he.congr_of_eventuallyEq (by filter_upwards [bout_v i] with j e using (p'.readK (bout i j) e a b))).unique hg.2]; rw [hq,tsum_mul_left];
    rw [←Complex.coe_smul,smul_eq_mul]; push_cast; ring
 have hi(i): D' i=(q:ℂ)*I_*χf η i*f i:=by rw [χf,mul_sum,sum_mul]
 have ho(i): (B-f-D') i=(mode Q i-1-(q:ℂ)*I_*χf η i)*f i:=by simp only [Pi.sub_apply,hi]; unfold B; ring
 have hk(i):‖(B-f-D') i‖ ≤ 48*q^2* (tweight 2 i*‖f i‖):=by
    rw [ho,norm_mul]; exact (mul_le_mul_of_nonneg_right (phase_tail p.pos.le η i) (norm_nonneg _)).trans_eq (mul_assoc ..)
 have he:Summable B:=by apply Summable.of_norm; simpa only [B,norm_mul,mode_real Q _ hT.1,one_mul] using hh.falls.2.1
 have hu: Summable D':=summable_sum fun i _=> hp i
 have hu': Summable f:= hh.falls.2.1.of_norm
 have hx:‖T Q a b - T 0 a b - ∑ i:Axis,(q*signs (η i)) • D i a b‖=‖∑' x,(B-f-D') x‖:=by
    simp_rw [hz,show T Q a b=∑' x,B x from (p'.readK _ hT a b).symm,ht,Pi.sub_apply]; rw [←Summable.tsum_finsetSum (fun i _=>hp i), Summable.tsum_sub (he.sub hu') hu,Summable.tsum_sub he hu']
 rw [hx]; have hw:Summable (B-f-D'):= (he.sub hu').sub hu;
 refine (norm_tsum_le_tsum_norm hw.norm).trans ((hw.norm.tsum_le_tsum hk (hh.2.1.mul_left _)).trans ?_); rw [tsum_mul_left]; exact mul_le_mul_of_nonneg_left hh.2.2 (by positivity)
private lemma minus_p (k:Bool):signs k.not= -signs k:=by cases k <;> simp [signs]
private lemma flip_w (b:Ω→ℝ)(p:∀ v:Ω,b (update v 0 (!(v 0)))= -b v): ∑ v:Ω,b v=0:=by
 let Q:Ω→Ω := fun v=> update v 0 (!(v 0)); have he:Involutive Q:= fun i=>by funext j; by_cases h:j=0 <;>simp [Q,h]
 have hh:∑ v:Ω,b (Q v)= ∑ v:Ω,b v:= Equiv.sum_comp he.toPerm _; simp_rw [show ∀ v: Ω,b (Q v)=_ from p,sum_neg_distrib] at hh; linarith
private lemma ε_f : (∑ v:Ω,signs (v 0))=0:=flip_w _ fun v=> by rw [update_self]; exact minus_p _
private lemma ε_t (j:Axis): (∑ v:Ω,signs (v 0)*(q*signs (v j)))= if j=0 then 16*q else 0:=by
 split
 next h=>
    subst j; have ht(k:Bool): signs k*(q*signs k)=q:=by cases k<;>simp [signs]
    simp_rw [ht]; simp [Axis]
 next e=> exact flip_w _ fun v=> by rw [update_self,minus_p,update_of_ne e,neg_mul]
lemma tier2 (p:Frequency L n q)(Zs:RailP 2 Z v)(p':Reads Z T)(t:AxisP T):
 ‖sovX q T - deriv (fun x=> T (bout 0 x)) 0‖ ≤ (48*ξP) * q * v:=by
 let D(i):=deriv (fun x=> T (bout i x)) 0; let S(i:Ω):=signs (i 0); let A(i:Ω):=T 0 + ∑ j:Axis,(q*signs (i j)) • D j
 have ht:0<q:=p.pos
 have he(y:Ω):‖S y • (T (song q y)-A y)‖≤ ξP * (48*q^2*v):=by
    unfold A; rw [norm_smul,show ‖S y‖=1 from (by unfold S; cases h:y 0 <;> simp [signs,h]),one_mul,←sub_sub]; exact tier1 p y Zs p' t
 have hu: ∑ v:Ω,S v • A v = (16*q) • D 0:=by
    unfold A; simp_rw [smul_add, Finset.smul_sum,sum_add_distrib, ←sum_smul]
    rw [ε_f, zero_smul,zero_add,sum_comm]; simp_rw [smul_smul,S,←sum_smul, ε_t]; simp
 change ‖sovX q T - D 0‖≤ _
 have hg:0<(16:ℝ)*q:=by positivity
 rw [sovX, ← inv_smul_smul₀ hg.ne' (D 0), ←smul_sub, ←hu,←sum_sub_distrib]; simp_rw [show ∀ y:Ω,signs (y 0) • T (song q y)-S y • A y= _ from fun y=> (smul_sub (S y) (T _) (A y)).symm]; rw [norm_smul,Real.norm_of_nonneg (inv_nonneg.mpr hg.le), inv_mul_le_iff₀ hg]; apply (norm_sum_le ..).trans; refine (sum_le_sum (fun i _=>he i)).trans_eq ?_; simp [Axis]; ring
end TestW
end Test
end YM.CF.Py.Rate
