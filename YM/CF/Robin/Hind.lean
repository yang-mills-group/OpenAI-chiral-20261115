import YM.CF.Song.Height
import YM.CF.Neon.Spring
import YM.CF.Swell.VitaK
import YM.CF.Swell.Vote
import YM.CF.Swell.Chill
import YM.CF.Swell.Beam
import YM.CF.Swell.Hush
import YM.CF.Swell.Harp
import YM.CF.Swell.Lawn
import YM.CF.Swell.Bark
import YM.CF.Swell.Tap
import YM.CF.Swell.Fist
import YM.CF.Mew.Tube
import YM.CF.Pso.Pick
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 700000
set_option synthInstance.maxSize 24000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Swell
open Function Filter Topology NormedSpace Lattice Wilson Fock Pastry Scree Sault Sour Stax Skye Jet NormedSpace Scroll Finset Palot Cadre Vow Py
open RG Mew Rive Nor Hake MeasureTheory Bake Rue Salt Leaf
open Metric Drapes Tulip Lat Branch Cube Tenant Hove Haro Hest Dial Proa Tye
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Topology Classical
attribute [local instance] opCStarAlgebra
open Prism Moto Oath Font Levier Rill
attribute [local instance] loreM loreN boreKSpace boreXN
open Push.AbsoluteSums Trees Wray Ione Fief
variable {N B m L:Side}
variable {r:ℕ}
variable {I:Type}[Fintype I][LinearOrder I]
variable {P:BudgetPoint}(E':GramM (mid m B))
open Neon Hom Vale Vale.Grace Kea Nova RP RP.Str Spark Wilson Precision Next.Free Gauge Paige Vault Brace Spire Pressure Jade Oise
variable {A:Teller SU.group}{W:ChartRatio SU.group}{Zp:Patch}(D:Grace A Zp W){d e g x b a t u0 K Kt f l α s':ℝ}
open Roots Chaff Next.SectorChange Next.SectorChange.Schur SectorNext.Remainder SectorNext.Remainder.Scales Pail Lor
local notation "λo" => (allotΨ Zp.L)
variable(P_: BudgetPoint) (F:ℝ→ℝ)
local notation "zp" => (hall_P P_)
local notation "vχ" => (Scales.g SU.group Zp.L)
variable {c a0 h K0 M ΨH A0:ℝ} {k:ℕ}
lemma ζnk (Q':ℝ) : Tendsto (Nano_T P e a Q' · c) atTop (𝓝 0):=by -- Q' param
 have ht:Tendsto (fun h:ℝ=> Nano_T P e a Q' 1 c / h^2) atTop (𝓝 0):= tendsto_const_nhds.div_atTop (tendsto_pow_atTop (by decide))
 refine ht.congr (fun i=>?_); unfold Nano_T KarmaΓ chipZ chal; ring
lemma vρ(i s z:ℝ):Yρ (zp i) a (Eraρ s*z)=s*Yρ P_ a (hc_P*z):=by
 let P':=zp i; obtain ⟨p,u,v⟩:=let_X P_ i; unfold Yρ Eraρ κplant; rw [p,u,v,tV_c P_ _ p u]; unfold trotΦ Taxi.tollV chipZ chal; ring -- tV_c may Occurrence p order.N_check
lemma κg(i x:ℝ): KarmaΓ (zp i) e a x h=x*KarmaΓ P_ e a 1 h:=by unfold KarmaΓ Eraρ chipZ chal; rw [(let_X ..).2.1]; ring
lemma μg(i x:ℝ): Nano_T (zp i) e a x h c=Nano_T P_ e a 1 h c*x:=by unfold Nano_T νmeta; obtain ⟨p,u,v⟩:=let_X P_ i; rw [p,u,v,κg]; ring
lemma μfeet(k:ℕ): sizeK Zp.L 0 (fun i=>feeU (zp i).B k):=by
 have ht:sizeK Zp.L 0 (fun i=>(↑(zp i).B:ℝ)):=by
    apply (sizeK.Bcash Zp.L).cost_d; filter_upwards [hall_l P_] with i p; rw [p]
 unfold feeU; exact (((((ht.accrue (sizeK.mild Zp.L _)).scale _).powC 4).tint (sizeK.mild Zp.L _)).tint (sizeK.mild Zp.L _)) -- add order
lemma δfee (f:sizeK Zp.L k F) (K:ℕ):sizeK Zp.L k (fun i=> pulse_χ (zp i) (F i) K):=by unfold pulse_χ; exact ((μfeet P_ _).tint ((μfeet P_ _).tint f)).low (by omega)
lemma reserve_c :sizeK Zp.L 0 (fun x=> reserveT (zp x).power (zp x).order (zp x).B 1):= by
 apply ((Nor.vale_u P_.power P_.order 1).creditK Zp.L).cost_d; filter_upwards [hall_l P_] with i k; rw [k,(let_X P_ i).1,(let_X P_ i).2.1]
lemma Nano_w : sizeK Zp.L 2 (fun x=>Nano_W (zp x) e a (λo x) h c):=by
 let b':= Real.exp ((θG P_)*Fief.tileN 1)*(∑' i:ℕ, Real.exp (-a/2*i)*(Tenant.quota*((i:ℝ)+1)^4)); let G(x:ℝ):=spanV (zp x).B*b'
 have he: sizeK Zp.L 0 G:= (spg_B P_).tint (sizeK.mild Zp.L b')
 let Z(x):= nold (zp x) a (θG (zp x)) h; have hp: sizeK Zp.L 0 Z:=by
    apply (he.scale ((P_.order+1:ℝ)*h^2)).cost_d; filter_upwards with x; unfold Z nold aimV θG; rw [(let_X ..).1,(let_X ..).2.2]
 unfold Nano_W; simp_rw [κg]; exact ((hp.tint ((size_ψ ..).tint (sizeK.mild Zp.L _))).tint (sizeK.mild Zp.L _)) -- check
lemma μapp(k:ℕ):sizeK Zp.L 0 (fun i=> μReq (zp i).B k):=((spg_B P_).powC k).scale _
abbrev DebtP(P:BudgetPoint)(i:ℕ)(b K:ℝ):= Sour.spanV P.B*(Cu_μ P i b+2*K*Ξ₂ P 1 i b)
abbrev ShareP(P:BudgetPoint)(i:ℕ)(b K:ℝ):=Cu_μ P i b+Ξ₂ P 1 i b*K+Ξ₂ P 2 i b*K*K
lemma lift_Q(f:sizeK Zp.L 2 F): sizeK Zp.L 2 (fun i=> Cu_μ (zp i) k (F i)):= ((μfeet P_ k).scale 2).tint f
lemma ρm(f:sizeK Zp.L 2 F)(m n:ℕ): sizeK Zp.L 2 (fun i=> Ξ₂ (zp i) n m (F i)):= (μapp P_ n).tint (lift_Q P_ _ f)
lemma credit_ζ(f:sizeK Zp.L 2 F): sizeK Zp.L 2 (fun i=> DebtP (zp i) k (F i) (vχ i)) ∧ sizeK Zp.L 2 (fun i=>ShareP (zp i) k (F i) (vχ i)):=by
 let U:=sizeK.main Zp.L; let H:=lift_Q (k:=k) P_ _ f; let Y:=ρm P_ _ f k; let V:=H.accrue ((Y 1|>.tint U).low (by omega)); exact ⟨(spg_B P_).tint (H.accrue (((U.scale 2).tint (Y 1)).low (by omega))), V.accrue ((((Y 2).tint U).tint U).low (by omega))⟩
lemma Ζbuf(f:sizeK Zp.L 2 F)(k:ℕ): sizeK Zp.L 3 (fun i=>BillV (zp i) k (F i) (vχ i)):=by
 let U:=sizeK.main Zp.L; let H:= lift_Q (k:=k) P_ _ f; let Y:=ρm P_ _ f k; exact (reserve_c P_).tint ((((Y 1).tint U).accrue ((((Y 2).tint U).tint U).low (by omega))).accrue ((H.accrue (((U.scale 2).tint (Y 1)).low (by omega))).tint ((spg_B P_).tint U)))
lemma apexT_k(f:sizeK Zp.L 3 F): sizeK Zp.L 3 (fun i=>pivot_T (F i) (zp i)):=by
 unfold pivot_T; simp_rw [(let_X ..).1]; -- reserve_c affected. tune
 exact (by have ht:=reserve_c (Zp:=Zp) P_; simp_rw [(let_X ..).1] at ht; exact ht.tint (((μfeet P_ _).tint f).scale _))
lemma χpay(f:sizeK Zp.L 2 F): sizeK Zp.L 2 (fun i=>ECost (zp i)*F i):=by unfold ECost; simp_rw [(let_X ..).1]; exact ((μfeet P_ _).scale _).tint f
end YM.CF.Swell
