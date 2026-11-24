import Ridgetop.PriceU
import Ridgetop.Dial
import Ridgetop.Origin
import Risa.Warehouse
import Preen.Chey
-- pilot price exactly zero, all. 
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 5000
set_option maxHeartbeats 360000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
open Germ Alliance
namespace Spine
namespace PledgeT
open Calico
open Aria Casting Set
open scoped Pointwise
namespace MiterT
open _root_.YM.Gleam.Luster.Risa CF.BProof AnalyticBridge.VerifiedReset
open Py.Rate.LocalLimit Py Py.Dyad Papal _root_.YM.CF.Pannier.Chancel Cliplet Precision
variable (P:Spine) (s A:ℕ)(o:Bool→ Cover)(b:Bool)
local notation "π" i:max=> P.period (P.projection.rows i)
local notation "ζ" i:max=> P.cutoff (P.projection.columns i)
def enoughR (i:ℕ):Prop:= s ≤ P.run.uv (ζ i)
lemma prospects :∀ᶠ i:ℕ in atTop, enoughR P s i:=((P.run.uv_grows.comp (P.law.pick.grow_k.comp P.history.growsB)).tendsto_atTop).eventually_ge_atTop _
lemma showF_grows:Tendsto (fun i=> (showF P s i).val) atTop atTop:=by
 let g:=fun i:ℕ=> (count P.run s (π i)).val; have he : Tendsto g atTop atTop:= (count_grows ..).comp ((P.law.pick.grow_i.comp P.history.growsA).tendsto_atTop)
 apply tendsto_atTop_mono _ he; intro i; change g i ≤ g i *2; omega
open CF.Onyx CF.Ember
local notation "T" d:max=> stackW d
local notation "q" d:max=> scaleY (hat P.par.R.L P.par.x (stackW d))
local notation "A*" d:max=> ((girder P d):ℝ)
local notation "H*" d:max w:max=> outlookT P d w
-- ruleout reassembly money(d) fixed
abbrev flowε(d:ℕ):ℝ:= ((d:ℝ)+1)⁻¹
abbrev collector(d:ℕ):ℝ:= 32*(badge P d + (mudF P*64+1)*(q d)⁻¹)
lemma flowε_p(d:ℕ):0< flowε d:=by unfold flowε; positivity
lemma summers : Tendsto flowε atTop (𝓝 0):= tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop.atTop_add (tendsto_const_nhds (x:= (1:ℝ))))
lemma dollar_flow : Tendsto (collector P) atTop (𝓝 0):=by
 have h:= (bad_f P).add ((tendsto_inv_atTop_zero.comp (stages_q P)).const_mul (mudF P*64+1)); simpa only [Function.comp_def,mul_zero,add_zero,collector] using h.const_mul (32:ℝ)
private lemma fuelΔ {m d C a E V F:ℝ}(hm:1/32 ≤ m)(ht:|d-m*C| *a ≤ E)(hc:|d| * a ≤ V)(ha:0≤a): |C| *a ≤ 32*(V+E):=by
 have hp:0 < m:=lt_of_lt_of_le (by norm_num) hm
 have H:=abs_sub_abs_le_abs_sub (m*C) d
 rw [abs_sub_comm,abs_mul,abs_of_pos hp] at H
 nlinarith only [ht,hc,mul_le_mul_of_nonneg_right H ha,mul_le_mul_of_nonneg_right hm (mul_nonneg (abs_nonneg C) ha)]
lemma wager (l d:ℕ)(w:Cover)(v:A* d ≤ (q d)^l)(g: |roomsW P d l (8*l+6) w| *(A* d)^8 ≤ badge P d): ∀ᶠ i in atTop,
 let F:=T d; let R₀:=pilot P F (drive l (8*l+6)) (outlookT P d w) true
 ‖docket P F (R₀.station i) (outlookT P d w)‖*(A* d)^8 ≤ collector P d:=by
 let S0:= stackW d; let qx:=q d; have hv:= summitT (hat P.par.R.L P.par.x S0); change 1 ≤ qx at hv
 let U0:= mudF P*64; have hU:0≤U0:= mul_nonneg (mud_pos _) (by norm_num)
 let w0:= outlookT P d w; let F:=drive l (8*l+6); let a:= (A* d)
 let P0:=pilot P S0 F w0 true; let x(i):=boarding P S0 F w0 true (P0.station i); let I(i):=P0.station i; let h(i):=docket P S0 (I i) w0; let f0(i):= adage P S0 (I i) w0; let c(i):=ocore P S0 (I i)
 have hb:∀ᶠ i in atTop, |x i| * a^8 ≤ badge P d + qx⁻¹:=
    ((P0.market.abs.mul_const (a^8))).eventually (ge_mem_nhds (lt_of_le_of_lt g (lt_add_of_pos_right _ (by positivity)))) -- g price defeq? P0.price=roomsW
 filter_upwards [P0.trans.tendsto_atTop.eventually (prospects P S0),hb] with i t u
 dsimp only
 rw [← sweep_cast,Complex.norm_real,Real.norm_eq_abs]
 obtain ⟨r,z⟩:=ration P S0 F w0 (I i) t
 have he : |x i - c i*f0 i| * a^8 ≤ U0*qx⁻¹:=by
    have ht:0 ≤a:=Nat.cast_nonneg _
    change _ ≤ U0*qx⁻¹^_ at z
    refine (mul_le_mul_of_nonneg_right z (pow_nonneg ht 8)).trans ((mul_assoc ..).le.trans (mul_le_mul_of_nonneg_left ?_ hU))
    exact artFactor hv ht v
 change |f0 i| *a^8 ≤ 32*(_+_)
 exact (fuelΔ (m:=c i) (d:=x i) (F:=0) r he u (by positivity)).trans_eq (by change 32*(badge P d + qx⁻¹ + U0*qx⁻¹)=32*(badge P d +(U0+1)*qx⁻¹); ring)
-- choose regulator per d.Girt)
lemma coupons (l d:ℕ)(w:Cover)(v:A* d ≤ (q d)^l)(g: |roomsW P d l (8*l+6) w| *(A* d)^8 ≤ badge P d):
 ∃ i:ℕ, needleL P d w*CF.Ember.pinch (showF P (T d) i) ≤ flowε d ∧ ‖docket P (T d) i (outlookT P d w)‖*(A* d)^8 ≤ collector P d:=by
 let F:= pilot P (T d) (drive l (8*l+6)) (outlookT P d w) true
 have hv:Tendsto (fun i=> needleL P d w *CF.Ember.pinch (showF P (T d) i)) atTop (𝓝 0):=by
    have ht:= tendsto_inv_atTop_zero.comp ((tendsto_natCast_atTop_atTop (R:=ℝ)).comp (showF_grows P (T d))) |>.const_mul (needleL P d w*Real.pi); simpa [CF.Ember.pinch,div_eq_mul_inv,mul_assoc,Function.comp_def] using ht
 obtain ⟨i,p,h⟩:= (((hv.comp F.trans.tendsto_atTop).eventually (ge_mem_nhds (flowε_p d))).and (wager P l d w v g)).exists
 exact ⟨F.station i,p,h⟩
#print axioms prospects
#print axioms coupons
end MiterT
end PledgeT
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
