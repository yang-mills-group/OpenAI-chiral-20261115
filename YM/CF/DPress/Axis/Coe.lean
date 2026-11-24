import YM.CF.DPress.Axis.Chart
set_option autoImplicit false
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
set_option maxHeartbeats 400000
noncomputable section
namespace YM.CF.Py.Kay
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
open Lich.Muster Lor
open Jet Vol Rel
open Cascade
open Fief
open Yaw Pig
open Wray
open Lich.Muster Push.AbsoluteSums
open Iva Eire
open Trees Footprint Iva Eire
open Jade
open Oath Feu Feu.Corset Ione Nor Haro Beau Siete PhysicalNext.JointLoad.Heir Vow
open AnalyticBridge.VerifiedReset
open DPress DPress.Fees Finance Rosy
open scoped YM.CF.Mew
open Oise Larch  Bake
variable
 {N P B:Side}{S:StepData (Domain N B) (Domain P B)}{G:Ratio (mid N B) (mid P B)}{K:Teller SU.group}{R:Patch}{L:ChartRatio SU.group} {d:ℝ} {V:Grace K R L} {U:Grasp V.U B d}{W:GivenX V U}
 {x:ℝ}{C:Tew W}{β:ℝ}{t:Yds (mid P B)}{v:ℂ}{b:ℝ}{O:Shore0} {Q:Maud x C G S}(m:Penny Q O)
open Sour Tap Heath Tutor Docket Resident
namespace Campus
variable (P_:Campus C)
abbrev κ_r(x:ℝ) := rainX R 2 x -- R implicit.F
abbrev Sh(O:Shore0) := 10*|O.s|
abbrev SF(O:Shore0) := 10*|O.K|
abbrev Γr (O:Shore0)(R:Patch)(x:ℝ):= Sh O+rainX R 2 x*SF O+Scales.g SU.group R.L x
abbrev pressFee (x:ℝ)(O:Shore0):= (φFee (P_.Pm x) C.h P_.b0 P_.bL P_.bRq (P_.rM O))
abbrev dr (x:ℝ) (O:Shore0) := 20*|pressFee P_ x O|+ (Scales.g SU.group R.L x)^2
abbrev er (x:ℝ)(O:Shore0) := rentΦ (P_.Pm x) (Γr O R x) (dr P_ x O)
abbrev gamma(x:ℝ)(O: Shore0):= Sh O+Γr O R x+rainX R 1 x* (dr P_ x O+er P_ x O)+Scales.g SU.group R.L x
abbrev Τr (x:ℝ)(O:Shore0):= Sour.tintK (P_.Pm x) (er P_ x O) (gamma P_ x O) (rainX R 1 x)
structure Coef (D:Docket (P_.Pm x)) :Prop where
 δ_Sh : D.Sh=Sh O
 δ_Sf : D.SF=SF O
 δ_G : D.Γ=Γr O R x
 δ_g : D.γ=gamma P_ x O
 z : D.z = rainX R 1 x
 κ : D.κ = rainX R 2 x
 d : D.d=dr P_ x O
 nice : D.Tr ≤ C.servant x /32
 Ride0 : Ride (P_.Pm x) C.h P_.b0 P_.bL P_.bRq (P_.rM O) D
abbrev Forecast(x:ℝ)(O: Shore0):Prop:= ∃ D:Docket (P_.Pm x), Coef (O:=O) P_ D
variable {u:ℝ→ℝ}{Tκ:ℝ→ Shore0}(q:Income0 C Tκ u)(p:sizeK R.L 2 u)
lemma νΔ : 0< P_.Ct:= desire _ P_.τc
lemma sp0 (s:ℝ): 0 ≤ s→0≤ P_.rankP s:=fun h=>by unfold rankP RadP; have hg:=desire P_.P0 P_.τc; positivity
include p q
local notation "L'"=>((R.L.val:ℝ)⁻¹)
lemma arc_C : sizeK R.L 2 (fun i=>P_.rM (Tκ i)) ∧ sizeK R.L 2 P_.Rs:=by
 let t:= C.ζCA*L'; let y:= 8*P_.Ct*t/C.h^2; have zH(s):P_.rankP (C.pay s)=y*s:=by unfold y t Tew.pay rankP RadP Ct; ring
 unfold rM Rs Tew.master Tew.servant; simp_rw [q.stone,zH]; exact ⟨p.scale _, (dev_R R).1.scale _⟩
lemma zen : sizeK R.L 1 (fun i=>Γr (Tκ i) R i) := sizeK.accrue (((iFX q.s).scale 10).accrue (rockP 2 ((iFX q.K).scale 10))) (sizeK.main _) -- includes p
lemma earn_d : sizeK R.L 2 (fun i=>P_.dr i (Tκ i)):=by
 have ht:= fee_f P_.P0 (fun x=>P_.rM (Tκ x)) P_.b0 (Cad.rent*P_.bL) (Cad.rent*P_.bRq) C.h (P_.arc_C q p).1
 unfold dr pressFee φFee; have hx(r c:ℝ): Cad.rent*r*c=Cad.rent*c*r:=by ring; -- simp last rhs
 simp_rw [hx (P_.rM _) P_.bL,hx (P_.rM _) P_.bRq]; exact ((iFX ht).scale 20).accrue ((sizeK.main R.L).square 2) -- P_.Pm unfolds via defeq
lemma earn_e : sizeK R.L 3 (fun i=>P_.er i (Tκ i)):= pole_Q P_.P0 _ _ (zen q p) (P_.earn_d q p)
lemma earn_g : sizeK R.L 1 (fun i=> P_.gamma i (Tκ i)):= sizeK.accrue (((((iFX q.s).scale _).accrue (zen q p))).accrue (rockP 1 ((P_.earn_d q p).accrue ((P_.earn_e q p).low (by omega))))) (sizeK.main _)
lemma ζearn : sizeK R.L 3 (fun i=> P_.Τr i (Tκ i)):= σΩ P_.P0 _ _ (P_.earn_g q p) (P_.earn_e q p)
-- performance: $τr> costY^2 coin. delayed easy.t. No serialization plan denominator needed. proof after grant. Unit pre κ scale in Θ.Fee. exponent.F.Power.BOOT.
private lemma paid_Tr : ∀ᶠ x in atTop,P_.Τr x (Tκ x) ≤ C.servant x /32:=by
 let T:=C.ζCA * L' /32; have hp:0<T:=by unfold T; have he:= C.horn; positivity
 apply (tenor_Q T _ (Litt.gain (P_.ζearn q p)) hp).mono; intro i v; refine le_trans v (le_of_eq ?_); unfold T Tew.servant Tew.tiny Tew.pay; ring
lemma forms : ∀ᶠ x:ℝ in atTop,Forecast P_ x (Tκ x):=by
 let o(x):= Tκ x; let g(x):= Γr (o x) R x; let z(x):=P_.gamma x (o x); let d_r(x):=P_.dr x (o x); let σ(x):=spanV (P_.Pm x).B; let G(x):=Scales.g SU.group R.L x; let hm:=spg_B (R:=R) P_.P0
 let hq:sizeK R.L 1 g:= zen q p; let hf:sizeK R.L 2 d_r:= P_.earn_d q p
 let y:= uΨ
 filter_upwards [P_.paid_Tr q p,(fee_Q P_.P0 z (P_.earn_g q p)).spine.eventually (ge_mem_nhds (show (0:ℝ)<1/2 from by norm_num)), (hm.tint hq).spine.eventually (ge_mem_nhds zero_lt_one),((hm.tint hf).low (k:=1) (by omega)).spine.eventually (ge_mem_nhds (show 0 < wΨ/4 from by norm_num [wΨ])),spice_R (R:=R),pill_R (k:=1) d_r (show 0< wΨ/4 by norm_num [wΨ]) hf] with x p' κx β c h q0
 let τ:=o x; let J:=g x; have hr:0<G x:= h.2.2; have hz:0≤ Sh τ:= by unfold Sh; positivity
 have ht:0 ≤ SF τ:=by unfold SF; positivity
 have he:1≤rainX R 2 x:=h.2.1; have hh:Sh τ+rainX R 2 x*SF τ<J:=lt_add_of_pos_right _ hr; have pK:0 ≤ Sh τ+rainX R 2 x*SF τ:= add_nonneg hz (mul_nonneg (zero_le_one.trans he) ht); have hed: G x ≤ J:= le_add_of_nonneg_left pK; have hu:=hr.trans_le hed
 have hk:0< d_r x:= add_pos_of_nonneg_of_pos (mul_nonneg (by norm_num) (abs_nonneg _)) (pow_pos hr _)
 let v:=σ x; have v0:0≤ v:= Nat.cast_nonneg _; have h0:0 ≤ P_.er x τ:= add_nonneg (mul_nonneg (mul_nonneg v0 hk.le) hu.le) (mul_nonneg (mul_nonneg (mul_nonneg v0 (inv_nonneg.mpr y.le)) hu.le) hk.le)
 have hb:Sh τ + J + rainX R 1 x * (d_r x + P_.er x τ) ≤ z x:= le_add_of_nonneg_right hr.le
 have hb':0< z x:= lt_of_lt_of_le (add_pos_of_pos_of_nonneg (add_pos_of_nonneg_of_pos hz hu) (mul_nonneg h.1.le (add_nonneg hk.le h0))) hb; have heC:v*d_r x≤ wΨ/4:= c; have hL:v*d_r x ≤ wΨ:= heC.trans (by linarith [uΨ])
 have ha:d_r x+ v*d_r x*J-(wΨ-v*d_r x)*J<0:=by rw [pow_one] at q0; have ht: d_r x< wΨ/4*J:= (q0.trans_le (mul_le_mul_of_nonneg_left hed (by norm_num [wΨ]))); have he:=mul_le_mul_of_nonneg_right heC hu.le; unfold wΨ at *; linarith only [ht,hu,he]
 let D:Docket (P_.Pm x):= ⟨_,_,J,z x,d_r x,rainX R 1 x,rainX R 2 x,hz,ht,hh,hk,hb',h.1,he,κx,hb,β,hL,ha⟩
 refine ⟨D,rfl,rfl,rfl,rfl,rfl,rfl,rfl,p',?_⟩; let t:= P_.rM τ; have hp:0≤t:= sp0 P_ (C.master τ) (show 0≤ C.pay τ.δ from le_trans (le_of_eq (by unfold Tew.pay; rw [mul_zero] : 0=C.pay 0)) (C.monoP τ.pos)) -- pay pos needed
 let F'(t:ℝ):= φFee (P_.Pm x) C.h P_.b0 P_.bL P_.bRq t; change 20*(|F' 1| * t) ≤20*|F' t|+ G x^2; rw [show F' t= F' 1*t from (by unfold F' φFee feeΨ; ring),abs_mul (F' 1) t, abs_of_nonneg hp]; linarith [sq_nonneg (G x)]
end Campus
end YM.CF.Py.Kay
