import YM.SU5.WakeInvestment.Vessel
import YM.SU5.WakeInvestment.StageLease
set_option maxHeartbeats 1050000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Py.Rate.LocalLimit.Preparation
open Neon
open Py
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
open Ione Moto Taxi Hove Haro Vow Bake Lilt Prism Rue Larch Push.AbsoluteSums.Trees Salt Jet
open scoped YM.CF.Mew

set_option autoImplicit false
open Mew QuadClock Roots Rive Oise


open QuadClock FullBill Pitching Focus Buffered Afterglow Journey
open QuadClock FullBill Pitching Focus Buffered Afterglow Journey
variable {P:Preparation}{ℓ:ℕ}(Y:Course P (VolumeCape.Dream.Nimbus ℓ))
attribute [-instance] instDecidableEqLex
namespace Yoke
open Tapestry Advance Papyrus Papyrus.Franc
variable {n:Side}
open Py.Rate.Pannier CF.Pannier Chancel Rous Pressure Worth Worth.Pays Graph
variable {z A c:ℝ}
local notation "ξ" s:max => meterC (hat P.R.L P.x s)
open Regis Gleam Tempest
open scoped Topology ContDiff
local notation "θ" s:max => (Papal.xhood (P:=P) s)
local notation "N" s:max i:max => (side Y i s)
open MeasureTheory

/-! Arithmetic of this replica intensive strip. Compare room vs doom only in leading fee. -/
open WakeInvestment
open Lamour.Bridge Celeste Clock Hookah Tapestry Cliplet
variable (s i k : ℕ) (h : Real.exp 1 ≤ P.x)

open Gleam.Wake
open Regis.Wake (assay lipClay)
variable {Iw:ℝ}
local notation "X" s:max => hat P.R.L P.x s
local notation "χ" x:max c:max => WakeInvestment.chip x c
local notation "Cap" q:max=> Gleam.Wake.Vessel.cap q 4
-- costs purchased before all queries in force budgets of WB
abbrev dampA (m:ℕ):ℝ:=16/((m:ℝ)+1)
def dwarf (m:ℕ)(x:ℝ):=chip x (dampA m)
def upperPay (I:ℝ):= 4*I+1
abbrev gradientRent (x:ℝ):= χ x (-1000)
abbrev scratch (x:ℝ):= χ x (-7)
abbrev ticketRent (P:Preparation)(s:ℕ)(I:ℝ):ℝ:= chip (hat P.R.L P.x s) (-200) * (sPow P s I+sPow P s (upperPay I)) -- after sleeve
structure DyeLease (P:Preparation)(s:ℕ)(I:ℝ)(m d:ℕ) : Prop where
 day : 0<hat P.R.L P.x s
 mask: ageC (hat P.R.L P.x s)≤ gaugeRules.c
 tiny: ageC (hat P.R.L P.x s) ≤ skyline (hat P.R.L P.x s)
 gift: 1 ≤ dwarf m (hat P.R.L P.x s)
 shine: 2*Real.sqrt (hat P.R.L P.x s)* slotError gaugeRules (radiusB (hat P.R.L P.x s)) (ageC (hat P.R.L P.x s)) ≤ gradientRent (hat P.R.L P.x s)
 spray: 2*Real.sqrt (hat P.R.L P.x s)*temp (hat P.R.L P.x s)+ gradientRent (hat P.R.L P.x s) ≤ dwarf m (hat P.R.L P.x s)
 eyes: sPow P s I * dwarf m (hat P.R.L P.x s)^m * gradientRent (hat P.R.L P.x s) ≤ scratch (hat P.R.L P.x s)
 wax0: chip (hat P.R.L P.x s) (-200)*(2*scratch (hat P.R.L P.x s)) ≤ tabμ (hat P.R.L P.x s)
 assayE: sPow P s I * assay m (Gleam.Wake.Vessel.cap P.K.top.clip 4) (sPow P s I)≤ sPow P s (upperPay I)
 rescue: 2*sPow P s I / (dwarf m (hat P.R.L P.x s))^(m+1) * assay (m+(m+1)) (Gleam.Wake.Vessel.cap P.K.top.clip 4) (sPow P s I)≤ scratch (hat P.R.L P.x s)
 wax: chip (hat P.R.L P.x s) (-200)*(sPow P s I*(2*dwarf m (hat P.R.L P.x s))^m+sPow P s (upperPay I)) ≤ tollR (hat P.R.L P.x s)
 wave: chip (hat P.R.L P.x s) (-200)*(sPow P s I*(2*dwarf m (hat P.R.L P.x s))^m*(lipClay:ℝ)*Gleam.Wake.Vessel.cap P.K.top.clip 4)≤ tollR (hat P.R.L P.x s)
 pave: ticketRent P s I ≤1
 permits: ∀ D:ℕ, (D:ℝ) ≤ sPow P s I → ticketRent P s I *sizeRent d D ≤ chip (hat P.R.L P.x s) (-199)
private lemma balance (m:ℕ)(v A:ℝ)(p:0<A):
    let P:(ℝ→ℝ) := fun x=> BProof.coin x 0 A 0
    let Q:=fun x=> assay m v (P x); (Pays 0 A 0 Q):=by
 intro P' Q; let S:= Pays.whole 0 A 0; unfold Q assay; apply Pays.scale _; exact plus (Worth.Pays.merit (constant _) (Or.inr (Or.inl ⟨rfl,p⟩))) (Pays.right _ S)
private lemma dyeHouse (P:Preparation)(D:ℕ)(A:ℝ)(p:0<A): ∀ᶠ s in atTop, ticketRent P s A ≤1 ∧ ∀ z:ℕ,(z:ℝ)≤ sPow P s A→ticketRent P s A *sizeRent D z ≤ chip (hat P.R.L P.x s) (-199):=by
 let T:=upperPay A; have he:A<T:=by unfold T upperPay; linarith only [p]
 let S:= fun x=> BProof.coin x 0 A 0; let U(x:ℝ):= chip x (-200)*(S x+BProof.coin x 0 T 0); let g:ℝ:= Fintype.card (SpinIdx × SU.Slot); have h0 :Pays 0 A 0 S:=whole ..
 let R(x:ℝ):=(S x*g+1)^D; let a:=A*D; have ht:Pays (-200/400000) T 0 U:=by simpa only [zero_add,add_zero] using times (whole (-200/400000) 0 0) (plus (Worth.Pays.merit h0 (Or.inr (Or.inl ⟨rfl,he⟩))) (whole ..))
 have hr: Pays 0 a 0 R:=by simpa only [zero_mul] using pot (plus (Pays.right g h0) (Worth.Pays.merit (constant _) (Or.inr (Or.inl ⟨rfl,p⟩)))) D
 filter_upwards [(turnover P).eventually (leap (w:=0) (p:=0) (q:=0) ht (Or.inl (by norm_num))), (turnover P).eventually (leap (w:= -199/400000) (p:=0) (q:=0) (times ht hr) (Or.inl (by norm_num)))] with s h hz
 let x:=hat P.R.L P.x s; have hv:0≤U x:= mul_nonneg (chip_pos ..).le (add_nonneg (BProof.coin_pos ..).le (BProof.coin_pos ..).le)
 refine ⟨h.trans_eq (BProof.coin_zero _),fun z l=> hz.trans' (mul_le_mul_of_nonneg_left (show sizeRent D z ≤ R x from ?_) hv)⟩
 unfold R sizeRent modeCap; push_cast; unfold g; gcongr
open BProof (coin_pow coin_mul coin_pos)
lemma dye_funds (P:Preparation)(D m:ℕ)(A:ℝ)(p:0<A) : ∀ᶠ s in atTop, DyeLease P s A m D:=by
 let S:= fun x=> BProof.coin x 0 A 0; let T:=upperPay A; let U:= fun x=> BProof.coin x 0 T 0; let q:=Cap P.K.top.clip; let H:=dampA m; let K:= H*(m:ℝ); let E:=Real.sqrt; have hh:0 < H:= by unfold H dampA; positivity
 have hs:Pays 0 A 0 S:=whole ..; have hu:Pays 0 T 0 U:=whole ..; have ht: K≤16:=by have hx:H*((m:ℝ)+1)=16:=div_mul_cancel₀ _ (by positivity); unfold K; linarith
 have hv: Pays (16/400000) 0 0 (fun x=> dwarf m x^m):= by
    rcases ht.eq_or_lt with h|h
    · refine (Pays.pot (whole (H/400000) 0 0) m).trans ?_; rw [show H/400000*(m:ℝ)= _ from (div_mul_eq_mul_div H 400000 _).trans (show _ = 16/400000 from congrArg (fun x:ℝ=>x/400000) h),zero_mul]; exact whole .. -- trans uses shape fun target? maybe apply
    exact Worth.Pays.merit (Pays.pot (whole (H/400000) 0 0) m) (Or.inl (by rw [div_mul_eq_mul_div]; exact div_lt_div_of_pos_right h (by norm_num)))
 have hv':Pays (16/400000) 0 0 (fun x=> (2*dwarf m x)^m):=by simp_rw [mul_pow]; exact Pays.scale _ hv
 have hc:(Pays 0 1 0 (fun x=> Real.sqrt x*temp x)):=by
    refine Pays.fix (f:= fun x=> BProof.coin x 0 1 0) (whole ..) ?_; filter_upwards [eventually_gt_atTop (0:ℝ)] with x p; rw [Head.Garland.era x p,←BProof.thresh_eq p,BProof.thresh,coin_mul]; norm_num
 let e(r:ℝ):=(slotError gaugeRules (radiusB r) (ageC r)); let c:ℝ:=2*Tempest.r_age
 have h':Pays c 0 2 e := by
    have hb:Pays c 0 0 (fun x=>ageC x^2):=by convert pot (whole Tempest.r_age 0 0) 2 using 1 <;> first| (unfold c; push_cast; ring)| norm_num
    unfold e slotError faceCutError; apply plus (Worth.Pays.merit (Pays.scale _ hb) (Or.inr (Or.inr ⟨rfl,rfl,by norm_num⟩))); simpa only [zero_add,add_zero] using times (Pays.scale (8*SU.group.colorScale) rising) hb
 have hy:Pays (1/2) 0 0 E:= Pays.fix (whole ..) (f:=fun x=> BProof.coin x (1/2) 0 0) ((eventually_gt_atTop (0:ℝ)).mono fun x hx=>(Head.Garland.era x hx).symm)
 let R:=turnover P
 have hD:=leap (w:= -1000/400000) (p:=0) (q:=0) (times (Pays.scale 2 hy) h') (Or.inl (by norm_num [Tempest.r_age,c]))
 have hU:Pays 0 1 0 (fun x=>2*Real.sqrt x*temp x+gradientRent x):=by simp_rw [mul_assoc (2:ℝ)]; exact plus (Pays.scale 2 hc) (Worth.Pays.merit (whole ..) (Or.inl (by norm_num)))
 have hE:=leap (w:= -7/400000) (p:=0) (q:=0) (times (times hs hv) (whole (-1000/400000) 0 0)) (Or.inl (by norm_num))
 have hZ:=leap (w:=0) (p:=T) (q:=0) (times hs (balance m q A p)) (by simp only [Worth.Earlier,zero_add]; unfold T upperPay; grind)
 have hy':Pays (16/400000) A 0 (fun x=>S x*(2*dwarf m x)^m):=by simpa only [zero_add,add_zero] using times hs hv'
 have hh':=leap (w:= -150/400000) (p:=0) (q:=0) (times (whole (-200/400000) 0 0) (plus hy' (Worth.Pays.merit hu (Or.inl (by norm_num))))) (Or.inl (by norm_num)); have ht':=leap (w:= -150/400000) (p:=0) (q:=0) (times (whole (-200/400000) 0 0) (Pays.right q (Pays.right (lipClay:ℝ) hy'))) (Or.inl (by norm_num))
 have heq(x):dwarf m x^(m+1)= chip x 16:=by rw [dwarf,chip_pow]; unfold dampA; push_cast; rw [div_mul_cancel₀ _ (by positivity)]
 let f':= times (times (Pays.scale 2 hs) (whole (-16/400000) 0 0)) (balance (m+(m+1)) q A p); let hX:= leap (w:= -7/400000) (p:=0) (q:=0) f' (Or.inl (by norm_num));
 filter_upwards [R.eventually_gt_atTop 0,R.eventually ((Pays.limit (whole r_age 0 0) (by norm_num [Worth.Earlier,Tempest.r_age])).eventually (ge_mem_nhds gaugeRules.radius)),R.eventually (leap (p:=0) (q:=0) (w:= -120000/400000) (whole r_age 0 0) (Or.inl (by norm_num [r_age]))),R.eventually (chip_spend 0 H 1 1 hh zero_lt_one),R.eventually hD,R.eventually (leap (w:=H/400000) (p:=0) (q:=0) hU (Or.inl (by positivity))),R.eventually hE,R.eventually (chip_spend (-207) (-205) 2 1 (by norm_num) zero_lt_one),R.eventually hZ,R.eventually hX,R.eventually hh',R.eventually ht',dyeHouse P D A p] with s h l e q' k y v w xX x b t Q
 let Xc:=hat P.R.L P.x s; refine ⟨h,l,e,by simpa only [WakeInvestment.chip,dwarf,zero_div,BProof.coin_zero,one_mul] using q'.le,k,y,v,?_,xX,?_,b,t,Q.1,Q.2⟩
 · unfold scratch; rw [mul_left_comm,←chip_add,show (-200:ℝ) + -7=-207 by norm_num]; simpa only [one_mul] using w.le
 rw [heq, div_eq_mul_inv (_*_),show (chip Xc 16)⁻¹= BProof.coin Xc (-16/400000) 0 0 from ?_]; exact x; rw [BProof.coin_inv]; norm_num
#print axioms dye_funds
end Yoke
end YM.CF.Py.Rate.LocalLimit.Preparation
