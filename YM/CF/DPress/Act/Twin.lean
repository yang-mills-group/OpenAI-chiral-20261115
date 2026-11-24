import YM.CF.DPress.Act.Heart
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
 {x:ℝ}{C:Tew W}{β:ℝ}{b:ℝ}{O:Shore0} {Q:Maud x C G S}
 {P_:Campus C}
open Sour Tap Heath Tutor Docket Resident Campus Flight Moral Rosy
open Arco WagesC
open UVNext.PricedKernels Work.F03 WilsonStartup
namespace Act
open Harvester WagesC Urban
namespace Silo
variable {A:Harvester P_}{ξ:ℝ→ℝ}(T: Silo A ξ Q O) (Wν : Blend (mid N B) A.μ) (α:ℝ)
local notation "vΠ"=> mid N B
local notation "vℓ"=> Q.X.p
variable (E:Lobby Q O β)(p: HonestL E)(G':Lobby Q O β)(q':HonestL G')(f:Lapse E G' b)
abbrev twin := ε_P T E p- ε_P T G' q'
local notation "θ"=> twin T E p G' q'
local notation "ε"=> εΔ O b
include f T
lemma lap : b ≤ O.δ := f.budget.trans (by linarith [O.pos])
lemma ticketμ : Can Q P_ b (twin T E p G' q'):=by
 unfold Can twin ε_P; rw [abs_sub_comm, ← Arco.guess Q.X.p C.uB (T.u.Ψrent _ _ q') (T.u.Ψrent _ _ p)] -- Psi for before maybe rw
 obtain ⟨-,-,-,-,-,j,-⟩:= Field.terms T.p A T.Y _ (T.u.R_out' _ _ p _ q' f) 1; exact j
lemma passage : Can Q P_ O.δ (twin T E p G' q'):= ease θ (T.lap E G' f) (ticketμ T E p G' q' f)
lemma reading0 : Δa T 0 E p=Δa T (twin T E p G' q') G' q':=by rw [T.βnice _ E p (base0 O.pos),T.βnice _ _ _ (T.passage E p G' q' f),twin]; abel
local notation "Q1"=> EHat T (twin T E p G' q') G' q'
local notation "Q0"=> EHat T 0 E p
lemma doubleL : IncX Utrue (Q1-Q0) Q.X.p C.h (A.Ue b):=by
 have ht:= Ione.addT (vℓ) (Urban.R_out' T.p T.u E p G' q' f) (T.wE _ (ticketμ T E p G' q' f)); rw [tally] at ht; rw [T.η_K,EHat, show ∀ a b c:RegBudget (mid N B),a+b-c=(a-c)+b from (fun a b c=>by abel)]; exact ht
local notation "HK"=> χCost (C:=C) ξ x
lemma ΔRRplus : IncX primeU (R0 T Wν θ G' q'- R0 T Wν 0 E p) Q.X.p C.h (A.meter b):=by
 rw [R0,R0,B0,B0,ΤregP,Wν.s0,add_zero, show ∀ a b c:RegBudget (mid N B),a+b-c=(a-c)+b from (fun a b c=>by abel), ←Arco.brolS Q.X.p C.uB (T.ηw _ _ q' (T.passage E p G' q' f)) (T.ηw _ _ p (base0 O.pos))]
 have hp:= (brain_add (Field.terms T.p A T.Y _ (T.doubleL E p G' q' f) 1).1 (wS T Wν θ (T.ticketμ E p G' q' f))); refine (billP (n:=vΠ) (vℓ) C.uB).toReceipt.relax (⟨hp.weight,fun _ t=>False.elim t⟩: IncX primeU _ _ _ _ ) ((add_le_add (le_refl _) (taxPay (A:=A) f.money.le)).trans ?_); have he:=A.costXM f.money.le; rw [add_mul,one_mul] at he; exact he
lemma toll_b : A.Ue b=ε/4*A.Ue O.δ:=by
 have hp: b=(εΔ O b/4)*O.δ:=by
    unfold εΔ; let d:=O.δ; have h0:0<d:= f.δpos; change b=4*b/d/4*d; have ht:(4*b/d/4=b/d):=by ring
    rw [ht,div_mul_cancel₀ _ h0.ne']
 unfold Ue Campus.tax; nth_rewrite 1 [hp]; ring
lemma ΔKKc : ZL Q.X.p C.h (lev2 Q.X.p) (A0 T Wν θ G' q'- A0 T Wν 0 E p) (εΔ O b * A.Hp x O):=by
 let Ψ:= Field.terms T.p A T.Y _ (T.doubleL E p G' q' f) 1; rw [A0,A0,add_sub_add_comm,add_sub_add_comm, ←Arco.truceS Q.X.p C.uB (T.ηw _ _ q' (T.passage E p G' q' f)) (T.ηw _ _ p (base0 O.pos)),Wν.z0,sub_zero]
 obtain ⟨-,-,-,-,h,-⟩:=Ψ; let S:=νreg (n:=vΠ) (vℓ) C.h (lev2 Q.X.p) false C.uB; refine S.toReceipt.relax (S.add (S.add (T.p.saltK T.u.star f) h) (wZ T Wν θ (T.ticketμ E p G' q' f))) ?_
 let P:= ε; let Ω:= (A.Hp x O); have hz:0≤P:= f.εpos.le; have hv(P Q:ℝ)(t:0≤P): P/4*Q ≤ P*|Q|:= ((mul_le_mul_of_nonneg_left (le_abs_self Q) (by positivity : 0 ≤ P/4)).trans (mul_le_mul_of_nonneg_right (by linarith) (abs_nonneg Q))) -- replace
 have hb: C.KΔ x O b ≤ εΔ O b*(|C.CT*C.CY x O| + |O.Vt| +3*|O.Pt|):=by
    unfold Tew.KΔ; rw [mul_left_comm C.CT (εΔ O b),←mul_add]; exact mul_le_mul_of_nonneg_left (by linarith [le_abs_self (C.CT*C.CY x O),le_abs_self O.Pt,abs_nonneg O.Vt,abs_nonneg O.Pt]) hz
 rw [Harvester.Hp, mul_add,mul_add _ (_+3*|O.Pt|)]; refine add_le_add (add_le_add hb ?_) ((taxPay (A:=A) f.money.le).trans ?_); · rw [T.toll_b E G' f,A.GE_sm]; exact hv _ _ hz
 rw [T.toll_b E G' f]; exact mul_le_mul_of_nonneg_right (by linarith [f.εpos]) (A.Ls O.pos)
lemma twins : Lent (T.ΞK E p) (T.ΞK G' q') (A0 T Wν 0 E p) (A0 T Wν θ G' q') T.u.docks (A.Hp x O) C.h ε:=by
 obtain ⟨t,h⟩:= Bf' T.p T.u E p G' q' f; exact ⟨f.εpos,f.εone,t,h,T.ΔKKc Wν E p G' q' f,T.frameQ Wν 0 _ _ (base0 O.pos),T.frameQ Wν θ G' _ (T.passage E p G' q' f)⟩
lemma ΔOKK (v:χCost (C:=C) ξ x ≤ (R.L.val:ℝ)⁻¹* Tew.tiny R x):AccountY Q.X.p C.h (T.duo Wν θ G' q'-T.duo Wν 0 E p) (A.meter b):=by
 refine ⟨T.ΔRRplus Wν E p G' q' f,(billF (n:=vΠ) (vℓ) C.uB).toReceipt.relax ((T.twins Wν E p G' q' f).homes A.δpos C.uB T.v.chill) ?_⟩; rw [T.v.fate]; let d:=O.δ; let s:= (R.L.val:ℝ)⁻¹; have hp: 4*Tew.tiny R x≤ O.δ:= T.u.pawn.strain; have he:χCost (C:=C) ξ x≤ s*(d/4):= v.trans (mul_le_mul_of_nonneg_left (by unfold d; linarith only [hp]) (by positivity))
 refine ((mul_le_mul_of_nonneg_left he f.εpos.le).trans_eq ?_).trans (mul_le_mul_of_nonneg_right (le_mul_of_one_le_left (by positivity) (show 1≤ A.C_D from le_max_left ..)) f.money.le); unfold s d εΔ; have he:= f.δpos; field_simp
end Silo
end Act
end YM.CF.Py.Kay
