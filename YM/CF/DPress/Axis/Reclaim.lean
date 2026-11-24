import YM.CF.DPress.Axis.Coe
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
 {P_:Campus C}
open Sour Tap Heath Tutor Docket Resident
-- passport actual per-step. global grant coherent across all budgets and angular motion. Loom unchanged.
namespace Campus
structure Urban (P_:Campus C)(Q:Maud x C G S)(O:Shore0) where
 hope : Heath.Room Q.G₀ Q.X.p C.dS C.vS C.h C.M₀
 ν : QuotaH V.f V.g V.F1 V.F2
 blend : (ν.1 (mid N B)).val=Q.X.J.P
 tone : ν.2=Q.X.J.M
 A : BondL (tatE V ν (mid N B)) (tagE V ν (mid N B)) (body_Q 1) P_.bL P_.bRq P_.b0 C.dS
 pure : pureB A 1
 pawn : Dust C x O
 TutorP : Tutor Q.X.p C.h P_.Wk P_.b0 P_.bL P_.bRq
 docks : Docket Q.X.p
 -- copy fields from Income.Coef; avoids cast.
 Wage : docks.Γ=Γr O R x
 nice : docks.Tr≤ C.servant x/32
 rideP : Ride Q.X.p C.h P_.b0 P_.bL P_.bRq (P_.rM O) docks
 lens : docks.z=rainX R 1 x
 h_sh : docks.Sh=Sh O
 h_sf : docks.SF=SF O
 pitch : docks.γ=gamma P_ x O
 κW : docks.κ=rainX R 2 x
-- re-wrap Axis with casts across parameters
private lemma push_Ω(P_:Campus C)(F:Forecast P_ x O)(P0:BudgetPoint)(t:P0=P_.Pm x): ∃ D:Docket P0,D.Γ=Γr O R x∧D.Tr≤ C.servant x/32∧Ride P0 C.h P_.b0 P_.bL P_.bRq (P_.rM O) D ∧ D.z=rainX R 1 x ∧ D.Sh=Sh O∧ D.SF=SF O∧ D.γ=gamma P_ x O∧ D.κ=rainX R 2 x:=by
 subst P0; obtain ⟨D,v⟩:= F; exact ⟨D,v.δ_G,v.nice,v.Ride0,v.z,v.δ_Sh,v.δ_Sf,v.δ_g,v.κ⟩
structure Church (x:ℝ)(O:Shore0)(P_:Campus C): Prop where
 Year : Dust C x O
 openP : ∀ {M N:Side}{G:Ratio (mid M B) (mid N B)}{S:StepData (Domain M B) (Domain N B)}(Q:Maud x C G S), P_.μN ≤ (mid M B).val → Nonempty (Urban P_ Q O)
namespace Urban
variable (D:Urban P_ Q O)
abbrev seatq(X: Maud x C G S) : Finset (Scree.Hub (mid N B)):= treeΘ X.X.p R.L.val
lemma Θtag (v:ℝ): TagT (tatE V D.ν (mid N B)) (tagE V D.ν (mid N B)) (body_Q v) C.dS:= rise_F V P_.tk U W Q.X Q.stat.dose.courage Q.baseL.size D.ν _ D.blend D.tone C.wq.le
include Q in
lemma Θlive : liveB (seatq Q) := plea _ _ _
lemma Θhead (i:Scree.Hub (mid N B))(t:coverNumber Q.X.p.B i.val.2 ≤1): i∈ seatq Q:=teal _ _ _ V.tallX _ t
end Urban
variable {w:ℝ→ℝ}{E:ℝ→Shore0}
lemma appoint (H:Income0 C E w)(u:sizeK R.L 2 w)(p:∀ᶠ x:ℝ in atTop,4*Tew.tiny R x≤w x) :∀ᶠ x:ℝ in atTop,Church x (E x) P_:=by
 have hw:= C.w0.trans_le C.wp; obtain ⟨a,b,Wb⟩:= cozy C.i hw; let Z:= (sizeK.tempo R.L).spine; filter_upwards [budgetline E H p,P_.forms H u,P_.warrant,Work.E01.radiusB_tendsto.eventually_ge_atTop (C.M₀+C.M₀+30+cipherK C.M₀), Z.eventually (ge_mem_nhds Wb.peta),Z.eventually (ge_mem_nhds C.w0)] with x Cx P0 Κ pX p h
 refine ⟨Cx,?_⟩; intro M P' G S Q v; have hz:= Q.stat.down; let nx:= mid M B; let P:= Q.X.p; have hp: Tutor Q.X.p C.h P_.Wk P_.b0 P_.bL P_.bRq:= P_.mentor Q ▸ Κ
 obtain ⟨D,U₀,hL,uQ,δp,vH,e0,f0,qv⟩:= push_Ω P_ P0 P (P_.mentor Q).symm; let be: Heath.Room Q.G₀ P C.dS C.vS C.h C.M₀:= ⟨Q.A₀,C.uB,hw,_,_,hz.order.symm ▸ Wb,hz.large.symm ▸ p,hz.large.symm ▸ h,by unfold P; rw [Q.stat.fee]; omega,by unfold P; rw [Q.stat.fee]; omega,by unfold P; rw [Q.stat.fee]; omega⟩
 let H:= Q.stat.dose.courage; have hr:= H.leanJ.1; rw [W.h2,W.h4,W.h1,W.h3] at hr; obtain ⟨jT,t1,pS⟩:= demand _ V.pos1.le V.pos2.le _ hr Q.X.J.M; have Ab:=(P_.Mot.earn jT nx 1 C.dS zero_lt_one v hw P_.b3p); have hQ:= rise_F V P_.tk U W Q.X H Q.baseL.size jT 1 t1 pS C.wq.le; letI:Nonempty (Haro.ΘS 1) := Cad.nonzero zero_le_one -- tune
 rw [mul_one (P_.b1),mul_one (P_.b2)] at Ab; obtain ⟨p0⟩:= renderX _ _ _ Ab; have hc:= Sour.ember p0 hQ (continuous_subtype_val.comp continuous_subtype_val) (fun z=>z.val.property) zero_le_one (fun z=>z.property) P_.bm ((mul_one η₁).trans_le P_.Mot.fresh); obtain ⟨A,UA⟩:=hc; -- 
 refine ⟨⟨be,jT,t1,pS,A,UA,Cx,hp, D,U₀,hL,uQ,δp,vH,e0,f0,qv⟩⟩
end Campus
end YM.CF.Py.Kay
