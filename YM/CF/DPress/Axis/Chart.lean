import YM.CF.DPress.Crew.Site
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
-- cost field HP&R Lift.Γ approx eventual on hall_P.
open Sour Tap Heath Tutor Docket Resident
structure Campus (C:Tew W) where
 i6 : 6≤ C.i
 p2 : 2≤ C.p
 ha : 0 < C.w
 Wk : ℝ
 b0 : ℝ
 b1 : ℝ
 b2 : ℝ
 b3 : ℝ
 μN : ℕ
 τc : 0 < Wk
 Tax : Haro.Lens Wk
 b0p : 0 < b0
 bm : b0 ≤ 1
 b3p : C.dS ≤ b3
 tk : 1 ≤ K.j
 Mot : MotD V b0 b1 b2 b3 μN
 Lob : lobe (32*Cad.rent*Wk) C.h (γ₀ (pond_X C.i C.p C.w i6 p2 ha) b0 (Tenant.quota^2*b1) (Tenant.quota^2*b2) 0 C.h) (pond_X C.i C.p C.w i6 p2 ha)
namespace Campus
variable (Q':Campus C)
abbrev P0 := pond_X C.i C.p C.w Q'.i6 Q'.p2 Q'.ha
abbrev Pm (x:ℝ) := hall_P Q'.P0 x
abbrev bL := Tenant.quota^2* Q'.b1
abbrev bRq := Tenant.quota^2*Q'.b2
abbrev Ct := tiltB Q'.Wk Q'.P0
abbrev rankP (v:ℝ) := RadP Q'.P0 Q'.Wk C.h v
abbrev rM (O:Shore0) := Q'.rankP (C.master O)
abbrev Rs (x:ℝ) := Q'.rankP (C.servant x)
lemma mentor(Q: Maud x C G S): Q'.Pm x=Q.X.p:=by
 let P':=Q.X.p; obtain ⟨p,t,v⟩:= let_X Q'.P0 x; refine bud_y _ _ (t.trans Q.stat.down.hK.symm) (p.trans Q.stat.down.order.symm) (v.trans Q.stat.bill.symm) ?_ ?_; all_goals unfold Pm hall_P; rw [dif_pos (show _ from And.intro (show 0<radiusB x from Q.stat.fee ▸ Q.X.p.B_pos) (And.intro (Q.stat.down.large ▸ Q.X.p.threshold_pos) (Q.stat.down.large ▸ Q.X.p.threshold_le)))]; first| exact Q.stat.down.large.symm|exact Q.stat.fee.symm
lemma sizeP(Q:Maud x C G S)(t:ℝ): RadP Q.X.p Q'.Wk C.h t=Q'.rankP t:=by unfold RadP rankP; unfold RadP tiltB; rw [Q.stat.down.hK] -- syntax first RadP both sides?
lemma tall_x(Q:Maud x C G S) : tiltB Q'.Wk Q.X.p = Q'.Ct:=by unfold tiltB Campus.Ct; unfold tiltB; rw [Q.stat.down.hK]
lemma periodAge (x:ℝ): tiltB Q'.Wk (Q'.Pm x)= Q'.Ct:= by unfold Campus.Ct tiltB; rw [(let_X Q'.P0 x).2.1]
-- transport lobe exactly
lemma spotP(x:ℝ): Sp (Q'.Pm x) = Sp Q'.P0 :=by obtain ⟨p,t,v⟩:= let_X Q'.P0 x; unfold Tutor.Sp u0 Glyph.cap1 Sour.numV Sour.κY; rw [p,t,v] -- tune
lemma warrant : ∀ᶠ x:ℝ in atTop,Tutor (Q'.Pm x) C.h Q'.Wk Q'.b0 Q'.bL Q'.bRq:=by
 let b:= Q'.b0; have ht:0<b/2:=by have he:0<b:=Q'.b0p; positivity
 filter_upwards [buy_B Q'.P0 (2*C.w*Fief.tileN 1) ht,buy_B Q'.P0 (2*(wu Q'.P0+2)*Fief.tileN 1) (half_pos ht)] with x p v
 let P':= Q'.Pm x; obtain ⟨h,l,u⟩:=let_X Q'.P0 x
 refine ⟨Q'.τc,Q'.Tax,C.uB,Q'.b0p,Q'.bm,(by rw [u]; exact p),(by unfold wu; rw [u]; exact v), ((by decide : 1≤ (2:ℕ)).trans P'.power_ge),?_⟩
 unfold lobe γ₀ tiltB; unfold Glyph.cap2 Sour.numV Sour.κY; rw [l,u,h]; exact Q'.Lob -- order tune
lemma weakening (P:BudgetPoint){g:ℝ}(p:Tutor P C.h Q'.Wk Q'.b0 Q'.bL Q'.bRq)(u:lobe (32*Cad.rent*Q'.Wk) C.h g P) : lobe Q'.Wk C.h g P:=by
 refine u.trans ?_; have he: tiltB Q'.Wk P ≤ tiltB (32*Cad.rent*Q'.Wk) P:= by rw [show tiltB (32*Cad.rent*Q'.Wk) P=32*Cad.rent* tiltB Q'.Wk P from (by unfold tiltB; ring)]; exact (show _≤_ from le_mul_of_one_le_left p.heat.le (by linarith [Cad.rent_p]))
 exact div_le_div_of_nonneg_left (by positivity) (by have he:=p.heat; change 0< 4*tiltB Q'.Wk P; positivity) (mul_le_mul_of_nonneg_left he (by norm_num)) -- actual need at Pb pre p etc even without Tutor. generalize later
end Campus
end YM.CF.Py.Kay
