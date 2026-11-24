import YM.CF.DPress.Arco.Hera
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
open Larch Ione Taxi Bake Salt LinearT Sour Heath Docket Moral Flight QHol DPress.Analytic
namespace Arco
variable {n:Side}{P:BudgetPoint}{D:Docket P}{ε R h:ℝ}{E E' B B':Cusp n}{Y:Subzero P D.κ}
abbrev OfferV (P:BudgetPoint) (D:Docket P)(Y:Subzero P D.κ)(r:ℝ) :Prop:= Y.g=8*D.Γ ∧ Y.R= 8*(D.κ⁻¹*D.Γ) ∧ Y.S=4*r
structure FrameL (P:BudgetPoint) (D:Docket P) (R h:ℝ) (B E:Cusp n) :Prop where
 first: PactF P (ρL P) h (EmptyD B) D.Γ
 second: XL P h (ρL P) B (D.κ⁻¹*D.Γ)
 real : stipend P B
 θ: ZL P h (lev2 P) E R
structure Lent (F G U V:Cusp n) (D:Docket P)(R h ε:ℝ):Prop where
 p : 0< ε
 q : ε≤1
 d : PactF P (ρL P) h (EmptyD G-EmptyD F) (3*ε*D.Γ)
 kL : XL P h (ρL P) (G-F) ((D.κ⁻¹*D.Γ)*(3*ε))
 zest : ZL P h (lev2 P) (V-U) (ε*R)
 first : FrameL P D R h F U
 second : FrameL P D R h G V
namespace Lent
variable (G:Lent B B' E E' D R h ε) (hv:0 ≤ R)(H:1≤h)(F: OfferV P D Y R)
include G
abbrev βL (ε:ℝ):=1+1/ε
lemma setU :1<βL ε:=lt_add_of_pos_right _ (div_pos zero_lt_one G.p)
lemma hot (z:ℂ): ‖Flight.keep (βL ε) z‖ * ε ≤2:=by
 apply (mul_le_mul_of_nonneg_right (Flight.keep_n z G.setU |>.le) G.p.le).trans; rw [show βL ε*ε= ε+1 from (by unfold βL; rw [add_mul,one_mul,div_mul_cancel₀ _ G.p.ne'])]; linarith [G.q]
omit G
lemma startP {B E:Cusp n} (W:FrameL P D R h B E)(f: OfferV P D Y R) (u:0≤R)(v:1 ≤ h) : Chips P Y B E h:=by
 obtain ⟨p,r,e⟩:=f
 constructor
 · rw [p]; exact (fortune (n:=n) _ _ _ v).toReceipt.relax W.first (le_mul_of_one_le_left D.Γp.le (by norm_num))
 · rw [r]; exact (νreg (n:=n) _ _ _ true v).toReceipt.relax W.second (le_mul_of_one_le_left (mul_nonneg (inv_nonneg.mpr (zero_le_one.trans D.unitK)) D.Γp.le) (by norm_num))
 · exact W.real
 rw [e]; exact (νreg (n:=n) _ _ _ false v).toReceipt.relax W.θ (le_mul_of_one_le_left u (by norm_num))
include G hv H F
abbrev βt(V U:Cusp n)(ε:ℝ)(z:ℂ):=Flight.vista U V (Flight.keep (βL ε) z)
lemma issues(z:ℂ): Chips P Y (βt B B' ε z) (βt E E' ε z) h:=by
 obtain ⟨p,t,r⟩:=F; let j:=Flight.keep (βL ε) z; have hu(k:ℝ)(v:0≤k): k+‖j‖*(3*ε*k)≤ 8*k:=by let w:=G.hot z; have hg:= mul_le_mul_of_nonneg_right w v; change ‖j‖*ε*k ≤_ at hg; nlinarith only [hg,v]
 constructor
 · rw [p, show EmptyD (βt B B' ε z)= EmptyD B+j • (EmptyD B'-EmptyD B) from rfl]; let F0:=fortune (n:=n) P h (ρL P) H; exact F0.toReceipt.relax (F0.add G.first.first (F0.scale j G.d)) (hu D.Γ D.Γp.le)
 · rw [t]; let Q:= νreg (n:=n) P h (ρL P) true H; refine Q.toReceipt.relax (Q.add G.first.second (Q.scale j G.kL)) ?_; rw [mul_comm (D.κ⁻¹*D.Γ)]; exact hu _ (mul_nonneg (inv_nonneg.mpr (zero_le_one.trans D.unitK)) D.Γp.le)
 · apply Arco.staff P G.first.real (team P _ j); rw [sub_eq_add_neg,← neg_one_smul ℂ B]; exact Arco.staff P G.second.real (team P G.first.real _)
 · rw [r]; let V:=νreg (n:=n) P h (lev2 P) false H; refine V.toReceipt.relax (V.add G.first.θ (V.scale j G.zest)) ?_; have hg:= mul_le_mul_of_nonneg_right (G.hot z) hv; change ‖j‖*ε * R ≤ _ at hg; linarith
omit G hv H F
lemma halo(X Y:Cusp n) : HaloL (βL ε) (βt X Y ε):=by intro i K j; unfold βt Flight.vista; dsimp only; simp only [Pi.add_apply,Pi.smul_apply]; exact (differentiableOn_const _).add (Flight.keep_s.smul_const _)
include G hv H F
lemma homes : Dark primeU (Kir P B' E'-Kir P B E) P h (ε*Cog_P P Y.X D.κ):=by
 let Q:= βt B B' ε; let P':= βt E E' ε; have he:= beast H (halo B B') (halo E E') G.setU (issues G hv H F); change Dark primeU (Kir P (Q 1) (P' 1) - Kir P (Q 0) (P' 0)) P h _ at he; rw [show Q 1=B' from ?_,show Q 0=B from ?_,show P' 1=E' from ?_,show P' 0=E from ?_, show Cog_P P Y.X D.κ/(βL ε-1)= ε*Cog_P P Y.X D.κ from ?_] at he; rotate_left
 · exact (show Cog_P P Y.X D.κ/(βL ε-1)= ε*Cog_P P Y.X D.κ from by rw [βL,add_sub_cancel_left,one_div,div_inv_eq_mul,mul_comm]) -- tune `div_inv_eq_mul`
 · unfold P' βt Flight.vista; rw [Flight.zero G.setU]; simp
 · unfold P' βt Flight.vista; rw [Flight.one G.setU]; simp
 · unfold Q βt Flight.vista; rw [Flight.zero G.setU]; simp
 · unfold Q βt Flight.vista; rw [Flight.one G.setU]; simp
 exact he
end Lent
end Arco
end YM.CF.Py.Kay
