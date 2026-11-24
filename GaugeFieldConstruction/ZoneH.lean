import GaugeFieldConstruction.Quick
import GaugeFieldConstruction.Kub
import GaugeFieldConstruction.Caliber
import GaugeFieldConstruction.Bough
import GaugeFieldConstruction.Kasol
import GaugeFieldConstruction.Bracer
import GaugeFieldConstruction.Savio
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Oath
open Nor
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
open Lich.Muster Push.AbsoluteSums
open Iva Eire
open Wray Prism Font
open PhysicalNext.JointLoad PhysicalNext.JointLoad.Heir Siete
open Feu Feu.Corset Haro
open Jet Plume Eire.Dress
section
open Py Riant Lattice Prism Tap FlightFlux TableF Boom Axon Flot Taxi
open Lenten.ModuleB
open Trees Hake Vow Bake Rue Larch
open TableF Lenten.Bank Lenten
open Layout Fren
open TableF Lenten.Bank Lenten Lenten.Layout Fren
-- detector at chart.Height.Board. aggregate.
-- analytic shape normalization. ℂ major currency.Chart projections.T source. white-all. Landscape
variable {E F:Type}{N:Side}{p:BudgetPoint}{X:Scree.Hub N}{H:InkD N}{M:Tulip.Male}{h a c b d x:ℝ}{k r:ℕ}
-- diagonal block per fixed step parameters. Select 4 unitless factors.
def Crown (u v w a:ℝ) (X:Waves):Waves:= ((u:ℂ) • bV0 X, ((v:ℂ) • bF4 X,(u:ℂ) • bV1 X), ( (w:ℂ) • bF5 X,( (u:ℂ) • bV2 X,(a:ℂ) • bm5 X)))

lemma chartC (x y z u:ℝ)(f:Waves): chartF (Crown x y z u f)= x • chartF f:=by
 apply Prod.ext; · exact Complex.coe_smul _ (bV0 f).val
 refine Prod.ext (ContinuousLinearMap.ext fun i=>Complex.coe_smul x ((bV1 f).val i)) ?_; -- tune
 apply dual_uni; intro i; exact Complex.coe_smul x ((bV2 f).val i i) -- remove
lemma xFcost {Z Y:Waves}(k:ℕ)(z:k≤2)(p:CostOle (Shorten k (chartF Z)- Shorten k (chartF Y))≤ a)(q:1 ≤ k→ ∀ i j:Gem,‖i‖≤1/50→‖j‖≤1/50→‖(bF4 Z).val i j-(bF4 Y).val i j‖ ≤a)(t:2≤ k→(∀ i:Gem,∀ j:Sut,‖i‖≤1/50→‖j‖≤1/50→‖bF5 Z i j-bF5 Y i j‖ ≤ a)∧ ∀ i: ComG, ‖i‖ ≤1/50→ ‖(bm5 Z).val i-(bm5 Y).val i‖ ≤a): ‖MSlot k Z- MSlot k Y‖≤ 2500*a:=by
 let T:=MSlot k Z-MSlot k Y; have hp:0≤a:= le_trans (Ole_non _) p
 have he: chartF T= Shorten k (chartF Z)- Shorten k (chartF Y):=by simp_rw [←chart_origin]; rfl
 refine bean_R T _ ?_ ?_ ?_ ?_
 · rw [he]; exact p.trans (by linarith)
 · by_cases u:1 ≤k
   · apply le_trans (price_heap (show 0<(1/50:ℝ) by norm_num) hp ((bF4 T).val) _); swap
     · intro i w j d; unfold T MSlot; simp only [if_pos u]; exact q u _ _ w d
     exact le_of_eq (by ring)
   have hp:= price_heap (show 0 < (1/50:ℝ) by norm_num) hp ((bF4 T).val) (fun i v j w=>?_)
   · exact hp.trans_eq (by ring)
   unfold T MSlot; simp only [if_neg u]; change ‖(0:ℂ)-0‖≤a; simp [hp]

 · by_cases u:2≤k
   · apply le_trans (price_heap (show 0<(1/50:ℝ) by norm_num) hp (bF5 T) _); swap
     · intro i w j v; unfold T MSlot; simp only [if_pos u]; exact (t u).1 _ _ w v
     exact le_of_eq (by ring)
   have hp:= price_heap (show 0 < (1/50:ℝ) by norm_num) hp (bF5 T) (fun i v j w=> ?_)
   · exact hp.trans_eq (by ring)
   unfold T MSlot; simp only [if_neg u]; change ‖(0:ℂ)-0‖ ≤a; simp [hp]

 by_cases u:2 ≤k
 · apply le_trans (price_desk ((bm5 T).val) (show 0 < (1/50:ℝ) by norm_num) hp _); swap
   · intro i v; unfold T MSlot; simp only [if_pos u]; exact (t u).2 i v
   norm_num; linarith
 have hz: (bm5 T).val=0:=by apply ContinuousLinearMap.ext; intro i; unfold T MSlot; simp only [if_neg u]; exact sub_zero (0:Pal)
 rw [hz, tautF]; exact (@norm_zero (ComG→L[ℝ]Pal) _).le.trans (by positivity)
variable {P L:Side}{Y:Scree.Hub P}{M':Male}{U:InkD P}{Q:BudgetPoint}
abbrev MoonIdeal (k:ℕ)(ρ:Side)(p Q:BudgetPoint)(F:Waves):= let u:=αN ρ; let t:=Λgear 1 p.threshold Q.threshold ρ; let s:=Λgear 2 p.threshold Q.threshold ρ; MSlot k (Crown (u^(3+k)) (t*t) (t*s) (u^3*t) F)
lemma Bequeath (k:ℕ)(t:k≤2)(f:Waves)(q:PressB p X H h b)(u:0≤h)(g:p.threshold=temp x)(v:MetaB Y.val.1 M' f U Q h)(C:Charter N (OratorX N p (lagE X) H x (X.val.1)))(V:HeadX k (OratorX N p (lagE X) H x (X.val.1)) p (X.val.1) X.val.2 M h (radiusB x) (MoonBook _ k h p Q L Y.val.1 M' U) a) : ‖MSlot k (SealT X H p h M)- MoonIdeal k L p Q f‖ ≤2500*a:=by
 obtain ⟨p₀,p₁,p₂⟩:=K_Post q u g k _ V C; let s:= αN L; let μ:=Λgear 1 p.threshold Q.threshold L; let b:=Λgear 2 p.threshold Q.threshold L; let U':=SealT X H p h M; let z:=AnalyticBridge.VerifiedReset.spike SU.group; let G':=Crown (s^(3+k)) (μ*μ) (μ*b) (s^3*μ) f; have hp :=meterL q u M
 apply (xFcost (Y:=G') _ t)
 · unfold G'; rw [hp.port,chartC,v.port]; exact p₀
 · intro h' i j a c; have he:=p₁ h' i j a c; rw [←hp.post] at he
   change ‖(bF4 U').val i j- _‖≤ _; rw [show (bF4 G').val=(μ*μ) • (fave Q Y.val.1 U) from ?_]; exact he -- tune
   rw [←v.post]; change (↑(μ*μ):ℂ) • (bF4 f).val= _; ext i j; exact Complex.coe_smul _ _
 intro j; constructor
 · intro x y i l; have he:=(p₂ j).1 x y i l; rw [←hp.mast] at he
   rw [show bF5 G'= (μ*b) • claw Q Y.val.1 U from ?_]; exact he
   rw [← v.mast]; apply ContinuousLinearMap.ext; intro i; apply ContinuousLinearMap.ext; intro j; exact Complex.coe_smul _ _
 intro x i; rw [hp.mixed]; unfold G'; change ‖ _ - ((↑(s^3*μ):ℂ) • (bm5 f).val x)‖≤_; rw [v.mixed, Complex.coe_smul,mul_smul]; exact (p₂ j).2 x i
end
end YM.CF.Oath
end
