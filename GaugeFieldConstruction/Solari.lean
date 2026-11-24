import GaugeFieldConstruction.Cornell
import GaugeFieldConstruction.Bowdeck
import GaugeFieldConstruction.Dartel
import GaugeFieldConstruction.Pendant
import GaugeFieldConstruction.Crisp
set_option autoImplicit false
set_option maxHeartbeats 400000
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
open Lattice TableF Axon Lenten.Bank Lenten.ModuleB Lenten
open FlightFlux Fluxim Prism Tap Analysis
open Taxi Boom Flot
-- predisp.Loss scheme θ.Top coul
variable {p:BudgetPoint}{P:Side}{M:Tulip.Male}{E:InkD P}{X:Scree.Hub P} {h z a b c t d:ℝ}{k n:ℕ}
abbrev MinorTab(T:BookTarget)(C:ℝ):Prop:= CostOle T.S ≤ C ∧ (∀ i j,‖i‖≤1/50→ ‖j‖≤ 1/50→ ‖T.v i j‖ ≤ C) ∧ (∀ i j, ‖i‖ ≤1/50 → ‖j‖≤1/50→ ‖T.l i j‖≤ C)∧ ∀ i, ‖i‖ ≤1/50 → ‖T.p i‖ ≤ C -- norm ambiguous Com etc. Ψ.
private lemma κTab {E F:Type}[NormedAddCommGroup E][NormedSpace ℝ E][NormedAddCommGroup F][NormedSpace ℝ F](p:Ole E F)(a:ℝ)(h:0≤a): CostOle (a • p)=a*CostOle p:=by
 -- avoiding mismatch proji
 change max ‖a • p.1‖ (max ‖a • p.2.1‖ ‖a • p.2.2.val‖)= a * max ‖p.1‖ (max ‖p.2.1‖ ‖p.2.2.val‖)
 simp only [norm_smul, Real.norm_of_nonneg h]; rw [mul_max_of_nonneg _ _ h, mul_max_of_nonneg _ _ h, show ‖a • p.2.2.val‖=‖a‖ * ‖p.2.2.val‖ from (show ∀ (J K:Type)[NormedAddCommGroup J][NormedSpace ℝ J][NormedAddCommGroup K][NormedSpace ℝ K](A:J→L[ℝ]K), ‖a • A‖ = ‖a‖*‖A‖ from (fun J K _ _ _ _ T=> norm_smul ..)) E (E→L[ℝ] F) p.2.2.val,Real.norm_of_nonneg h]
abbrev bargeDue (P Q:BudgetPoint)(K:Side)(h:ℝ):= let a:=Λgear 1 P.threshold Q.threshold K; let b:=Λgear 2 P.threshold Q.threshold K; a*a*h + a*b*h+ (h*mintPay (caboose*16)+ (αN K)^3*(a*(50*mintPay (caboose*16)*h)))
lemma MoonSize (P':BudgetPoint)(x:PressB p X E h z)(u:0≤h) (M:Tulip.Male)(k:ℕ)(K:Side): MinorTab (MoonBook _ k h P' p K X.val.1 M E) (bargeDue P' p K z):=by
 let μ:=Λgear 1 P'.threshold p.threshold K; let κ:=Λgear 2 P'.threshold p.threshold K; let v:= αN K; have hv:0≤v:=(α_pos K).le; have hp: v ≤1:=inv_le_one_of_one_le₀ (by exact_mod_cast K.property); let I:=X.val.1;
 let c:= bargeDue P' p K z; let μ':=mintPay (caboose*16); have hc := skim x u; have hμ :0 ≤ μ:=mul_nonneg (pow_nonneg (Planned.PrimaryIntegral295.Carrier.unitStep_pos _).le _) (div_nonneg P'.threshold_pos.le p.threshold_pos.le)
 have hκ :0 ≤ κ:=mul_nonneg (pow_nonneg (Planned.PrimaryIntegral295.Carrier.unitStep_pos _).le _) (div_nonneg P'.threshold_pos.le p.threshold_pos.le)
 have h':0≤ μ':=mT_non _ (mul_nonneg cab_pos.le (by positivity))
 have he:c= μ*μ*z+κ*μ*z+(z*μ'+v^3*(μ*(50*μ'*z))):=by unfold c bargeDue; change _= μ*μ*z+κ*μ*z+(z*μ'+v^3*(μ*(50*μ'*z))); rw [mul_comm κ μ]
 constructor
 · let V:= winJ I M h (orbitPH (E 1)); apply (Short_N k (v^(3+k) • V)).trans; rw [κTab _ _ (pow_nonneg hv _)]; change _≤c; rw [he]; exact (le_trans (mul_le_of_le_one_left (Ole_non _) (pow_le_one₀ hv hp)) ((winκ M x u).trans (by change μ'*z ≤ _; rw [mul_comm μ' z]; exact (le_add_of_nonneg_right (by positivity)).trans (le_add_of_nonneg_left (by positivity)) -- fill tune
   )))
 constructor
 · intro i j vi vj; change ‖(μ*μ) • ploy E (gateC I p.threshold i) (gateC I p.threshold j)‖ ≤ c; rw [he,norm_smul, Real.norm_of_nonneg (mul_nonneg hμ hμ)]
   exact (mul_le_mul_of_nonneg_left (ploy_priced x u _ _ (formC_life i _ p vi) (formC_life j _ p vj)) (mul_nonneg hμ hμ)).trans ((le_add_of_nonneg_right (by positivity)).trans (le_add_of_nonneg_right (by positivity))) -- implicit o
 constructor
 · intro i j vi vj; change ‖(μ*κ) • ploy E (gateC I p.threshold i) (gateT I p.threshold j)‖ ≤ c; rw [he,norm_smul, Real.norm_of_nonneg (mul_nonneg hμ hκ),mul_comm μ κ]; exact (mul_le_mul_of_nonneg_left (ploy_priced x u _ _ (formC_life i _ p vi) (formT_life j _ p vj)) (mul_nonneg hκ hμ)).trans ((le_add_of_nonneg_left (by positivity)).trans (le_add_of_nonneg_right (by positivity)))
 intro i vi; change ‖v^3 • μ • landA M I E p h i‖ ≤ c; rw [he,norm_smul,norm_smul,Real.norm_of_nonneg (pow_nonneg hv _),Real.norm_of_nonneg hμ]; apply le_trans _ (le_trans (le_add_of_nonneg_left (a:=v^3*(μ*(50*μ'*z))) (by positivity)) (le_add_of_nonneg_left (by positivity))) -- tune syntax a arg
 have he:50*μ'*z= (1/50:ℝ)⁻¹ * μ' *z:= by ring
 have ht:‖landA M I E p h i‖≤50*μ'*z:= ((landA M I E p h).le_opNorm i).trans ((mul_le_of_le_one_right (norm_nonneg _) (vi.trans (by norm_num))).trans (by rw [he]; exact roof_T M x u))
 exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ht hμ) (pow_nonneg hv _)
-- version not scaling Aℓ.PQ on all.Best.B.
private lemma bendE {F:Type}[NormedAddCommGroup F][NormedSpace ℝ F](hp:|1-t| ≤ c)(hx:0≤d){x y:F}(hq:‖x-t • y‖ ≤ a)(hy:‖y‖ ≤ d): ‖x-y‖ ≤ a+c*d:=by apply (norm_sub_le_norm_sub_add_norm_sub x (t • y) y).trans; apply add_le_add hq; rw [show t • y-y=(t-1) • y from (by rw [sub_smul,one_smul]),norm_smul,Real.norm_eq_abs,abs_sub_comm]; exact mul_le_mul hp hy (norm_nonneg _) (le_trans (abs_nonneg _) hp)
private lemma boe {E F:Type}[NormedAddCommGroup E][NormedSpace ℝ E][NormedAddCommGroup F][NormedSpace ℝ F]{x y:Ole E F}{d:ℝ}(hp:|1-t| ≤ c)(hx:0≤d) (p₀:CostOle (x-t • y)≤a)(hv:CostOle y≤d):CostOle (x-y) ≤ a+c*d:=by
 apply max_le ?_ (max_le ?_ ?_)
 · exact bendE hp hx (x:=x.1) (y:=y.1) ((le_max_left ..).trans p₀) ((le_max_left ..).trans hv)
 · exact bendE hp hx (x:=x.2.1) (y:=y.2.1) (((le_max_left ..).trans (le_max_right ..)).trans p₀) ((le_max_left ..|>.trans (le_max_right ..)).trans hv)
 exact bendE hp hx (x:=x.2.2.val) (y:=y.2.2.val) (((le_max_right ..).trans (le_max_right ..)).trans p₀) ((le_max_right ..|>.trans (le_max_right ..)).trans hv)
variable {Y:TirB P}{u:ℝ}{d:ℝ}
lemma under_scale {T:BookTarget}{V:Support (More P)}{o:Seat P}(v:MinorTab T d)(e:|1-a|≤c)(g: HeadX k Y p o V M h n (scale_B a T) u): HeadX k Y p o V M h n T (u+c*d):=by
 have hD:0 ≤d:=(Ole_non _).trans v.1
 refine ⟨boe e hD g.1 v.1,fun h i j w p=>bendE e hD (g.2.1 h i j w p) (v.2.1 i j w p), fun h i w=>⟨fun j vj=>bendE e hD ((g.2.2 h i w).1 j vj) (v.2.2.1 i j w vj),bendE e hD ((g.2.2 h i w).2) (v.2.2.2 i w)⟩⟩
lemma clear_r(a:ℝ):scale_B a book_zero=book_zero:=by
 unfold scale_B book_zero; simp only []; congr 1 -- tune
 · exact (show ∀ {E F:Type}[NormedAddCommGroup E][NormedSpace ℝ E][NormedAddCommGroup F][NormedSpace ℝ F],a • (0:Ole E F)=0 from fun {E F} _ _ _ _=>smul_zero a)
 · funext i j; simp
 · funext i j; simp
 funext i; simp
--
end
end YM.CF.Oath
end
