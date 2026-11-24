import Compass.Bullion
import YM.CF.Neon.Ten
import Compass.Hubs
import YM.CF.Ione.Jost
import Compass.Lode
import YM.CF.Brood.Tips
import YM.CF.Coal.Vice
import YM.CF.Moto.Band
import YM.CF.Moto.Kearn
import Compass.Jazz
import Compass.Needle
import Compass.Sloop
import YM.Push.LOCAL_SPLITTING.Orientation
set_option autoImplicit false
set_option maxHeartbeats 300000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Compass
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
variable{N P B:Side}{S:StepData (Domain N B) (Domain P B)}{T: Tube SU.group S}{K:Teller SU.group}{G:Ratio (mid N B) (mid P B)}{R:Patch}{L:ChartRatio SU.group}
variable {d e η t z g A B':ℝ} {j k k' m n l:ℕ}
variable (V:Grace K R L)
open Lich.Muster Lor
open Jet Vol Rel
local notation "G5"=>SU.group
variable {x y0 β:ℝ}(pp:BudgetPoint){t₀ v v₁ p11 p22 p3 p4:ℝ}
local notation "SN"=> Site (Domain N B)
open Cascade
open Fief
open Yaw Pig
open Wray
open Lich.Muster Push.AbsoluteSums
open Iva Eire
local notation "ζ"=> (radiusB x)
open Trees Footprint Iva Eire
open Jade
-- certify.WAGES off all granted tasks
variable {u Hh pK qK a γ vS dS kL w:ℝ}{r p i:ℕ}{X: GramM (mid N B)}{Y: GramM (mid P B)}{U:Grasp V.U B d}
open Oath Feu Feu.Corset Haro Nor Siete PhysicalNext.JointLoad PhysicalNext.JointLoad.Heir
open Moto
open Vow Lilt Larch Bake Rue
open Prism Hove Oise
-- primary picture: rank 0 pressure (global scalar extracted separately), 3 PH weight and 4 derivatives, 4 radial. representation.H.
open Neon Ione Lattice.PlaqAxes AnalyticBridge.VerifiedReset
open Trees Salt
open scoped Mew
variable {Nq:Side}
-- real linear structure proofs
lemma dealScale (q:ℝ)(V:InkD Nq):(q:ℂ) • V=q • V:=by funext v; apply Subtype.ext; exact Complex.coe_smul .. -- direction
lemma deal_budget (q:ℝ)(V:RegBudget Nq):(q:ℂ) • V=q • V:=funext fun i=> dealScale q (V i)
lemma deal_arc(q:ℝ)(D:ArcΦ): (q:ℂ) • D=q • D:=by -- standard Mathlib Complex.coe_smul; Pal spaces. 
 exact Complex.coe_smul ..
lemma C_amount(q:ℝ)(Z:Cusp Nq): (q:ℂ) • Z=q • Z:=by funext i D v; apply Subtype.ext; exact Complex.coe_smul ..
variable {G:Type*}[DecidableEq G]{D:BudgetPoint}{h c:ℝ}
lemma laxHull (H:Finset G)(F:G→Aura Nq→ℝ)(Z:G→Cusp Nq)(p:∀ i∈H,Anuk (Z i) (F i) D h)(w:G→ℝ):
 Anuk (∑ i∈H,w i • Z i) (∑ i∈H,|w i| • F i) D h:=by
 refine ⟨sum_nonneg fun i t=>smul_nonneg (abs_nonneg _) (p i t).1,fun i V e v=>?_⟩
 have hz:=Medal.sumP H (fun a:G=>w a • Z a i V) _ (fun a t=> ((p a t).2 i V e v).rum (w a))
 simp only [Finset.sum_apply,Pi.smul_apply,Real.norm_eq_abs,smul_eq_mul] at hz ⊢; exact hz
lemma spinTall (H:Finset G)(F:G→Aura Nq→ℝ)(i:Skye.Seat Nq)(q:ℝ)(k:ℕ)(A:G→ℝ)(x:∀ p∈H,tallB (F p) k q i ≤ A p)(w:G→ℝ):tallB (∑ j∈H,|w j| • F j) k q i ≤ ∑ j∈H,|w j| *(A j):=by
 unfold tallB; simp_rw [Finset.sum_apply,sum_mul]; rw [sum_comm]; refine sum_le_sum fun j u=>?_; simp only [Pi.smul_apply,smul_eq_mul,mul_assoc,← mul_sum]; exact mul_le_mul_of_nonneg_left (x j u) (abs_nonneg _)
-- Ice sum
local notation "N1"=>mid N B
variable (D:BudgetPoint)
variable (F:G→ Copy (mid N B))(X:G→ RegBudget (mid N B))(Z:G→Cusp (mid N B))(z:G→ℂ)(M:G→ ArcΦ)(h Eμ Kμ Cμ:ℝ)
lemma verses (B0: Site (mid N B))(L0:ℕ)(H:Finset G)(u:∀ i∈H,Ice L0 B0 D h Eμ Kμ Cμ (F i) (X i) (Z i) (z i) (M i))(h':0≤h)(w:G→ℝ):
 Ice L0 B0 D h ((∑ i∈H,|w i|)*Eμ) ((∑ i∈H,|w i|)*Kμ) ((∑ i∈H,|w i|)*Cμ) (∑ i∈H,w i • F i) (∑ i∈H,w i • X i) (∑ i∈H,w i • Z i) (∑ i∈H,w i • z i) (∑ i∈H,w i • M i):=by
 have e:Axon L0 B0 D (∑ i∈H,(w i:ℂ) • X i) h (∑ i∈H, ‖(w i:ℂ)‖* Eμ) (∑ i∈H,(w i:ℂ) • M i):= Py.wave_F H _ _ _ _ _ _ (fun i t=>charge_ν _ L0 B0 _ _ D Eμ h' (u i t).axle) (v:=h')
 simp_rw [deal_budget,deal_arc,Complex.norm_real,Real.norm_eq_abs,←sum_mul] at e
 have hg (i:G):∃ f:Aura N1→ℝ,i∈H→ Anuk (Z i) f D h∧(∀ x:Skye.Seat N1, tallB f D.B (D.supportExponent+1+1) x ≤ Kμ) ∧ SparF B0 D f L0:=by
    by_cases s:i∈H; · obtain ⟨a,x,v,y⟩:=(u i s).grant; exact ⟨a,fun _=>⟨x,v,y⟩⟩
    exact ⟨0,fun v=>False.elim (s v)⟩
 choose f t using hg
 refine ⟨e,?_,?_,?_,?_⟩; · apply (norm_sum_le ..).trans; rw [sum_mul]; refine sum_le_sum fun i v=>?_ ; rw [norm_smul,Real.norm_eq_abs]; exact mul_le_mul_of_nonneg_left (u i v).phase (abs_nonneg _)
 · intro A' v; rw [Finset.sum_apply]; exact sum_eq_zero (fun i p=> (by rw [Pi.smul_apply,(u i p).stout _ v,smul_zero]))
 · refine ⟨_,laxHull H f Z (fun i p=> (t i p).1) w,fun i=>?_,fun i w'=>?_⟩
   · exact (spinTall H f i _ _ (fun _=>Kμ) (fun p v=>(t p v).2.1 _) w).trans_eq (Eq.symm (sum_mul H _ _))
   by_contra h; apply w'; rw [Finset.sum_apply]; apply sum_eq_zero; intro j p; rw [Pi.smul_apply,show f j i=0 from not_not.mp fun v=> h ((t j p).2.2 _ v),smul_zero]
 · intro v hv; rw [Finset.sum_apply,e_s_K D H, τlump D H,Finset.sum_smul, ←sum_add_distrib,←sum_add_distrib]; apply sum_congr rfl; intro i p; rw [←deal_budget,←C_amount, voc_E D,cul_z D]; rw [Pi.smul_apply, (u i p).wear _ hv,smul_add, smul_add,Complex.coe_smul, Complex.coe_smul, smul_assoc]
#check cul_z
end YM.CF.Compass
