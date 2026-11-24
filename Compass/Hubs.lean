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
variable {N0:Side}{h c:ℝ}(s:Sweep N0)(hs:Anchored s.s)(Q: BudgetPoint)
-- g moves old? (g s) o = old = a=s^-1 . Claim gInv injective. no quotient.
lemma rapX (i:Site N0)(r:ℕ): moveHub s (Φrap N0 i r)= Φrap N0 (inspire s i) r:=by
 apply Subtype.ext; refine Prod.ext ((node_inspire s i).symm) ?_
 change Finset.map (boxA s).symm.toEmbedding (Lattice.halo r {Cube.node i})=Lattice.halo _ _
 rw [Finset.map_eq_image]; change Finset.image ((boxA s).symm : _→_) (Lattice.halo r {Cube.node i}) =_; rw [← Push.Local.halo_map (r:=(boxA s).symm) (fun x y=>?_)]
 · simp only [image_singleton,node_inspire]
 rw [←sitU]; exact sitT ..
lemma dieq (i:Scree.Hub N0)(j:Scree.Hub N0):moveHub s i=moveHub s j ↔ i=j:= Equiv.apply_eq_iff_eq (scope_q s)
lemma movedChose(k:ℕ)(i:Scree.Hub N0): chose k Q (moveHub s i) ↔ chose k Q i:=by unfold chose; rw [show coverNumber Q.B (moveHub s i).val.2= _ from glow_q s Q.B i.val.2]
include hs
lemma pressRX (R:RegBudget N0)(x:IncX Py.primeU R Q h c)(hv:0≤h): IncX Py.primeU (base_Q s R) Q h (duty_Q Q.order Q.power *c):=by
 obtain ⟨F,p,j⟩:=x.weight; let H:= duty_Q Q.order Q.power
 refine ⟨⟨fun i=> H*F (moveHub s i),fun i=> pullPressR Q s i hs (p _) hv,fun i=>?_⟩,fun _ t=>t.elim⟩
 apply le_trans _ (mul_le_mul_of_nonneg_left (j ((boxA s).symm i)) (by unfold duty_Q composeCost; positivity)); rw [Finset.mul_sum]; conv_rhs=>rw [←Equiv.sum_comp (scope_q s)]
 apply le_of_eq; apply sum_congr rfl; intro j _; change ite _ _ _=_; split_ifs with v p h
 · unfold BudgetPoint.mass; rw [show coverNumber _ (scope_q s j).val.2= _ from glow_q s Q.B j.val.2]; change (Trees.currency Q.B Q.supportExponent j.val.2)*(H*F _)=H*(Trees.currency _ _ _* F (moveHub s j)); ring
 · exact False.elim (p (congrArg (boxA s).symm v))
 · exact False.elim (v ((boxA s).symm.injective h))
 rw [mul_zero]
section
variable (s:Sweep (mid N B))(R0:RegBudget (mid N B))(o:Site (mid N B))(D_:ArcΦ)(hs':Anchored s.s)
omit hs
include hs'
lemma cargo (L:ℕ)(p:Axon L (inspire s o) Q R0 h c D_)(h0:1≤h)(h1:4≤(More (mid N B)).val)(h2:∀ i:Scree.Hub (mid N B),chose L Q i → Nonwrapping i.val.2 i.val.1):
 Axon L o Q (base_Q s R0) h (duty_Q Q.order Q.power*c) (tiltA s D_):=by
 let hv:0≤h:=zero_le_one.trans h0
 have he (i:Scree.Hub (mid N B))(v:i.val.1≠Cube.node o):base_Q s R0 i=0:=by
    have ht: (moveHub s i).val.1≠ Cube.node (inspire s o):=by rw [node_inspire]; exact (boxA s).symm.injective.ne v
    unfold base_Q; rw [p.site _ ht]; funext x; exact map_zero (suit_Y s⁻¹)
 refine ⟨pressRX s ?tx Q R0 p.vest hv,he,?fl⟩ -- order #
 case fl =>
    intro i v
    by_cases q:i.val.1=Cube.node o; swap
    · have hl:i≠Φrap _ o 10:= fun t=>q (congrArg (fun x:Scree.Hub (mid N B)=>x.val.1) t)
      rw [he i q,if_neg hl]; exact ⟨rfl, Pill_0 o Q⟩
    let m:=moveHub s i
    have hM:chose L Q m:=(movedChose s Q _ _).mpr v
    obtain ⟨a,b⟩:=p.flair m hM
    refine ⟨?_,?_⟩; · let F:=R0 m; change Taxi.lifeH (step_F s F) _=_; rw [life_T]; change Spire.payZ _ (Taxi.lifeH _ (flashA _ _))=_; rw [flash_one,show Taxi.lifeH F 1=0 from a]; exact sign0 ..
    unfold base_Q; rw [motives Q s hs' o i m rfl (R0 m) (p.vest.weight.choose_spec.1 _) hv q h1 (h2 _ hM),b]; unfold m; rw [←rapX s o 10]; simp_rw [dieq]; split; rfl; exact riseΦ_zero s
 case tx=>exact hs'
#check pressRX
#check motives
#check Push.Local.halo_map
end
end YM.CF.Compass
