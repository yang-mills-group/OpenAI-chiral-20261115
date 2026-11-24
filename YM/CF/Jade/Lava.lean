import YM.CF.Jade.Trail
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Jade
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
variable {e:ℝ}(C:Support (More N)){P0:BudgetPoint}{As:Set (Pane N)}
open Plume
-- extension general output local with labels from agreeing on support, including output tag. Boot in after epoch.
local notation "N_"=> (mid N B)
variable{E_:Type}[MeasurableSpace E_]
lemma via_w (O:Support (More N))(P: Ids N→Pane N→Cipher N)(p:IsOpen As)(h:∀ {U},U∈As→∀ {V}, V∈As→Agrees O U V→∀ τ ζ':Ids N,Set.EqOn τ ζ' O→P τ U=P ζ' V)(u:Measurable fun i:Ids N × ↥As=> P i.1 i.2):∃ f:Orbit N→ Cipher N, Measurable f∧(∀ τ,Set.EqOn (P τ) (fun V=>f (V,τ)) As)∧(∀ {U V:Pane N},Agrees O U V→∀ τ ζ':Ids N,Set.EqOn τ ζ' O → f (U,τ)= f (V,ζ'))∧(∀ U,¬ Rue.Gates As O U→∀ τ,f (U,τ)=0):=by
 let W: Ids N:=Classical.arbitrary _; let X:Seat N→ Prop:=fun i=> i∈O; let U(τ:Ids N)(i:Seat N):= if X i then τ i else W i; have he(A:Ids N): Set.EqOn (U A) A O:=fun _ v=> if_pos (show X _ from v); have hv: Measurable U:=measurable_pi_lambda _ fun i=>by unfold U; split; exact measurable_pi_apply _; exact measurable_const
 obtain ⟨g,l,w,v,z⟩:= Rue.via_g P O p (fun x _ hu _ hw t=>h hu hw t _ _ (fun _ _=>rfl)) u
 refine ⟨fun (i:Orbit N)=> g (U i.2) i.1,l.comp ((hv.comp measurable_snd).prodMk measurable_fst),fun τ _ u=> ?_,@fun _ _ t τ ζ' y=>?_ ,fun U p τ=> z _ p _⟩ -- tune
 · exact Eq.trans (h u u (fun _ _ _=>rfl) _ _ (he τ).symm) (w _ u)
 change g (U τ) _=g (U ζ') _; rw [show U τ=U ζ' from funext fun i=>by unfold U; split; apply y; assumption; rfl]; exact v _ _ _ t
lemma seal_m(X: Finset (Dwell N))(f:E_→ Cipher N)(p:∀ i, Flour X (f i).val)(μ:Measure E_): Flour X (∫ i,f i∂μ).val:=by
 by_cases h:Integrable f μ; swap; · rw [integral_undef h]; exact Flour.trivial
 let Z:= ∫ i,f i∂μ; refine ⟨fun i=>crumb Z.val i, (fineShape Z).allP.trans (sum_subset (subset_univ (Wheat X)) ?_).symm⟩; intro i _ l; change crumb Z.val i • poke i=0; rw [show crumb Z.val i=0 from Eq.trans (Pastry.hinge (prismL i) h).symm (by simp_rw [show ∀ y,prismL i (f y)=0 from fun y=>(p y).door l]; rw [integral_zero]),zero_smul]
end YM.CF.Jade
