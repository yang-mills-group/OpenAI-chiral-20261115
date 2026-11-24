import YM.CF.Oise.Far
import YM.CF.Stake.Loom
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Oise
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open CF.Appel CF.Newt CF.Char CF.Neige CF.Summit Next Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Wisps Next.SectorChange.Schur MultiNext.SignedSource Lyre Banjo Analysis Pressure AnalyticBridge.MarginalMultiplier3b1d PatchReads SectorNext.Remainder SectorNext.Remainder.Scales Planned.AtomRegular Extra.Iteration Extra.Iteration.Scales
open Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.Frobenius
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
open ConnectedActivityE6.Art
open Scroll Eire Girt Err Matrix
open Push Push.AbsoluteSums -- tune
open Lich.Muster Vol AnalyticBridge.SectorAffine
variable {N P B C:Side} {m k j:ℕ}{ι:Type}[MeasurableSpace ι]
local notation "G5"=>SU.group
variable {S: StepData N P}{T:Tube SU.group S}{K:Teller SU.group}{F:Forest S.ratio}{A: Stores S}{κ:S.Choices}{q:Chi}{β x C u v σ w e:ℝ}
variable (V:ι→ Config SU.group N)(U:ι→ Config SU.group P)(P₀:Finset (Cell N))(P₁: Finset (Cell P))(W:ι→ Bond N → SU.group.Mat)
section
attribute [local instance] mt
local instance : BorelSpace SU.group.Mat:=⟨rfl⟩
variable (h:Measurable V)(vu:Measurable U)(t:Measurable W)(f:K.Funds S T) (j:ℕ)
open Offset
variable (Pu Pv:BudgetPoint)(hPu:temp x=Pu.threshold)(hPv:fiery G5 x S.patch.L=Pv.threshold)
local notation "Lα"=> Prices G5 (Active A x F)
variable (Y:ι→LinkArray SU.group (Frozen A x F))(Pq:ι→LogArray SU.group (Active A x F))
variable (hv:Measurable Y)(hB: Measurable Pq) (Q:ι→Prices SU.group (Active A x F))(hQ:Measurable Q)
include h hv hQ
lemma borrow_m : Measurable (fun i=> landed x A F (V i) (Y i) (Q i)):=by
 let U(x':ι):= landed x A F (V x') (Y x') (Q x'); apply measurable_pi_lambda; intro i; by_cases p:i∈ F.trunks
 · rw [funext (fun x'=>F.on_tree _ ⟨i,p⟩ : ∀ x':ι, U x' i=1)] -- tune rw
   exact measurable_const
 let a:F.Free:=⟨i,p⟩; by_cases g:chill A x F a
 · let t: Frozen A x F:=⟨a,g⟩; change Measurable (fun v=>U v i); rw [funext (g:=fun v=> Y v t) fun j=> held_physical x A F (V j) (Y j) (Q j) t]; exact (measurable_pi_apply t).comp hv
 let b: Active A x F:=⟨a,g⟩; change Measurable (fun v=> U v i); rw [funext fun v=> clear_physical x A F (V v) (Y v) (Q v) b]; apply Measurable.mul ((SU.group.lieExp_cont.measurable).comp ((measurable_pi_apply b).comp (tape.measurable.comp hQ))); unfold Precision.replica; split; exact measurable_const; exact (measurable_pi_apply _).comp h
omit hQ
variable (pv:∀ i,MossX k j x A F T (V i) κ u e w q)(p':0<temp x) -- remove
include hB p' pv
lemma mass_m : Measurable (fun i=> fieldU β T F A (V i) κ x j q e (Y i) (Pq i)):= by
 apply borrow_m V h Y hv _ _; exact cape_m V Y Pq pv h hv p' hB
variable (Z:Stores S) (w':ℕ)
local notation "U'"=> (fun i=> fieldU β T F A (V i) κ x j q e (Y i) (Pq i))
include f
lemma hail_a (s b:ℝ): Measurable fun i=> dawnP T A Z F (V i) x κ q e (Y i) j (Pq i) β w' s b:= by apply cupX V U' h (mass_m V h j Y Pq hv hB pv p') f
variable (R:ChartRatio SU.group)(hp:LocalRatio R)(wH:4*e < R.radius)(uτ:0 < e)
include hp wH uτ
lemma pull_m : Measurable fun i=> beamE T A Z F (V i) x κ q e (Y i) j (Pq i) β R w':=by
 have hw:= tape.measurable.comp (cape_m (β:=β) V Y Pq pv h hv p' hB); let X:= locals A Z x F ((w'+104)*radiusB x); exact (Finset.measurable_prod X (fun i _=> (extended_smooth q hp uτ wH).continuous.measurable.comp ((measurable_pi_apply i).comp hw))).mul (Finset.measurable_prod X fun i _=> (broad_smooth q e).continuous.measurable.comp ((measurable_pi_apply i).comp hw))
-- sigma
omit hp wH
variable {γ:ℝ} (eP:2*e< firstRadius SU.group) (tp:∀ i, wheelAux T q e x A F (V i) γ k κ)
include tp hPu hPv eP
lemma fork_m (s:ℝ): Measurable fun i=> Esti.σ T A Z F x κ q e (Y i) j (Pq i) β w' s (fun _:ℝ=> V i) 0:=by
 obtain ⟨a,b,X,D_⟩:=f.feeds; rw [←f.high] at X; let U0:= U'; have hy:= mass_m (β:=β) V h j Y Pq hv hB pv p' -- Y shadow
 have hz:=wand_m (A:=A) V Y h hv p' X uτ eP tp _ (cape_m (β:=β) V Y Pq pv h hv p' hB)
 have hu:=wand_m V Y h hv p' X uτ eP tp _ (pluto V Y pv h hv p')
 have hg(D:ι→LogArray SU.group (Slots S))(h:Measurable D)(i:Slots S):Measurable (fun t=> Esti.media i (D t)):= (show Continuous (Esti.media i) from by unfold Esti.media; fun_prop).measurable.comp h
 have hp(D:ι→LogArray SU.group (Slots S))(h:Measurable D)(s:Signed):Measurable fun t=> Esti.columnP s (D t) (whim x w' Z s):= (Finset.measurable_sum _ (fun i m=> Finset.measurable_sum _ fun j _=> hg D h (s,.inl (i,j)))).add (Finset.measurable_sum _ fun i _=> hg D h (s,.inr i)) -- parser _ 
 unfold Esti.σ Esti.pist averaged; refine measurable_const.mul (measurable_const.mul (Finset.measurable_sum _ fun v _=>?_)); exact ((case_m V U0 h hy f Pu Pv hPu hPv v (whim x w' Z v)).sub (hp _ hz v)).add (hp _ hu v)
end
end YM.CF.Oise
