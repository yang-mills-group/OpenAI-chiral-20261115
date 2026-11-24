import YM.CF.Rive.Ora
import YM.CF.Pso.Tide
import YM.CF.Rive.Muck
import YM.CF.Pso.Pick
import YM.CF.Ione.Pose
import YM.CF.Ione.Lean
import YM.ProjectorNext.PROJECTOR_EQUIVARIANCE.Trails
import YM.ProjectorNext.PROJECTOR_EQUIVARIANCE.Links
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Rive
open Mew Ione
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
open Jet Yaw Nor Prism Font Push.AbsoluteSums Wray
variable{n:Side} {P: BudgetPoint}{x y a b h c d:ℝ}{k m:ℕ}
local notation "DN"=>tangD n
local notation "E'"=>SU.group
variable {X D Y Z:Support (More n)}
open Vow Salt
open Vow Larch Rue Push.AbsoluteSums Trees Ursell
-- two readings; sum-bound tail with varying witnesses at fixed price
variable{C:Type}[Fintype C][LinearOrder C] (Vb:Mew.Key C→ Pax n) (P:BudgetPoint)
variable (hp1:1≤h)(g:∀ x:Aura n,∀ y,River (fun z:Key C=> Vb z x y)){B:ℕ}{δ S a q:ℝ} (X:Mew.Key C→ Aura n→ℝ)(u:0 ≤ a)(s:∀ i∈hill C,Ready Palot.stern B (X i) a S δ q) (o:∀ i∈hill C,∀ x, Medal P x.val ∅ (Vb i x) h (X i x)) (qh:0 ≤ q)(qt:q<1)
open Bake Gas Palot
lemma river_minus (f g:Mew.Key C→Cipher n)(h:River f)(p:River g):River (fun z=>f z-g z):=by simp_rw [sub_eq_add_neg]; exact dub_V h (yorkB _ p)
lemma lore_H (σ:C→Seat n)(p:∀ x:Aura n,Hush σ x.val (fun z=>Vb z x))(i:Aura n): Hush σ i.val (fun z=>FeeD P (Vb z) i):=by
 intro v hv V hV hu; funext j; by_cases g:visible P i.val ∅ j.1; swap
 · exact (show FeeD P (Vb v) i j=0 from if_neg g).trans (show _ from (show FeeD P (Vb V) i j=0 from if_neg g).symm)
 refine (show FeeD P (Vb v) i j=_ from if_pos g).trans (Eq.trans ?_ (show FeeD P (Vb V) i j=_ from if_pos g).symm)
 change (∑' k:ℕ,funge i (Vb v) 0 k j)=∑' k:ℕ,funge i (Vb V) 0 k j
 refine tsum_congr fun k=>congrFun ?_ j; unfold funge; refine sum_congr rfl fun a _=>?_ ; unfold sta; split
 next h=> unfold guava; apply congrArg; refine prod_congr rfl fun b _=> p (a b) v hv V hV (fun k hk=> hu k ((show (a b).val⊆i.val from h.1 ▸ rimY ⟨_,a⟩ b) hk)) -- tune
 rfl
variable (W0 L0: Mew.Key C→ Cusp n) (hC:∀ i:Aura n,∀ D⊆ i.val,∀ V,River (fun z=> W0 z i D V))(hL:∀ i:Aura n,∀ D⊆ i.val,∀ V,River (fun z=> L0 z i D V))(pX:∀ i:Aura n,∀ V:Orbit n,River (fun z:Mew.Key C=> FeeD P (fun a:Aura n=>W0 z a ∅) i V))
include hC hL pX
lemma moto_R(i:Aura n)(D:Support (More n))(V:Orbit n): River fun z=> roomV P (fun y=>W0 z y ∅) (W0 z) (L0 z) i D V:=by
 change River fun z=> glowV (W0 z) (boastV (FeeD P (fun y=> W0 z y ∅)) (L0 z)) i D V; unfold glowV; split; swap; exact zeroR _
 unfold mintF; simp_rw [Finset.sum_apply]; refine tick_sum _ _ (fun j _=>?_ ); let K(z):=boastV (FeeD P (fun y=> W0 z y ∅)) (L0 z); change River (fun z=>gemB D (W0 z) (K z) j (Stilo.beamH i.val) V); have he(z):=congrFun (gear_v (W0 z) (K z) D j i) V; rw [funext he]; split; swap; exact zeroR _
 simp_rw [Pi.mul_apply,Finset.prod_apply]; refine River.mul_T (cost_R _ _ (fun a p=>hC a _ inter_subset_right V)) (cost_R _ _ (fun b q=>?_ )); unfold K boastV
 apply river_minus; swap; exact zeroR _
 split; exact (hL b _ inter_subset_right V).exp_V; exact (yorkB _ (pX b V)).exp_V
omit hC hL pX
lemma moto_H(σ:C→Seat n)(p:∀ i:Aura n,∀ D⊆ i.val,Hush σ i.val (fun z=> W0 z i D))(q:∀ i:Aura n,∀ D⊆ i.val,Hush σ i.val (fun z=> L0 z i D)) (i:Aura n)(D:Support (More n)): Hush σ i.val (fun z=> roomV P (fun y=>W0 z y ∅) (W0 z) (L0 z) i D):=by
 intro a ha b hb v; let V(z):= fun y:Aura n=> W0 z y ∅; let K(z):=boastV (FeeD P (V z)) (L0 z); change glowV (W0 a) (K a) i D=glowV (W0 b) (K b) i D; unfold glowV; split; swap; rfl
 unfold mintF; refine sum_congr rfl fun j _=>?_ ; rw [gear_v,gear_v]; split; swap; rfl
 next e=>
    have hh:=rim_beat (T:=j); rw [(show lumpD j D i from e).1,bay_beam] at hh
    apply congrArg₂ _ (prod_congr rfl ?_) (prod_congr rfl ?_)
    · intro z u; exact p _ _ inter_subset_right _ ha _ hb fun i g=> v i (hh ▸ mem_union_left _ (mem_biUnion.mpr ⟨_,u,g⟩))
    intro z u; have ht(k)(p:σ k∈ z.val):= v k (hh ▸ mem_union_right _ (mem_biUnion.mpr ⟨_,u,p⟩)); funext V'; unfold K boastV; split; · rw [show L0 a z _= L0 b z _ from q z _ inter_subset_right _ ha _ hb ht]
    rw [show FeeD P (V a) z=FeeD P (V b) z from lore_H V P σ (fun i=>p _ _ (empty_subset _)) z a ha b hb ht]
end YM.CF.Rive
