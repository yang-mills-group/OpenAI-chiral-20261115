import YM.CF.Iva.Pride
import YM.CF.Iva.Tights
import YM.CF.Lich.Spear
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Iva
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open CF.Appel CF.Newt CF.Char CF.Neige CF.Summit Next Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Wisps Next.SectorChange.Schur MultiNext.SignedSource Lyre Banjo Analysis Pressure AnalyticBridge.MarginalMultiplier3b1d PatchReads SectorNext.Remainder SectorNext.Remainder.Scales Planned.AtomRegular Extra.Iteration Extra.Iteration.Scales
open Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
open AnalyticBridge.Annulus1AD Ac Esti
open Atala Forge Cloak Rill Hive Fock Stilo Palot Scion
open Cube Lat Tenant Tulip
open Pastry Hake Levier Urn Peaks Fock Laic Branch Drapes
open Stilo Palot Scion Function Levier Hake Urn Peaks Fock Laic Branch Drapes
open Rush Scroll Paige Vault Phase Acorn Spire Eire
open Tarn Cay Slate Esti Cour Hest Arena Reine Kennel Facet Broc Pec Push.SectorMeasure.Oriented
open Jet Lich Corne
open Lich.Muster
variable {N P B:Side}{G:Ratio (mid N B) (mid P B)}{S:StepData (Domain N B) (Domain P B)}{x β R e a b:ℝ} {n m l k:ℕ}
local notation "G₅"=> SU.group
variable{T:Tube G₅ S}(Z:Muster G S x e T)(M:Monk G₅ S){w t u C D:ℝ}
local notation "l_"=> Z.post
local notation "q_"=> Z.trot
local notation "Ba"=> radiusB x
local notation "Wa"=> (fun y=>M.atop y x)
local notation "G_"=> SU.group
variable {s t w a b:ℝ}{l1 l2 r r' j κ:ℕ}{T:Tube SU.group S}{M M':Monk SU.group S}
lemma down_k{U:Support (Domain N B)}{V:Support (Domain N B)}{Y:HomeL (Domain N B) (Domain P B)}{q:Chi} (p:Rill.MarkP M U x e b Y l k T q a)(v:V⊆U):MarkP M V x e b Y l k T q a:=by
 refine ⟨⟨fun i g=>p.stampK i (v g),fun i g=> p.mindF i ?_,fun i g=>p.farF i (v g)⟩,fun i g=>p.tea i (chilling le_rfl v g)⟩ -- tune syntax
 exact mem_filter.mpr ⟨mem_univ _,v (mem_filter.mp g).2⟩
variable {U:Loom (mid N B)}{V:Loom (mid P B)}
local notation "Y"=> ((M.V,M.U,β,M.z):HomeL (Domain N B) (Domain P B))
variable (I0:Ids (mid N B))(I1:Ids (mid P B))(H:Muster G S x e T)
variable {h:Chi}{E:Type}[NormedAddCommGroup E][NormedSpace ℝ E]
variable (I:E→L[ℝ] Directions SU.group (Domain N B))(Ω:Support (Domain N B))
variable(φ:S.ratio=ratio G)
local notation "l₀"=> H.post
local notation "κ₀"=> ((H.post+90)*radiusB x)
local notation "σ₀"=> ((H.post+70)*radiusB x)
local notation "Y'"=> erosion ((H.post+70)*radiusB x) Ω
local notation "Ξ"=> (fun x'=>M.atop (I x') x)
include φ
lemma restore(C C':E→Arch G e){N':E→Monk SU.group S} (p:Rill.MarkP M (erosion ((H.post+70)*radiusB x) Ω) x s t Y l₀ n T H.trot H.room) (hu:1000≤radiusB x)(hq: Ready T x)(ht:t < firstRadius SU.group)(Z:Roof (mid N B) s w l1 U)(B':Roof (mid P B) s b l2 V)(hz:l1+l2≤radiusB x)
 (iT:M.key.dome (17*Ba) ⊆ Y') (eC:∀ i:E, Eire.Clan G S (T:=T) φ I0 I1 (Ξ i) U V H.trot h H.post x H.room t β (C i))(eV:∀ i:E, Eire.Clan G S (T:=T) φ I0 I1 (N' i) U V H.trot h H.post x H.room t β (C' i))
 (g:∀ i:E,Forge.Duo SU.group S (Ξ i) (N' i) Ω ∧ M.park=(N' i).park∧M.k=(N' i).k) : ∀ᶠ i in 𝓝 (0:E), Panel H Ω κ₀ (onK (C i)) (onK (C' i)):=by
 let V'(i:E):= TasteZ.hover M.V I i x Y; have hv:Continuous V':=by unfold V' TasteZ.hover Vmove RG.increment; fun_prop
 have he : V' 0=Y:=by simp [TasteZ.hover,V',Vmove]
 have hl:∀ᶠ i in 𝓝 0,MarkP M Y' x s t (V' i) l₀ n T H.trot H.room:= hv.continuousAt.eventually (he.symm ▸ mead p ht) -- dependent rewrite
 let K:= Stilo.beamH Ω; have hk:Ω=bay K:= (bay_beam ..).symm; have hz':AcX S l₀ x 0 K Y':=by -- tune r implicit
    rw [← show erosion _ (bay K)=Y' from congrArg (erosion _) hk.symm]; exact skyC S K
 filter_upwards [hl] with i p'; have he:= lifts_a G S φ K I0 I0 I1 I1 (C i) (C' i) (show PaneL (Ξ i) _ _ _ _ _ from p'.toPaneL) hz' iT hu (eC i) (eV i) (hk ▸ (g i).1.toBeat) hq Z B' (by omega) (fun _ _=>rfl) (fun _ _=>rfl) (fun t u=> by change M.park.up t=_; rw [(g i).2.1]) -- tune
 rw [hk]; exact H.panelV _ _ _ he
-- literal X⊂Ω full and M in Ξ synthetic. erosion pads and transfers
omit φ
variable {X: Ride S}
local notation "F'"=> erosion ((H.post+70)*radiusB x) (Stilo.bay X)
lemma chips_p {Q:Finset (Kite S r)}(p:M.key=cook S Q)(h:1000≤radiusB x)(hp:30*Ba ≤ r)(hx:∀ i∈ Q, halo ((H.post+90)*radiusB x) (Eire.frameP S i)⊆Stilo.bay X) :M.key.dome r ⊆ erosion ((H.post+70)*radiusB x) (erosion 15 (Stilo.bay X)):=by
 refine way_g S Q _ (fun i v=>?_) p r le_rfl; have hu:Lattice.halo κ₀ (stem S i.1)⊆ Stilo.bay X:=Subset.trans (Corona.halo_mono le_rfl (frame_s S i)) (hx i v)
 intro j p; refine mem_filter.mpr ⟨mem_univ _,fun a t=> mem_filter.mpr ⟨mem_univ _,fun u z=>?_⟩⟩; obtain ⟨b,t,x'⟩:=halo_spec.mp t; obtain ⟨j',u',t'⟩:=halo_spec.mp z; rw [mem_singleton.mp t] at x'; rw [mem_singleton.mp u'] at t'; exact hu (halo_spec.mpr ⟨j,p,(separation_triangle j a u).trans (by simp_rw [Nat.add_mul] at *; omega)⟩)
end YM.CF.Iva
