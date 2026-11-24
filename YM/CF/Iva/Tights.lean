import YM.CF.Eire.Rail
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Eire
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open CF.Appel CF.Newt CF.Char CF.Neige CF.Summit Next Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Wisps Next.SectorChange.Schur MultiNext.SignedSource Lyre Banjo Analysis Pressure AnalyticBridge.MarginalMultiplier3b1d PatchReads SectorNext.Remainder SectorNext.Remainder.Scales Planned.AtomRegular Extra.Iteration Extra.Iteration.Scales
open Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
open AnalyticBridge.Annulus1AD Ac Esti
open Atala Forge Cloak Rill Hive Fock Stilo Palot Scion
open Cube Lat Tenant Tulip
open Pastry Hake Levier Urn Peaks Fock Laic Branch Drapes
attribute [local instance] opCStarAlgebra
variable {N P B:Side}(G:Ratio (mid N B) (mid P B))(S:StepData (Domain N B) (Domain P B))(u:S.ratio=Rush.ratio G) (z:Odd G.count.val)(e:ℝ)(g:0<e)(X: Meter TailB G e)(V: Meter Grave G e)
variable {T:Tube SU.group S}{x s e b' w t a b d β:ℝ}{r k l k':ℕ}{U:Scree.Loom (mid N B)}{C:Scree.Loom (mid P B)}{M K:Monk SU.group S}{q q':Chi}
local notation "Ft"=> M.sent x T q d l β
local notation "Fv"=> K.sent x T q d l β
local notation "B0"=>radiusB x
local notation "Lm"=>(l+70)*B0
local notation "K₁"=> (l+90)*B0
variable (Ω:Ride S)
local notation "bay"=> Stilo.bay
variable (R R':Ids (mid N B))(L L':Ids (mid P B))(Y Y':Rill.Arch G e)
variable {F:Support (Domain N B)}(f:PaneL M F x s b (M.sent x T q d l β))(p:AcX S l x r Ω F)
variable (Q:Finset (Kite S r))(hp:∀ i∈Q,Lattice.halo ((l+90)*radiusB x) (Eire.frameP S i)⊆ bay Ω)(hm:M.key=cook S Q)
include u p f 
lemma lifts_a (hQ: M.key.dome (17*B0)⊆ F)(v:1000≤ radiusB x)(g:Clan G S (T:=T) u R L M U C q q' l x d b β Y)(g':Clan G S (T:=T) u R' L' K U C q q' l x d b β Y')(hs:Beat M K (bay Ω))(hv:Ready T x)(P':Roof (mid N B) s w k U)(hK:Roof (mid P B) s a k' C)(hk:k'+k≤ B0)(e:Set.EqOn R R' F)(l': Set.EqOn L L' (Passage S F))(p':∀ i,S.ratio.parent i∈ F→ M.park.up i= K.park.up i): CrownB G S _ Y Y' ((l+90)*radiusB x) Ω:=by
 constructor; intro X h; let E':=hatY S X; let D:= Lattice.halo 2 E'; let D':= Lattice.halo 4 E'; have hD:D⊆ D':=chilling (by omega) (Subset.refl _); have he: Lattice.halo (20*B0) E'⊆ F:=p.ports _ h; have hh:D⊆ F:=(chilling (by omega) (Subset.refl _)).trans he
 have he': Lattice.halo k' (Passage S D')⊆ Passage S F:=fun i u=>mem_filter.mpr ⟨mem_univ _, he (icing (by omega : k'+1+4≤20*B0) (mem_filter.mp (parent_hK D' u)).2)⟩
 let V:=U (M.V,R); let V':=U (K.V,R'); let W:=C (Ft,L); let W':=C (Fv,L'); have hx:= fieldR (Q:=D) (K:=Passage S D') f hs hv v p.cup hK P' hk hQ he' ((icing (by omega : k+2≤20*B0)).trans he) R R' L L' e l' -- tune
 unfold Clan at g g'; rw [g,g']; have ht: cloudG G X⊆ D:=fun i m=> halo_subset 2 E' (show i∈ E' from by have ht:= (mem_filter.mp m).2; rw [←u] at ht; exact ((Ratio.embed_parent S.ratio i) ▸ mem_image_of_mem S.ratio.parent ht))
 have hz:X⊆ Passage S D':=fun i h=>mem_filter.mpr ⟨mem_univ _,halo_subset 4 E' (mem_image_of_mem _ h)⟩
 refine ⟨fun i h t=>?_, agrees_mono hx.2 (Finset.coe_subset.mpr ht),agrees_mono hx.1 (Finset.coe_subset.mpr hz)⟩
 apply seineR (q:=q') G u M.park K.park W W' V V' b i (mem_image_of_mem S.ratio.parent (show i.1∈X from h)) (show Lattice.halo 2 E'⊆ D from Subset.refl _) _ hx.2 (fun i t=> p' i (hh t)) -- tune
 intro j t; apply hx.1 j (mem_filter.mpr ⟨mem_univ _,hD t⟩) (mem_filter.mpr ⟨mem_univ _, icing (by omega : 1+2 ≤ 4) (halo_spec.mpr ⟨_,t, Work.E03.parent_step ..⟩)⟩)
end YM.CF.Eire
