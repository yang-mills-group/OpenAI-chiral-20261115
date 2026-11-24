import YM.CF.Eire.Dab
import YM.CF.Rill.Opt
import YM.CF.Rill.Peak
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
-- eroded bay. Fr.M.L pressure proofs account at entrances
section
variable {g:Side}{E F X:Support g}
def erosion(n:ℕ)(S:Support g):Support g:= univ.filter fun i=> Lattice.halo n {i} ⊆ S
lemma erosion_c(n:ℕ)(S:Support g): Lattice.halo n (erosion n S)⊆ S:=by
 intro j p; obtain ⟨i,l,v⟩:=halo_spec.mp p; exact (mem_filter.mp l).2 (halo_spec.mpr ⟨i,mem_singleton_self _,v⟩)
lemma erosion_b(n m:ℕ)(h:Lattice.halo n E⊆ X)(p:r+m≤n): Lattice.halo r E⊆ erosion m X:=by
 intro i v; obtain ⟨z,t,l⟩:=halo_spec.mp v; refine mem_filter.mpr ⟨mem_univ _,?_⟩; intro j v; obtain ⟨y,g,v⟩:=halo_spec.mp v; rw [mem_singleton.mp g] at v; exact h (halo_spec.mpr ⟨z,t,(separation_triangle z i j).trans (by omega)⟩)
lemma chilling (p:r≤k) (h:X⊆E): Lattice.halo r X ⊆ Lattice.halo k E:= Corona.halo_mono p h
lemma icing (p:r+l≤k):Lattice.halo r (Lattice.halo l X) ⊆ Lattice.halo k X:=by
 intro i v; obtain ⟨j,t,v⟩:= halo_spec.mp v; obtain ⟨z,u,t⟩:=halo_spec.mp t; exact halo_spec.mpr ⟨z,u,(separation_triangle z j i).trans (by omega)⟩
end
variable (Ω:Ride S)
local notation "bay"=> Stilo.bay
local notation "O"=> erosion ((l+70)*radiusB x) (bay Ω)
variable (R:Ids (mid N B))(L:Ids (mid P B))(Y:Rill.Arch G e)
abbrev Clan (M:Monk SU.group S)(U:Scree.Loom (mid N B))(C:Scree.Loom (mid P B))(q q':Chi)(l:ℕ)(x d b β:ℝ)(Y:Rill.Arch G e):Prop:=Y.val=(Girt.YF G U C q' b (u ▸ M.park) (M.V,R) (M.sent x T q d l β,L), C (M.sent x T q d l β,L))
structure AcX (l:ℕ)(x:ℝ)(r:ℕ)(Ω:Ride S)(E:Support (Domain N B)):Prop where
 cup:Lattice.halo ((l+70)*radiusB x) E⊆bay Ω
 ports:∀ X:Support (Domain N B),Lattice.halo ((l+90)*radiusB x) X⊆bay Ω→Lattice.halo (20*radiusB x) X⊆ E
lemma skyC : AcX S l x r Ω O:= ⟨erosion_c ..,fun _ h=> erosion_b _ _ h (by simp_rw [Nat.add_mul]; omega)⟩
variable {F:Support (Domain N B)}(f:PaneL M F x s b (M.sent x T q d l β))(v:F⊆ bay Ω)(p:AcX S l x r Ω F)
omit v
variable (Q:Finset (Kite S r))(hp:∀ i∈Q,Lattice.halo ((l+90)*radiusB x) (Eire.frameP S i)⊆ bay Ω)(hm: M.key=cook S Q)
local notation "D₁"=> M.key
lemma way_g (P: Support (Domain N B))(h:∀ i∈Q,(stem S i.1) ⊆ P)(u:D₁=cook S Q)(a:ℕ)(w:a≤r): M.key.dome a⊆ P:=by
 rw [u,palm_v,wears,biUnion_biUnion]; apply biUnion_subset.mpr; intro i t; apply (Subset.trans _ (h i t)); rw [stem,palm_v]; intro y z; obtain ⟨j,t,v⟩:=mem_biUnion.mp z; exact mem_biUnion.mpr ⟨j,t,chilling w (Subset.refl _) v⟩
include u f p hp hm
lemma watt (v:1000≤ radiusB x)(z:30*B0≤ r)(t:s≤e) (P':Roof (mid N B) s w k U)(K':Roof (mid P B) s a k' C)(hk:k'+k≤B0)(h:b<firstRadius SU.group)(hc:0<b)(he:Clan G S (T:=T) u R L M U C q q' l x d b β Y)(l0:pureK S Q): HullK S (20*B0) Q Y.val.1.1 Y.val.2 e:=by
 constructor; omega; intro K hx; let A:=M.key.dome (20*B0+12); have hY(K:ℕ)(pK:K≤r): M.key.dome K⊆ F:=by
    apply way_g S Q F _ hm K pK; intro i t; exact (frame_s ..).trans ((halo_subset _ _).trans (p.ports _ (hp i t))) -- tune
 apply Rill.safeT M.key _ _ _ A (Subset.refl _); swap; · rw [hm,cooked S _ l0]; exact hx
 · intro i w t; unfold Clan at he; -- rw Mord
   have hh:= beam_l G u q' f K' P' hk v hc h i t (foster w (hY _ (Nat.le_refl r)) (by omega)) R L -- foster r+ may need ≤r; r -D≥ B (hk)! choose hp.
   rw [he]; exact hh.symm
 omega; exact Y.property.1.fg; exact Y.property.2
end YM.CF.Eire
