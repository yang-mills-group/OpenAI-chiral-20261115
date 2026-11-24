import YM.CF.Stake.Pole
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Stake
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
open Tye Lich
variable{N P B:Side}{S:StepData (Domain N B) (Domain P B)}{T: Tube SU.group S}{K:Teller SU.group}{G:Ratio (mid N B) (mid P B)}{R:Patch}{L:ChartRatio SU.group}
variable {d e η t z g b c A B':ℝ} {j k k' m n l:ℕ}
variable (V:Grace K R L) (O:Acorn.Repair K.j){U:Grasp V.U B d}(W:GivenX V U)
open Lich.Muster Lor
open Jet Vol Rel
local notation "G5"=>SU.group
variable {x y β:ℝ}(p:BudgetPoint){t₀ v v₁ p1 p2 p3 p4:ℝ}
local notation "SN"=> Site (Domain N B)
open Cascade
open Fief
variable {X: Interest (mid N B)}{Y:Interest (mid P B)}{U: Grasp V.U B d}{W:GivenX V U}
variable (M: Sheep V U W G Y X k n A)
local notation "sN"=>mid N B
local notation "θo"=> Hest.Budget R.L R.odd_side Y.P.den X.P.den G Y.M K.j
local notation "Δ"=> shipA G U Y.M Y.P.den Y.I X.I
local notation "TΦ"=> (Thera.yet_one)
variable (F: Pilot)(q:Chi){S' D':ℕ}
-- expose program β for ALL basis. Output C history ζ trial independent. avoid choices depend on post path.ClockB. Stencil projection sizes. Integrated maturity of L.
open Corne
open AnalyticBridge.GaussianFieldAlignment Locations Channels Orthogonal Tensor
variable (Z Z':Monk SU.group S)(s:Signed)(x':Site (Domain N B))
local notation "d_"=> Domain N B
local notation "d'"=> Domain P B
local notation "iM"=>affine s x'
local notation "jp"=> S.ratio.embed x'
local notation "M'"=> sendEdge s x'
local notation "N'"=> sendEdge s (S.ratio.embed x')
lemma pin_h (j:Bond d_)(X:Support d_)(p:j.1∈ X):(M' j).1∈(halo 1 X).image (affine s x'):=by
 have ht: pinPos j⊆ halo 1 X:=by intro i l; simp only [pinPos,mem_insert,mem_singleton] at l; cases l with | inl h=>exact h ▸ halo_subset _ _ p| inr h=>exact h ▸ halo_spec.mpr ⟨_,p,Work.E01.sep_step_le ..⟩
 exact image_subset_image ht ((pin_map s x' j) ▸ (show (M' j).1∈ pinPos (M' j) from mem_insert_self ..))
lemma parent_h (i:Bond d')(w:Site d_)(v:separation w (S.ratio.parent i.1)≤l): separation (affine s x' w) (S.ratio.parent (N' i).1) ≤ l+2:=by
 have hp:=pin_h (N:=P) (B:=B) s (S.ratio.embed x') i {i.1} (mem_singleton_self _)
 obtain ⟨g,u,v'⟩:= mem_image.mp hp; obtain ⟨j,t,h⟩:= halo_spec.mp u; rw [mem_singleton.mp t] at h; have he:= Work.E04.parent_separation S.ratio i.1 g; rw [← v',parent_map, affine,affine,separation_translate,separation_signed]; exact (separation_triangle w (S.ratio.parent i.1) _).trans (by omega)
lemma pin_X (X:Support d_)(O:Support d_)(v:X.image (affine s x')⊆O)(V W:Config G5 d_)(e:Agrees O V W)(j:Bond d_)(p:pinPos j ⊆ X): pull s x' V j=pull s x' W j:=by
 have hx: pinPos (M' j)⊆ O:=by rw [pin_map]; exact (image_subset_image p).trans v
 rw [read_back,read_back,e _ (hx (mem_insert_self ..)) (hx (mem_insert_of_mem (mem_singleton_self _)))] -- syntax arguments
variable {E C:Support (Domain N B)}(h: Duo SU.group S Z Z' E)(u:(halo 1 C).image (affine s x') ⊆ E)(r:Kind S (Z.park,Z.k) (Z'.park,Z'.k) E)
local notation "Y'"=> clue S s x' Z
local notation "C_"=> clue S s x' Z'
include h r u
set_option linter.unusedVariables false in
set_option maxHeartbeats 1600000 in
lemma ctu (i:Site d')(p':S.ratio.parent i∈ C) :(Y').park.up i=(C_).park.up i:=by
   let b:=affine s jp i
   change S.ratio.parent i∈ C at p'
   change (Z.park.up b).rotate s⁻¹=(Z'.park.up b).rotate s⁻¹
   have t:S.ratio.parent b∈E:=Eq.mpr (congrArg (fun i:Site d_=>i∈E) (parent_map (S:=S) s x' i)) (u (mem_image_of_mem _ (halo_subset _ _ p')))
   exact congrArg (fun i:Lattice.Step=>i.rotate s⁻¹) (r.up b t)
#print axioms ctu
lemma ctv (i:Site d')(p':S.ratio.parent i∈ C) :(Y').park.height i=(C_).park.height i:=by
   let b:=affine s jp i
   have hy: S.ratio.parent b∈E:=Eq.mpr (congrArg (fun i:Site d_=>i∈E) (parent_map (S:=S) s x' i)) (u (mem_image_of_mem _ (halo_subset _ _ p')))
   exact r.ht _ hy
#print axioms ctv
lemma cts (i:Site d_)(p':i ∈ C): ((Y').k.1 i)=((C_).k.1 i):=by
   apply (S.patch.orient s).injective
   change S.patch.orient s ((Channels.ticket s x' Z.k).1 i)= S.patch.orient s ((Channels.ticket s x' Z'.k).1 i)
   have he(Y:Monk SU.group S): S.withinSites s x' (Channels.ticket s x' Y.k).1=Y.k.1:=congrArg Prod.fst ((S.withinChoice s x').apply_symm_apply Y.k)
   have hx(t:Monk SU.group S): S.patch.orient s ((Channels.ticket s x' t.k).1 i)=t.k.1 (affine s x' i):=(S.port_site s x' _ i).symm.trans (congrFun (he t) _)
   have hv: Z.k.1 (affine s x' i)=Z'.k.1 (affine s x' i):= r.site (affine s x' i) (u (mem_image_of_mem _ (halo_subset _ _ p')))
   exact (hx Z).trans (hv.trans (hx Z').symm)
#print axioms cts
lemma ctb (i:Bond d_)(p':i.1∈C): (Y').k.2 i=(C_).k.2 i:=by
   apply (S.patch.offset s).injective
   change S.patch.offset s ((Channels.ticket s x' Z.k).2 i)= S.patch.offset s ((Channels.ticket s x' Z'.k).2 i)
   have he(Y:Monk SU.group S): S.withinBond s x' (Channels.ticket s x' Y.k).2=Y.k.2:=congrArg Prod.snd ((S.withinChoice s x').apply_symm_apply Y.k)
   have hx(t:Monk SU.group S): S.patch.offset s ((Channels.ticket s x' t.k).2 i)= t.k.2 (sendEdge s x' i):=(S.port_bond s x' _ i).symm.trans (congrFun (he t) _)
   have hv:Z.k.2 (sendEdge s x' i)=Z'.k.2 (sendEdge s x' i):=r.edge (sendEdge s x' i) (u (pin_h s x' i C p'))
   exact (hx Z).trans (hv.trans (hx Z').symm)
#print axioms ctb
lemma clip_t : Kind S ((Y').park,(Y').k) ((C_).park,(C_).k) C:=by

 refine ⟨fun i p=>ctu Z Z' s x' h u r i p,fun i p=>ctv Z Z' s x' h u r i p, fun i p=>cts Z Z' s x' h u r i p,fun i p=>ctb Z Z' s x' h u r i p⟩
set_option linter.unusedVariables false in
set_option maxHeartbeats 1600000 in
lemma clip_u : Duo SU.group S (clue S s x' Z) (clue S s x' Z') C:=by
 have ht:= clip_t Z Z' s x' h u r; have hg:(C.image (affine s x'))⊆ E:= (image_subset_image (halo_subset 1 C)).trans u
 have hu(i:Bond d')(p: Next.SectorChange.points S i ⊆ (C:Set _)):Next.SectorChange.points S (N' i) ⊆ (E:Set _):=by rw [Tensor.moves_points]; exact fun i ⟨y,h,r⟩=> r ▸ hg (mem_image_of_mem _ (p h))
 constructor
 · constructor
   · intro i p; change i∈(Locations.book _ _ _).place↔i∈ (Locations.book _ _ _).place; rw [place_map,place_map]; exact h.road _ (hg (mem_image_of_mem _ p))
   · exact ht.site
   · exact fun i p=> ht.edge i (p (mem_insert_self ..))
   · exact KinT ht
   · exact fun i p k=>pin_X _ _ C E hg Z.V Z'.V h.view i (insert_subset p (singleton_subset_iff.mpr k))
   · intro i p; change pull s _ Z.U i=pull s _ Z'.U i; rw [read_back, read_back,h.data _ (hu _ p)]
   · intro i p; let P:=fiber s x' Z.V S; let Q:=fiber s x' Z'.V S; change Tensor.lifting P (diagram s x' S) Z.z i= Tensor.lifting Q _ Z'.z i; have hp: P i= Q i:=by
        let U:= Next.SectorChange.points S (N' i); let z:= N' i
        have he:Precision.replica S.ratio Z.V z=Precision.replica S.ratio Z'.V z:=by
           unfold Precision.replica; split; rfl
           next q=> have hh: S.ratio.parent (z.1+step z.2)= S.ratio.parent z.1+step z.2:=crossing z q; exact h.view _ (hu i p (show _∈U from Set.mem_insert ..)) (hu i p (hh ▸ (show _∈ U from Set.mem_insert_of_mem _ rfl)))
        change Channels.scatter s jp _ _= Channels.scatter s jp _ _; unfold Channels.scatter; split; swap; exact rfl
        apply LinearIsometry.ext; intro v; change -SU.group.adjoint _ _= -SU.group.adjoint _ _; rw [show Precision.replica S.ratio Z.V _= _ from he]
     rw [Tensor.lifting_apply,Tensor.lifting_apply,hp]; exact congrArg (Q i) (h.color _ (hu i p))
 · intro i p; have hx: ¬ Disjoint (startPos S (shiftFaces s jp i)) E:=by rw [start_map]; obtain ⟨z,v,k⟩:= Finset.not_disjoint_iff.mp p; exact not_disjoint_iff.mpr ⟨_,mem_image_of_mem _ v,hg (mem_image_of_mem _ k)⟩
   simp only [clue,Locations.book, Finset.mem_map_equiv,Equiv.symm_symm]; exact h.cost _ hx
 · intro i p; have hx: ¬ Disjoint (pinPos (M' i)) E:=by rw [pin_map]; obtain ⟨z,v,k⟩:= Finset.not_disjoint_iff.mp p; exact not_disjoint_iff.mpr ⟨_,mem_image_of_mem _ v,hg (mem_image_of_mem _ k)⟩
   simp only [clue,Locations.book, Finset.mem_map_equiv,Equiv.symm_symm]; exact h.aisles _ hx
 intro i p; simp only [clue,Locations.book, Finset.mem_map_equiv,Equiv.symm_symm]; exact h.flags _ (hg (mem_image_of_mem _ p)) -- implicit
end YM.CF.Stake

#print axioms YM.CF.Stake.clip_t
#print axioms YM.CF.Stake.clip_u
