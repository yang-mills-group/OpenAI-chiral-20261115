import YM.SU5.Registration.Rise.Commerce
import YM.SU5.Diva.Jewel
/-!
# Sell the Sonnet straight trains on the chosen path
Uses Papal.many_price (actual MANY path estimates) as an inspiration; here still
on actual Dress. We redo its `scatter` & ice argument at the needed long line
with arbitrary spectator pricing in view.
-/
set_option autoImplicit false
set_option maxHeartbeats 320000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Py
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
local notation "G5"=>SU.group
open Cascade
open Fief
open Yaw Pig
open Wray
open Lich.Muster Push.AbsoluteSums
open Iva Eire
open Trees Footprint Iva Eire
open Jade
open Oath Feu Feu.Corset Nor
open Chaff Gloss Maize Tye RP RP.Str
open Brace
namespace Rate
open Pitching Focus CF.Mint
namespace LocalLimit
open Preparation
variable {P:Preparation}{l:ℕ}(Y:Course P (VolumeCape.Dream.Nimbus l))
variable {h z:ℝ}
open Buffered
open CF.Pannier.Damask
open YM.CF.Velvet
open Pannier
namespace Papal
local notation "ℶ" => hat P.R.L P.x
local notation "💠" => P.K.j
open Lamour.Bridge CF.Pannier.Chancel
variable {Z θ b v t ε R C ξ:ℝ} {n a y z' k:ℕ}
universe u0
open Buffered Afterglow Journey
open scoped ComplexOrder
open CF.Pannier.Chancel
open CF.Pannier.Chancel.Cliplet
variable (H:Real.exp 1≤ P.x)
open YM.CF.Lamour.Bridge.Celeste
open YM.CF.Lamour.Bridge.Celeste.Morn
open YM.CF.Lamour.Bridge YM.CF.Velvet

namespace LaceLayer
open Yoke Tower Tower.SlabMark Tower.SlabMark.ClockBooking Sonnet
variable {N: Side}{J r p d:ℕ}{M:Tulip.Male}{D σ:ℝ}

private lemma halo_anchor {T:Finset (Seat N)}{j:Axis}
    (p:cows j T d)(u:0∈T): Packing.NativeRoll (N:=N) j T (- (d:ℤ)) (d:ℤ):= by
 intro x t; obtain ⟨k,v⟩:=p; obtain ⟨y,y0,y1,hy⟩:= v x t; obtain ⟨w,w0,w1,hw⟩:= v 0 u
 exact ⟨y-w,by omega,by omega,by change (↑w:Per (More N))=0 at hw; rw [Int.cast_sub,hy,hw,sub_zero]⟩

private lemma to_halo {x:Seat N} (k:ℕ){T:Finset (Seat N)} (h:x∈T): x ∈ Lattice.halo k T:= halo_spec.mpr ⟨x,h,(separation_self _).le.trans (Nat.zero_le k)⟩
private lemma inside_halo {S:List (Sonnet N)}{p:ℕ}{x:Seat N}(u:x ∈ Broad p S): ∃ A∈ S,x ∈ Lattice.halo p A.S:=by
 induction S with
 | nil => simp at u
 | cons h t ih=>
   rcases mem_union.mp (show x∈ Lattice.halo p h.S ∪ Broad p t from u) with z|z
   · exact ⟨h,List.mem_cons_self,z⟩
   obtain ⟨s,f,q⟩:=ih z; exact ⟨s,List.mem_cons_of_mem _ f,q⟩

def hull (j:Axis) (r d p:ℕ) (M:Tulip.Male)(ε ξ C σ:ℝ)(u:HaloTw J N): Packing (Sonnet.x (N:=N)) j N 1:= {
 footprint A:= Lattice.halo p A.S
 turn s A:= A.twistL j s
 admissible:= Sonnet.Cost J r d M ε ξ C σ
 still := fun _ _ t=> t.reflect u _ _
 turns := fun _ _=> coal_halo ..
 reflects x s:= by rw [one_mul]; rfl
 }
lemma booth_lease {j:Axis}{s i w:ℕ}
    (f:Weaver)(o:Cover)(g:wrap (More (Papal.count Y s i)) o=0) -- o actually zero in application; no uniformity needed here
    (T:Finset Cover)(h:HaloTw P.K.j (Papal.count Y s i))(pN:ℕ)
    (V:Sonnet.Cost P.K.j r d M ε ξ C σ (⟨f (Papal.count Y s i), dBook (Papal.count Y s i) T,wrap _ o⟩:Sonnet (Papal.count Y s i)))
    (u: ((↑(2*(r+pN)+(pN+1):ℕ)):ℤ) ≤ (Tower.SlabMark.ruler P.block)*(w:ℤ)) :
    ∃ A:Sonnet (Papal.count Y s i), Tower.SlabMark.ClockBooking.Leased Y H s i (hull j r d pN M ε ξ C σ h) (fun _=>- ↑(2*(r+pN):ℕ)) (4*(r+pN)) (pN+1) (relocate (tent Y H) j (w:ℤ) (household (tent Y H) f)) 0 (ruler P.block*((w+w:ℕ):ℤ)) [A]:=by
 let N:= Papal.count Y s i; let b:=ruler P.block * (w:ℤ); let K:=tent Y H; let y:=household K f; let J:Sonnet N:= ⟨f N,dBook N T,wrap _ o⟩
 let W:=hull j r d pN M ε ξ C σ h; let D:=2*(r+pN)
 have ht:0∈ Lattice.halo pN J.S:= to_halo _ (by rw [← g]; exact V.slotT)
 let z(i':Axis):= - (D:ℤ)
 have hf:Tower.SlabMark.ClockBooking.Leased Y H s i W z (4*(r+pN)) (pN+1) y (-b) b [J] :=by
    refine ⟨⟨fun r' u=> List.mem_singleton.mp u |>.symm ▸ V,fun x o u' v' => ?_,fun i' _ x o u' v' => ?_, List.pairwise_singleton ..⟩,?_⟩
    · obtain ⟨c,t,q,g⟩:= halo_anchor (from_block (w:=j) J V) ht _ ((List.mem_singleton.mp o) ▸ v'); exact ⟨c,by unfold b; omega,by unfold b; omega,g⟩
    · obtain ⟨c,t,q,g⟩:= halo_anchor (from_block (w:=i') J V) ht _ ((List.mem_singleton.mp o) ▸ v'); exact ⟨c,t,by unfold z D; omega,g⟩
    rw [List.map_singleton,List.prod_singleton]
    apply congr'' f _ _ (terrain Y H (Y.ir i) s)
 let t:= hf.forward Y H s i W (w:ℤ); unfold b at t
 rw [one_mul,add_neg_cancel,show ruler P.block * (w:ℤ)+ ruler P.block * (w:ℤ)=ruler P.block * ((w+w:ℕ):ℤ) from by rw [Nat.cast_add,mul_add]] at t;
 exact ⟨W.turn (Tower.SlabMark.gaugeT K (w:ℤ)) (W.turn 0 J), t⟩
where congr'' (F: Weaver)(A B:Side)(h:A=B): Tower.ship h (F A)= F B:=by subst B; rfl

lemma hut_fiber {j:Axis}{L:List (Sonnet N)}(u:HaloTw J N){h:Cover}{B:ℕ}{l l':ℤ}(g:(hull j r d p M ε ξ C σ u).Stretch h B (p+1) l l' L): Sylvan J r d p M ε ξ C σ L ∧ ∀ i:Axis,i≠j → cows i (Broad p L) B:=by
 refine ⟨⟨g.goal,g.clear.imp fun {x z} G t f i u'=>?_⟩,fun i v=>⟨h i,fun x v'=>?_⟩⟩
 · exact (Nat.le_mul_of_pos_left (p+1) (by decide : 0<(2:ℕ))).trans (G t (to_halo p f) i (to_halo p u'))
 obtain ⟨r,h,g'⟩:= inside_halo v'; exact g.other i v r h x g'

end LaceLayer
end Papal
end LocalLimit
end Rate
end YM.CF.Py
