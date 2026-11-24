import Taffeta.Stigma
import Rods.Fold
import YM.SU5.FiniteGaugeData.Tower.Baggage
import YM.SU5.FiniteGaugeData.Pannier.FeastDay
set_option autoImplicit false
set_option maxHeartbeats 550000
set_option synthInstance.maxSize 28000
set_option quotPrecheck false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower
open Function Filter Metric NormedSpace Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Heat Fock Analysis SlabMark
namespace Calico
open Py.Dyad Work.E08 AnalyticBridge.VerifiedReset StressFlux PlaqAxes
variable {n:Side}(o:Cover)(q:ℝ)(D:BudgetPoint)
def Tch(p:Face ℤ):Finset Cover:= (visits p.1 (square p.2.val.1 p.2.val.2)).toFinset
def bands(o:Cover)(r:ℕ):Finset Cover:=(Lattice.box r).image (fun x=>x+nodeC o)
def freeze (p:Face ℤ):Face (Per (More n)):= (wrap (More n) p.1,p.2)
open StressFlux
private lemma handle (a:Cover)(l:Walk): ((visits a l).map (wrap (More n)))= visits (wrap (More n) a) l:=by induction l generalizing a with|nil=>rfl|cons t l ih=>simp [visits,ih,wrap_vec]
lemma Vag (p:Face ℤ): (Tch p).image (wrap (More n)) = touched (freeze p):=by unfold Tch touched; ext i; simp [←handle p.1,freeze] --←handle p.1 under simp? expects syntaxes
lemma scarf (r:ℕ): (bands o r).image (wrap (More n))=Lattice.halo r {node (wrap n o)}:=by
 classical
 ext i; rw [bands,image_image,mem_image,node_of]; dsimp only [Function.comp_apply]
 constructor; · rintro ⟨p,a,rfl⟩; rw [map_add]; exact halo_spec.mpr ⟨_,mem_singleton_self _,separation_box_add _ a⟩
 rintro e; obtain ⟨j,h,q⟩:=halo_spec.mp e; rw [mem_singleton] at h; subst j; let y:=wrap (More n) (nodeC o)
 exact ⟨Lattice.lift (i-y),lift_mem_box q,by rw [map_add,wrap_lift]; exact sub_add_cancel i y⟩
def touchC (p:Face ℤ)(o:Cover):Prop:=¬Disjoint (bands o 10) (Tch p)
-- qC on cover.All plates touching finite halo.Stays bounded
lemma shiftF(p:Face ℤ)(y:Cover)(h:y∈ Tch p): y-p.1∈ Lattice.box 4:=by -- general visits bound _ needed.
 simp only [Tch,List.mem_toFinset,square,visits,List.mem_cons, List.not_mem_nil, or_false,Step.vec_neg,Step.vec_pos] at h
 rw [box_test]; rcases h with x|x|x|x|x <;> subst y <;> constructor <;> intro i <;> simp [step,Pi.single_apply] <;> split_ifs <;> omega -- W
#check Lattice.visits
lemma touch_fill(i:Face (Per (More n)))(y:Cover)(p:wrap (More n) y∈touched i):∃ j:Face ℤ,freeze j=i ∧ y∈ Tch j:=by
 let e:Face ℤ:=(Lattice.lift i.1,i.2)
 have a: freeze (n:=n) e =i:=Prod.ext (wrap_lift _) rfl
 rw [←a,←Vag] at p; obtain ⟨k,h,b⟩:=mem_image.mp p
 refine ⟨(e.1+(y-k),e.2),?_ ,?_⟩
 · have t:wrap (More n) (y-k)=0:=by rw [map_sub,←b,sub_self]
   rw [←a]; unfold freeze; dsimp only; rw [map_add,t,add_zero]
 have g(x d:Cover)(w:Walk): ((visits x w).map (fun u=>u+d))=visits (x+d) w:=by induction w generalizing x with|nil=>rfl|cons i w ih=>simp only [visits,List.map_cons,ih,add_right_comm]
 unfold Tch; dsimp only; rw [List.mem_toFinset,←g]; exact List.mem_map.mpr ⟨_,List.mem_toFinset.mp h,add_sub_cancel ..⟩
-- tune add_sub
lemma frame_freeze (p:Face ℤ)(x:Pane n):faceValue (onC n x) p=faceValue x (freeze p):=by unfold onC faceValue; rw [travel_at,add_zero]; rfl
abbrev disc(o:Cover)(D:BudgetPoint)(X:LinksC):Prop:=∀ i:Face ℤ, touchC i o → SU.group.chord (faceValue X i)<D.threshold
lemma disc_cash(X:Pane n): disc o D (onC n X) ↔ pingS D.threshold (lease_H (wrap n o)) X:=by
 constructor
 · rintro h i t; rw [lease_H,←scarf] at t; obtain ⟨y,u,v⟩:=not_disjoint_iff.mp t; obtain ⟨z,p,rfl⟩:=mem_image.mp u
   obtain ⟨j,rfl,w⟩:=touch_fill i z v
   rw [←frame_freeze]; exact h j (not_disjoint_iff.mpr ⟨z,p,w⟩)
 rintro h i t; rw [frame_freeze]; apply h; obtain ⟨y,u,v⟩:=not_disjoint_iff.mp (t : ¬ Disjoint _ _); rw [lease_H,←scarf,←Vag]; exact not_disjoint_iff.mpr ⟨wrap (More n) y,mem_image_of_mem _ u,mem_image_of_mem _ v⟩
#check Py.Dyad.cameo
#check CF.Compass.decor
end Calico
end YM.CF.Buffered.Afterglow.Tower
