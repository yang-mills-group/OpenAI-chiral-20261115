import YM.SU5.Reconstruction.LinkMeasures.Socket
import YM.SU5.Reconstruction.LinkMeasures.MorningRoom
set_option autoImplicit false
set_option synthInstance.maxSize 30000
set_option maxRecDepth 6000
set_option maxHeartbeats 400000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Satori
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Heat Fock Analysis Tapestry
/-! # No hypothesis of regularity of the display kernel of the input link pairs.
Invariant material on local gauge rotations! Need use the actual Nimbus U. -/
open VolumeCape VolumeCape.Atlas VolumeCape.Mesh VolumeCape.Cane VolumeCape.Read
variable (S P:Finset Cover)(g:Cover→SU.E)

noncomputable def glaze (a:Aerial S)(e:LocalEdges S) : SU.E:= g e.val.1*a e*(g (e.val.1+step e.val.2))⁻¹
noncomputable def rotAct: ScoreBook S → ScoreBook S:= Prod.map (glaze S g) (glaze S g)
@[fun_prop] lemma rot_c: Continuous (rotAct S g):= by
 have t:Continuous (glaze S g):=by unfold glaze; refine continuous_pi fun i=> ?_; fun_prop
 exact t.prodMap t
lemma rot_price (U V: LinksC): rotAct S g (here S (U,V))=here S (Lattice.gauge g U,Lattice.gauge g V):=rfl
variable (C:Side)(Z:ℕ→ ℝ)
local notation "I₀"=> porch C P
local notation "H₀" => Hall C P
noncomputable def transportL (y : (((porch C P):Type) × Axis→SU.E)) : (((porch C P):Type) × Axis→SU.E) := fun e=> g e.1.val*y e*(g (e.1.val + step e.2))⁻¹
noncomputable def transportF (y : (((porch C P):Type)→ SU.E)) : (((porch C P):Type)→ SU.E) := fun e=> y e*(g e.val)⁻¹
noncomputable def reShip (x:Hall C P): Hall C P := Prod.map (transportL P g C) (transportF P g C) x
lemma tailor_preserving: MeasurePreserving (reShip P g C) (Common.law C P) (Common.law C P):=by
 let u(I:Type):=fun _:I=> SU.group.probHaar
 have p:MeasurePreserving (transportL P g C) (Measure.pi (u _)) (Measure.pi (u _)):= by
    exact measurePreserving_pi _ _ (f:=fun (e:((porch C P):Type)×Axis) y=> g e.1.val*y*(g (e.1.val+step e.2))⁻¹) fun i=> (measurePreserving_mul_right _ _).comp (measurePreserving_mul_left _ _)
 exact p.prod (measurePreserving_pi _ _ (f:=fun (e:(porch C P:Type)) (y:SU.E)=>y*(g e.val)⁻¹) (fun i=> measurePreserving_mul_right _ _))
local notation "rV" => reShip P g C
lemma gauged_all (x:Hall C P) (e: Edge Cover)(h:e.1∈ I₀) : Common.strips C P (rV x) e= Lattice.gauge g (Common.strips C P x) e:=by unfold Common.strips; rw [dif_pos h]; unfold Lattice.gauge; simp only [dif_pos h]; rfl
lemma frame_all(x:Hall C P)(y:Cover)(h:y∈ I₀) : Common.frame C P (rV x) y= Common.frame C P x y*(g y)⁻¹:=by unfold Common.frame; rw [dif_pos h,dif_pos h]; rfl
lemma tapDisplay (x:Hall C P)(u: Courses C P) (a:Cover)(i:Axis)(h:a∈ P) :
    display C Z (u ⟨a,h⟩) (translate a (Lattice.gauge (Common.frame C P (reShip P g C x)) (Common.strips C P (reShip P g C x)))) i=display C Z (u ⟨a,h⟩) (translate a (Lattice.gauge (Common.frame C P x) (Common.strips C P x))) i:=by
 refine Cane.scope0 _ _ _ _ _ ?_ _
 rintro ⟨b,j⟩ v t
 unfold Lattice.translate
 unfold Lattice.gauge; dsimp only; have vz:= porch_there C P h (show Scope (Fringe C) b from v); have tz:= porch_there C P h (show Scope (Fringe C) (b+ step j) from t); rw [add_right_comm b] at tz
 rw [frame_all P g _ x _ vz,frame_all P g _ x _ tz, gauged_all P g _ x (b+a,j) vz]; unfold Lattice.gauge; dsimp only; group
lemma gauged_out (x:Hall C P)(u:Courses C P)(e:Edge Cover)(h:e.1∈P)(p:e.1+ step e.2∈P): (Common.pairs C Z P u (rV x)).2 e=Lattice.gauge g (Common.pairs C Z P u x).2 e:=by
 unfold Common.pairs Lattice.gauge
 dsimp only [Pi.inv_apply,dif_pos h]
 have ht:=tapDisplay P g C Z x u e.1 e.2 h; unfold Lattice.gauge at ht
 rw [dif_pos h,dif_pos h,ht, frame_all P g _ x _ (porch_here C P h),frame_all P g _ x _ (porch_here C P p)]; group
variable (h:S⊆P)
include h
lemma gauge_all (x:Hall C P)(u:Courses C P) : here S (Common.pairs C Z P u (reShip P g C x))= rotAct S g (here S (Common.pairs C Z P u x)):=Prod.ext (funext fun y=> gauged_all P g C x y.val (porch_here C P (h ((localEdges S _).mp y.property).1))) (funext fun y=> gauged_out P g C Z x u y.val (h ((localEdges S _).mp y.property).1) (h ((localEdges S _).mp y.property).2))
omit h
variable (Λ:Preparation)(l:ℕ)
local notation "P₀" => plaza (Λ:=Λ) S
local notation "C₀" => (VolumeCape.Dream.plot l).C
local notation "Z₁" => (VolumeCape.Dream.plot l).K
lemma pull_preserving (u:Courses C₀ P₀): MeasurePreserving (rotAct S g) (pull S Λ l u) (pull S Λ l u):=by
 let f:= here S ∘ (pairs C₀ Z₁ P₀ u); have t:Measurable f:= (here_c S).measurable.comp (Common.pairs_m ..); have h:MeasurePreserving f (Common.law C₀ P₀) (pull S Λ l u):= ⟨t,rfl⟩
 refine ⟨(rot_c S g).measurable,?_⟩
 nth_rw 1 [←h.map_eq]
 rw [Measure.map_map (rot_c ..).measurable t, show (rotAct S g) ∘ f=f ∘ reShip P₀ g C₀ from funext fun x=> (gauge_all S P₀ g C₀ Z₁ (liner_here ..) x u).symm]; exact (h.comp (tailor_preserving ..)).map_eq
lemma physically_rot : MeasurePreserving (rotAct S g) (actual S Λ l) (actual S Λ l):=by
 refine ⟨(rot_c ..).measurable,?_⟩
 unfold actual; rw [Measure.map_finset_sum'  (m:=pull S Λ l) (rot_c S g).measurable.aemeasurable]; exact Finset.sum_congr rfl fun i _=> (pull_preserving S g Λ l i).map_eq

end YM.CF.Buffered.Afterglow.Satori
#print axioms YM.CF.Buffered.Afterglow.Satori.physically_rot
