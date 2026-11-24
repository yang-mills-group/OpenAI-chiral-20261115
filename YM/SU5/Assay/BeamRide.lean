import YM.SU5.Assay.Beam
set_option maxHeartbeats 400000
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 5000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common Ballad Cordial
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
open Germ Alliance
open Lamour.Bridge.Celeste
open Designs Twah Prototype
open YM.Stationary (Gaia) -- tune
open CF.Onyx (riseX moor)
open Lamour.Bridge.Celeste.Morn
namespace Spine
open Aria Set
open Six

variable {P:Spine}{f g:P.Test}{S T D:Finset Cover}{s t:ℕ}{W:Bool}
local notation "K"=> P.calibration

/-!
# Keep the genuine charge through promotion at resolution cost, pose, and reflection
-/
lemma Beam.turned (p:f∈P.Beam s D W)(i:Axis):
    P.reflectTest i f∈P.Beam s (reflectedBox i 0 D) W:=by
 let R:=P.Beam s (reflectedBox i 0 D) W
 refine Submodule.span_induction (p:=fun f _=>P.reflectTest i f∈R) (fun f h=>?_) (by rw [map_zero];exact R.zero_mem)
    (fun _ _ _ _ x y=>by rw [map_add]; exact R.add_mem x y) (fun z f _ x=>by rw [P.scale_mirror]; exact R.smul_mem _ x) p
 obtain ⟨S,T,V,U,a,b,t,v,u,j,l,z,c,d,rfl⟩:=h
 rw [show P.reflectTest i (a*b)=P.reflectTest i a*P.reflectTest i b from Subtype.ext (mirror_times ..)]
 exact enterBeam (Finset.union_subset (Finset.image_subset_image (Finset.subset_union_right.trans t))
    (Finset.image_subset_image (Finset.subset_union_left.trans t)))
    (Finset.image_subset_image v) (Finset.image_subset_image u) ((P.pin_reflect _ _ _ _ j).symm) (P.pin_reflect _ _ _ _ l)
    (mirror_dressed K W _ _ _ _ _ z) (P.mirror_keeps _ _ c) (P.canFlip _ _ d)
lemma Apron.Beams.kiss {B:P.Apron}(v:B.Beams W)(j:Axis): (B.kiss P j).Beams W:=
 Beam.turned v j

lemma Beam.shift (p:f∈P.Beam s D W)(i:Axis)(n:ℤ):
   P.shifts i n f∈P.Beam s (plow K i n D) W:=by
 let R:=P.Beam s (plow K i n D) W
 refine Submodule.span_induction (p:=fun f _=>P.shifts i n f∈R) (fun f h=>?_) (by rw [map_zero];exact R.zero_mem)
   (fun _ _ _ _ x y=>by rw [map_add]; exact R.add_mem x y) (fun z f _ x=>by rw [map_smul]; exact R.smul_mem _ x) p
 obtain ⟨S,T,V,U,a,b,t,v,u,j,l,z,c,d,rfl⟩:=h
 rw [map_mul]
 exact enterBeam (Finset.union_subset (Finset.image_subset_image (Finset.subset_union_left.trans t))
    (Finset.image_subset_image (Finset.subset_union_right.trans t)))
    (Finset.image_subset_image v) (Finset.image_subset_image u)
    (P.pin_relocate _ _ _ i n j) (P.pin_relocate _ _ _ i n l)
    (relocate_dressed K W _ _ _ i n z) (P.shifts_keep i n c) (P.shifts_support i n _ d)
lemma Beam.sail (p:f∈P.Beam s D W)(l:List Axis)(r:Cover):
    P.cruise l r f∈P.Beam s (P.placeSet D l r) W:= by
 induction l with
 | nil=> exact p
 | cons i l h=>rw [P.cruise_step,AlgHom.comp_apply]; exact Beam.shift h _ _

local notation "vol" => volumeAround P.par P.width
lemma pin_glue (v: Disjoint (P.pinFoot s S) (P.pinFoot s T)) : Detached P.par P.width S T:= by
 rw [P.usual_footprint,P.usual_footprint] at v; exact Reconstruction.separated_in_foot _ _ _ _ _ v
lemma far_woven (a:f∈bay K S true)(b:g∈bay K T true)(p:Disjoint (P.pinFoot s S) (P.pinFoot s T))(n:ℕ):
   P.conveying s n (f*g)=P.conveying s n f * P.conveying s n g:=by
 apply Subtype.ext
 exact woven_product _ P.large P.history.circuit s n ((Tapestry.locates ..).mp a) ((Tapestry.locates ..).mp b) (pin_glue p)
lemma woven_bay {f:P.Test}(s:ℕ)(h:f∈bay K S true)(n:ℕ):
    P.conveying s n f∈bay K (vol n S) true:= (proceeds _ _ P.history.circuit s n ((Tapestry.locates ..).mp h)).1
lemma Beam.age (p:f∈P.Beam s D W)(e:s≤t): P.conveying s (t-s) f ∈ P.Beam t (vol (t-s) D) W:=by
 let R:=P.Beam t (vol (t-s) D) W
 refine Submodule.span_induction (p:=fun f _=>P.conveying s (t-s) f ∈ R) (fun f h=>?_) (by rw [P.vanishes_receipt]; exact R.zero_mem)
    (fun _ _ _ _ x y=>by rw [P.later_receipt]; exact R.add_mem x y) (fun z f _ x=>by rw [P.scaled_receipt]; exact R.smul_mem _ x) p
 obtain ⟨S,T,V,U,a,b,w,v,u,j,l,z,c,d,rfl⟩:=h
 rw [far_woven ((Tapestry.locates ..).mpr (dressed_test _ _ _ _ _ w z)) d l]
 let x:S⊆V:= Finset.subset_union_left.trans w
 let y:T⊆V:= Finset.subset_union_right.trans w
 let g:=P.vol_mono (t-s)
 exact enterBeam (Finset.union_subset (g x) (g y)) (g v) (g u)
   (j.mono (P.pin_onward s t S e) (P.pin_onward s t T e)) (l.mono (P.pin_onward s t V e) (P.pin_onward s t U e))
   (P.onward W S T V s a x y z _) (P.refine_keeps s a c _) (woven_bay s d _)
lemma Apron.Beams.issue {B:P.Apron}(h:B.Beams W)(e:B.s≤t)(r:Cover):
    P.issuing t B r∈P.Beam t (P.plotSet t B r) W:=
  Beam.sail (Beam.age h e) Vacancy.ordinate r

variable (P) in
def beamAsk (s:ℕ)(f:P.Test)(M:Set Vantage)(W:Bool) : Prop:= ∃ S:Finset Cover,f∈P.Beam s S W ∧ P.pinFoot s S⊆ M
lemma beamAsk.price {M:Set Vantage}(h:P.beamAsk s f M W) : P.asked_at s f M:=
 ⟨_, Beam.bay_le h.choose_spec.1,h.choose_spec.2⟩
lemma beamAsk.fee {M:Set Vantage}(h:P.beamAsk s f M W){X:Dome P.calibration→ₗ[ℂ]ℂ}(p:Factors P.calibration X)(q:MatterWard P.calibration X∨GaugeWard P.calibration X):
 X f=0:=Beam.fee p q h.choose_spec.1
lemma beamAsk.visitor {M N:Set Vantage}(h:P.beamAsk s f M W)(u:P.asked_at s g N)(e:Disjoint M N) : P.beamAsk s (f*g) (M∪N) W:=by
 obtain ⟨U,t,w⟩:=u
 obtain ⟨S,p,v⟩:=h; refine ⟨S∪U,Beam.join p t (e.mono v w),?_⟩
 rw [P.pin_union]; exact Set.union_subset_union v w

lemma Apron.Beams.prepare {B:P.Apron}(h:B.Beams W)(q:B.s≤t)(F:SampleDose) :
  P.beamAsk t (P.prepared t B F) (P.spacePrice B F) W:=by
 let S:=P.usedGrid t F
 suffices H:∀ l:Finset Cover,l⊆S→P.beamAsk t (∑k∈l,P.activation t F k • P.issuing t B k) (P.spacePrice B F) W from H S fun _ e=>e
 intro l
 induction l using Finset.induction with
 | empty=> intro _; rw [sum_empty]; exact ⟨∅, (P.Beam t ∅ W).zero_mem,by simp [pinFoot]⟩
 | insert i l z ih=>
    intro v
    obtain ⟨U,a,e⟩:=ih ((Finset.subset_insert ..).trans v)
    let N:=P.plotSet t B i
    rw [sum_insert z]
    refine ⟨N∪U,Submodule.add_mem (P.Beam t (N∪U) W) ((P.Beam _ _ _).smul_mem _ (Beam.mono Finset.subset_union_left (h.issue q i)))
      (Beam.mono Finset.subset_union_right a),?_⟩
    rw [P.pin_union]
    exact Set.union_subset (Set.Subset.trans (P.inside_now t i B q) (Set.subset_iUnion₂_of_subset (P.meshPose t i) ((P.usedPose t F i).mp (v (Finset.mem_insert_self ..))) Set.Subset.rfl)) e
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
