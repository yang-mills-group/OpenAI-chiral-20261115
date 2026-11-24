import YM.SU5.Six.SupportPrice
import YM.SU5.Six.Extinguish
import YM.SU5.Six.SplitPredict
set_option maxHeartbeats 200000
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 2000
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
open Cheer (Narrow)
/-!
# Illuminating physically separated bodies, permanently

Allow differences of singlet signals, even if their supports *within* that
linear superposition intersect. The split must be on the probes after motion &
advancement; it is not enough to compare against tensoring old marginals at the
starting positions and resolutions.
-/
open Six
variable (P:Spine)(W:Bool)(Z:Lead.Clan)(s t:ℕ)(L:List Axis)(o:Cover)(S T D:Finset Cover)
local notation "K"=> P.calibration
local notation "A"=> P.Test
local notation "σ" X:max=>P.placeSet X L o
lemma cruise_keeps_charge {x:A} (p:x.val∈DressedPair K W S T D):
    (P.cruise L o x).val ∈ DressedPair K W (σ S) (σ T) (σ D):= by
  induction L with
  | nil=> exact p
  | cons i L h=> exact relocate_dressed K W _ _ _ i (o i) h

-- This span only records THAT the resolution price tests the given pockets, not that their
-- generation labels don't mix under motion/advance. The *representation choice* of
-- all these probes is controlled explicitly throughout. Initial labels in Aprons.
def sensing (P:Spine)(D:Finset Cover)(s:ℕ)(W:Bool) : Submodule ℂ P.Test:=
  Submodule.span ℂ {x:P.Test|∃ S T V:Finset Cover,S∪T ⊆ V∧ V ⊆ D ∧ Disjoint (P.pinFoot s S) (P.pinFoot s T) ∧
    x.val∈ DressedPair P.calibration W S T V ∧ x∈ enclave P.calibration}
def Sensor (P:Spine)(D:P.Apron)(W:Bool):Prop:= D.F∈ sensing P D.S D.s W
lemma later_receipt (F G:A): P.conveying s t (F+G)=P.conveying s t F+P.conveying s t G:=
  Subtype.ext (woven_add P.run P.large P.history.circuit s t F.property G.property)
lemma scaled_receipt (F:A)(a:ℂ):P.conveying s t (a • F)=a • P.conveying s t F:=
  Subtype.ext (woven_smul P.run P.large P.history.circuit s t F.property a)
lemma vanishes_receipt : P.conveying s t 0 = 0:= by
  have ht:= P.scaled_receipt s t (0:A) 0; simpa only [zero_smul] using ht
lemma scale_mirror (x:A)(a:ℂ)(j:Axis) : P.reflectTest j (a • x) = star a • P.reflectTest j x:= Subtype.ext (Tower.mirror_scale ..)
lemma sum_mirror (x y:A)(j:Axis) : P.reflectTest j (x+y)=P.reflectTest j x + P.reflectTest j y:= Subtype.ext (Tower.mirror_plus ..)
lemma sensor_mirror (j:Axis)(V:P.Apron)(q:P.Sensor V W): P.Sensor (V.kiss P j) W:=by
  let Φ:=P.reflectTest j
  let R:= sensing P (Tower.reflectedBox j 0 V.S) V.s W
  change Φ V.F ∈ R
  refine Submodule.span_induction (s:=_) (p:=fun f _=> Φ f∈R) (fun f v=>?_) ?_ ?_ ?_ (show V.F∈ P.sensing V.S V.s W from q)
  · obtain ⟨S,T,U,p,h,u,v,e⟩:=v
    have hx:= P.pin_reflect V.s _ _ j u
    refine Submodule.subset_span (show _∈_ from ⟨_,_,_,?_,?_,hx.symm,mirror_dressed K W S T U j 0 v,P.mirror_keeps j 0 e⟩)
    · exact union_subset (Finset.image_subset_image (Finset.subset_union_right.trans p)) (Finset.image_subset_image (Finset.subset_union_left.trans p))
    exact Finset.image_subset_image h
  · rw [show Φ 0=0 from by simpa using P.scale_mirror 0 0 j]; exact R.zero_mem
  · intro f g _ _ p q; unfold Φ at *; rw [P.sum_mirror]; exact R.add_mem p q
  intro z f _ p; unfold Φ at *; rw [P.scale_mirror]; exact R.smul_mem _ p
lemma issuance_senses (V:P.Apron)(p: V.s≤t)(v:P.Sensor V W):
    P.issuing t V o∈ P.sensing (P.plotSet t V o) t W:= by
  let n:= t-V.s
  let z(x:A):=P.chartAll o (P.conveying V.s n x)
  let B:=P.sensing (P.plotSet t V o) t W
  change z _ ∈ B
  refine Submodule.span_induction (s:=_) (p:=fun f _=> z f ∈ B) (fun f v=>?_) ?_ ?_ ?_ (show V.F∈ P.sensing V.S V.s W from v)
  · obtain ⟨S,T,U,w,h,u,v,c⟩:=v
    let a:=(volumeAround P.par P.width n)
    have hP:S⊆U:= Finset.subset_union_left.trans w
    have hQ:T⊆U:= Finset.subset_union_right.trans w
    let M:=(Vacancy.ordinate)
    have who := P.cruise_keeps_charge W M o (a S) (a T) (a U) (x:=P.conveying V.s n f) (P.onward W S T U V.s _ hP hQ v n) -- signature check
    -- argument order
    refine Submodule.subset_span (show _∈_ from ⟨_,_,_,?_,?_,?_,who,P.cruise_color M o (f := P.conveying V.s n f) ?_⟩)
    · exact union_subset (P.place_mono (a S) (a U) M o (P.vol_mono n hP)) (P.place_mono (a T) (a U) M o (P.vol_mono n hQ))
    · exact P.place_mono (a U) _ M o (P.vol_mono n h)
    · exact P.place_distinct t _ _ M o (u.mono (P.pin_onward V.s t S p) (P.pin_onward V.s t T p))
    exact P.refine_keeps V.s f c n
  · unfold z; rw [P.vanishes_receipt,map_zero]; exact B.zero_mem
  · intro a b _ _ h H; rw [show z (a+b)=z a+z b by unfold z; rw [P.later_receipt,map_add]]; exact B.add_mem h H
  intro r f _ p; rw [show z (r • f)=r • z f from by unfold z; rw [P.scaled_receipt,map_smul]]; exact B.smul_mem r p
lemma pocket_gap (n:ℕ)(h: P.calibration.ℓ < n) :
    Disjoint (P.pinFoot s {nodeC (P.flash n).birth}) (P.pinFoot s {nodeC (P.flash n).death}):= by
  apply Set.disjoint_left.mpr
  rintro x ⟨i,u,b⟩ ⟨k,v,d⟩
  rw [Finset.mem_singleton] at u v; rw [u] at b; rw [v] at d
  specialize b 3; specialize d 3
  have he:(nodeC (P.flash n).death) 3=(nodeC (P.flash n).birth) 3+ (2:ℤ)*n:= by simp [flash,nodeC,kernel0]; omega
  obtain ⟨a,p⟩:= abs_le.mp b
  -- p upper; a redundant. take abs inequality using copies
  have ht: (P.calibration.ℓ:ℝ) < (n:ℝ):=by exact_mod_cast h
  rw [he,Int.cast_add,Int.cast_mul,Int.cast_ofNat,Int.cast_natCast] at d
  change |_|≤ (P.calibration.ℓ:ℝ) at d
  have H':= (abs_le.mp d).1
  change _≤ (P.calibration.ℓ:ℝ) at p
  linarith only [p,H',ht]
lemma body_senses (n:ℕ)(h:P.calibration.ℓ < n) : P.Sensor (P.experimentBody Z s n) Z.2 := by
  let F:=P.flash n; let S:= ({nodeC F.birth}:Finset Cover); let T:= ({nodeC F.death}:Finset Cover); let i:= P.laterPulse n; let M:= F.patio
  have d:S⊆M:= Finset.singleton_subset_iff.mpr (Lamour.Bridge.Celeste.porchBorn F)
  have e:T⊆M:= Finset.singleton_subset_iff.mpr (Lamour.Bridge.Celeste.porchGone F)
  have u : Disjoint (P.pinFoot s S) (P.pinFoot s T):= P.pocket_gap s n h
  have hp:= P.front_charge Z n
  let R:=P.sensing (P.measureStencil n) s Z.2
  apply Submodule.sub_mem R
  · exact Submodule.subset_span (show _∈_ from ⟨S,T,M,union_subset d e, Finset.subset_union_left,u,hp,P.front_real Z n⟩)
  refine Submodule.subset_span (show _∈_ from ⟨plow K 3 i S,plow K 3 i T,plow K 3 i M,
    union_subset (image_subset_image d) (image_subset_image e), Finset.subset_union_right,
    P.pin_relocate s S T 3 i u, relocate_dressed K Z.2 S T M 3 i hp,P.back_real Z n⟩)
section kill
variable {X:Dome P.calibration→ₗ[ℂ]ℂ}(p: Factors P.calibration X)(h:MatterWard P.calibration X ∨ GaugeWard P.calibration X)
include p h
lemma far_price {f b:P.Test}(v:f∈ sensing P S s W)(g:b∈bay K T true)(d: Disjoint (P.pinFoot s S) (P.pinFoot s T)): X (f*b)=0:=by
  refine Submodule.span_induction (p:=fun f _=> X (f*b)=0) (fun f v=>?_) (by rw [zero_mul,map_zero]) (fun _ _ _ _ a b=>by rw [add_mul,map_add,a,b,zero_add]) (fun z _ _ a=>by rw [smul_mul_assoc,map_smul,a,smul_zero]) v
  obtain ⟨x,y,z,t,r,u,v,e⟩:=v
  exact ward_price K W x y z p h e v t (P.pin_disjoint _ _ _ u) g ((P.pin_disjoint _ _ _ d).mono_left r)
lemma msplit_pair (B C:P.Apron) (H:P.Sensor B W) (q:B.s ≤ s) (i j:Cover)
    (d:Disjoint (P.Aperture B (P.meshPose s i)) (P.Aperture C (P.meshPose s j)))
    (u:C.s ≤ s) : X (P.issuing s B i * P.issuing s C j)=0:=
  P.far_price W s _ _ p h (P.issuance_senses W s i B q H) (P.issuing_support s j C)
    (d.mono (P.inside_now s i B q) (P.inside_now s j C u))
-- `eq:msplit` also allowing any other list of Aprons, first with the indicated Sensor.
lemma msplit (B:P.Apron)(i:Cover)(v:P.Sensor B W)(u:B.s ≤ s)
    (L:List (P.Apron × Cover))
    (t:∀ a∈ L,a.1.s ≤ s ∧ Disjoint (P.Aperture B (P.meshPose s i)) (P.Aperture a.1 (P.meshPose s a.2))) :
    X (P.issuing s B i * (L.map (fun a=>P.issuing s a.1 a.2)).prod)=0:= by
  let f:=fun a:P.Apron × Cover =>P.issuing s a.1 a.2
  let M:=P.plotSet s B i
  have e:∃ T:Finset Cover,(L.map f).prod ∈ bay K T true ∧ Disjoint (P.pinFoot s M) (P.pinFoot s T):= by
    clear p h
    induction L with
    | nil=> exact ⟨∅,(bay K ∅ true).one_mem, by rw [show P.pinFoot s ∅=∅ by ext; simp [pinFoot]]; simp⟩
    | cons a l' w=>
      have hp:=t a (List.Mem.head ..)
      obtain ⟨S,v,H⟩:= w (fun a x=> t a (List.Mem.tail _ x)); let T:=P.plotSet s a.1 a.2
      have he : Disjoint (P.pinFoot s M) (P.pinFoot s T):= hp.2.mono (P.inside_now s i B u) (P.inside_now s a.2 a.1 hp.1)
      refine ⟨T∪S, Subalgebra.mul_mem (bay K (T∪S) true) (tallerBay K _ true subset_union_left (P.issuing_support s a.2 a.1)) (tallerBay K _ _ subset_union_right v),?_⟩
      apply Set.disjoint_left.mpr; rintro y u ⟨b,h,g⟩; rcases Finset.mem_union.mp h with p|p
      · exact Set.disjoint_left.mp he u ⟨_,p,g⟩
      exact Set.disjoint_left.mp H u ⟨_,p,g⟩
  obtain ⟨U,p',w⟩:= e; exact P.far_price W s _ _ p h (P.issuance_senses W s i B u v) p' w
end kill
-- bring the comparison onto P's normalization.
theorem comparator (x:P.Spectrum0 3) : let E:=P.singleState 3 s x
    ∃ X, Comparison K E X ∧ X 1=1 ∧ GaugeWard K X ∧ MatterWard K X:=by
  intro E
  have hp : E 1=1:=by unfold E; rw [P.single_state,P.reading_unit,map_one]
  obtain ⟨X,h⟩:= comparison_exists K E hp
  have he(g:Cover→SU.E)(f:A): E (pennant K g f)=E f:=by unfold E; rw [P.single_state,P.single_state,P.reading_gauge]
  exact ⟨X,h,h.unit K E hp, h.gaugeWard K E (fun g f _=> he g f),h.matterWard K E (fun g f _=> he g f)⟩
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
