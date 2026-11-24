import YM.SU5.Macro.Tilt
import YM.SU5.Macro.Invert
import YM.SU5.Macro.Margin
import YM.SU5.Obstruction.Gap
/-!
# The mask/tilt obstruction, now retesting the chosen INTERACTION EARLY operand itself

cf. `t:no`. Different election, mask & proof. Pay the actual mask and center extension
BEFORE applying this geometry. `Signal` stencils and sensor. The mask is on the Interaction
itself. This failure is in the full-width contact grammar, not charged conjectures.
-/ 
set_option autoImplicit false
set_option maxHeartbeats 470000
set_option maxRecDepth 4500
set_option synthInstance.maxSize 24000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.Selection.Home
open Function Filter NormedSpace Metric SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Heat Fock Analysis SlabMark Vacancy SatinVerification
open Tapestry Tapestry.Altitude
open Tower.PhaseChoice Tower.Selected Tower.Reconstruction
open CF.SatinRotation CF.Pannier.Chancel.Attic.Cairn Buffered.Reliance Buffered.Reliance.ShortWave
open CF.Pannier.Chancel CF.Pannier.Chancel.Lantern CF.Pannier.Chancel.Lantern.Bulb
open Rubric Fern Fern.Planet
open OS.Semigroup MeshClock
variable {Λ:Preparation}{l:ℕ}(Y:Course Λ (VolumeCape.Dream.Nimbus l))(H:Real.exp 1≤Λ.x)
local notation "K" => tent Y H
variable {i k:ℕ→ℕ}{I:ℕ→Family (tent Y H)→ℕ→ℂ}{E:ℕ→Family (tent Y H)→ℂ}
    {L: Rack Λ l} {B:Clay Λ l} {T:ℕ→ℕ→Tariff} {t:ℕ→Tariff} (D: Fashion Y H i k I E L B T t)
    (G:SatinVerification.GroundExtension (i:=i) (k:=k) (E:=E) Y H) (room : ∀ j:Axis,Arena Y H G.history.circuit j 0 false)
    (χ:CapCharacter Y H D.univ_ G.history G.clipped 3 false (room 3))
local notation "V" => D.univ_
local notation "Q" => G.history
local notation "Qt" => G.clipped
namespace Siam
open Giant
variable (s:ℕ) (M:Giant)
local notation "Φ" => Torrent.fare
local notation "A" => early M
local notation "S" => M.ascX
local notation "Wz" => wall M
local notation "Γ"=> sch Y H D G room (dial Y H D G room 3 χ 0)
local notation "Ω" => Dome (tent Y H)
local notation "Κ" n:max => (pinhole (Dome (tent Y H)) n)
namespace Blind
open CF.SatinRotation.Clean CF.SatinRotation.Tilt Bornology
variable {f g:Dome (tent Y H)}{z:Window.Family} {ε:ℝ}(p: Signal Y H D G room χ s M f g z ε)
local notation "U" => footprint Λ l s (early M)
local notation "U'" => footprint Λ l s M.ascX
local notation "Up" => followBox (Λ:=Λ) (l:=l) (CF.SatinRotation.faceSites (wall M))
local notation "E₀" => D.toExhibition
local notation "γ" => D.toExhibition.liftD Y H s
local notation "V'" => Clean.detector ε (wall M) (tent Y H)

/-- Footprint $U$ enough even for the interaction sensor (no new geometry
   when buying the countertest after taking the limit in s currency). -/
def sensor (ε:ℝ)(w:0<ε) : Altitude.Cloud Ω:= (Κ s) (Clean.detector ε (wall M) (tent Y H))* (Κ (s+1)) (undoLift ε (wall M) Y H s w D.toExhibition) - 1
local notation "Vw"=>undoLift ε (wall M) Y H s (Signal.mask_pos p) D.toExhibition
local notation "R"=> sensor Y H D s M ε (Signal.mask_pos p)
include p
lemma positionD : sensor Y H D s M ε (Signal.mask_pos p) ∈ PolAt Y H (s+1) (footprint Λ l s (early M)):=by
  -- fit
  have h: footprint Λ l s (faceSites (wall M))⊆ U := by
     intro x t; rw [footprint_eq] at *
     obtain ⟨w,q,g⟩:=silhouette_iff.mp t; exact silhouette_iff.mpr ⟨w,wall_in M q,g⟩
  let Up':= footprint Λ l s (faceSites (wall M))
  have ht: (Κ s) (V')∈ PolAt Y H (s+1) Up':=
    oneSlotWell Λ K l true _ _ s (Set.mem_inter (Set.mem_univ _) (Set.mem_Iic.mpr s.le_succ)) (x:=V') ((keeps ..).mpr ⟨_, det_bay .., has_footprint Λ l s _⟩) (det_enclave ε (wall M) K)
  have he:(Κ (s+1)) (Vw)∈PolAt Y H (s+1) Up':=
    oneSlotWell Λ K l true _ _ _ (Set.mem_inter (Set.mem_univ _) (Set.mem_Iic.mpr le_rfl)) (x:=Vw)
      ((keeps ..).mpr ⟨Up, undo_bay ..,shielding Λ l s (handstamp Up') _ (has_footprint Λ l s (faceSites (wall M)))⟩) (undo_neutral ε (wall M) Y H D.toExhibition s p.mask_pos)
  let B:= PolAt Y H (s+1) Up'
  exact isotone Y H h (B.sub_mem (B.mul_mem ht he) B.one_mem)
local notation "X" => pinhole (Dome K) s f
local notation "W" => pinhole (Dome K) s g
lemma dark : R*X = -X:= by
  have he : detector ε (wall M) K * f=0:= by
    apply Subtype.ext; funext m t
    let k:= SU.group.chord (faceValue (onC ((K).c m) t.1) (wall M)); change ((detector ε (wall M) K).val m t)*(f.val m t) = _
    rcases le_total k ε with q|q
    · rw [p.mask _ _ q, mul_zero]; rfl
    change ((CF.SatinRotation.Clean.«clear» ε _ : ℂ) • (1: FC _)) * (f.val m t) = 0; rw [closes ε _ q,Complex.ofReal_zero,zero_smul,zero_mul]
  unfold sensor; rw [_root_.sub_mul,one_mul,mul_right_comm,←map_mul (pinhole Ω s),he,map_zero,zero_mul,zero_sub]

lemma expires : D.toExhibition.vistaFinish Y H (s+1) (sensor Y H D s M ε (Signal.mask_pos p))=0:= by
  unfold sensor; rw [map_sub, finish_multiply Y H D.toExhibition _ _ (climbs Ω (Nat.le_succ s) (short_pinhole s V')),finish_step, undo, Exhibition.vistaFinish,Decking.crown1,sub_self]

omit p in
lemma high_zero {r n:ℕ}(h:r≤n)(F: Cloud Ω) (x: F∈ shorter Ω (r+1))(c:D.toExhibition.vistaFinish Y H (r+1) F=0) (y: Cloud Ω)
    (q:y∈ loosePol Y H Set.univ (Set.Ici (r+1)∩Set.Iic (n+1))) : D.toExhibition.vistaFinish Y H (n+1) (F*y)=0:= crown_later_poly (D.toExhibition.vistaDressing Y H) (auxiliaryPad K) F x c (n+1) (Nat.succ_le_succ h) _ Set.inter_subset_left Set.inter_subset_right (fun i=>keep Λ l i K true (handstamp Set.univ)) q
omit p in
lemma costs_none (F: Cloud Ω)(x:F∈ shorter Ω (s+1))(c:D.toExhibition.vistaFinish Y H (s+1) F=0) {y:Cloud Ω}(q:y∈ higherOnly Y H s): Γ (F*y)=0:= by
  obtain ⟨n,u⟩:=entrusted Λ l K true (handstamp Set.univ) _ q
  let N:= max n s
  let B:= Set.Ici (s+1)
  have v:y∈ loosePol Y H Set.univ (B∩ Set.Iic (N+1)):= admits Λ l K true _ _ _ _ (Set.inter_subset_inter_right _ (Set.Iic_subset_Iic.mpr ((le_max_left n s).trans (Nat.le_succ N)))) Set.Subset.rfl u
  have h: F*y∈ shorter Ω (N+1):=(shorter ..).mul_mem (climbs Ω (Nat.succ_le_succ (le_max_right n s)) x) (jettyBan Λ l K true (handstamp Set.univ) B (N+1) v)
  exact (sch_via_same Y H D G room (dial Y H D G room 3 χ 0) (F*y) 0 h (Subalgebra.zero_mem _) ((high_zero Y H D (le_max_right n s) F x c y v).trans (map_zero _).symm)).trans (map_zero _)

-- J for the gap--tested state's own apparatus. Normalize with nonzero price.
local notation "c" => Γ (X*W)
def witness : Altitude.Cloud Ω:= (- (Γ (X*W))⁻¹) • (R*W)
local notation "J" => witness Y H D G room χ s M p
local notation "Tχ" => sch Y H D G room (dial Y H D G room 3 χ 0)
lemma masked_price : Tχ ((witness Y H D G room χ s M p)* X) = 1 ∧ Tχ (R * (X*W)) = -(Tχ (X*W)) ∧ Torrent.fare < ‖Tχ (R*(X*W))‖:=by
  obtain ⟨e,h⟩:= p.connected Y H D G room χ s M
  have ht : Tχ (R*(X*W))= - (Tχ (X*W)):= by rw [← mul_assoc,dark Y H D G room χ s M p,neg_mul,map_neg]
  refine ⟨?_,ht,by rw [ht,norm_neg]; exact e⟩
  unfold witness; rw [Algebra.smul_mul_assoc, mul_assoc, mul_comm W X, map_smul, ht]
  simp [norm_pos_iff.mp (Torrent.fare_p.trans e)]
local notation "O" => U ∪ U'
lemma local_witness : J∈ PolAt Y H (s+1) O := by
  obtain ⟨_,_,_,_,_,_,h,_⟩:= p.paid_box Y H D G room χ s M
  let T:= PolAt Y H (s+1) O
  exact T.smul_mem (T.mul_mem (isotone Y H Set.subset_union_left (positionD Y H D G room χ s M p))
    (isotone Y H Set.subset_union_right (polAt_up Y H s.le_succ h))) _
lemma finish_zero : D.toExhibition.vistaFinish Y H (s+1) J=0:=by
  have a:= positionD Y H D G room χ s M p
  obtain ⟨_,_,_,w,_,_,h,_⟩:= p.paid_box Y H D G room χ s M
  have ht:= PhaseChoice.depart_pair Y H V G D.toExhibition ((well_spec ..).mp a).1 ((well_spec ..).mp (polAt_up Y H s.le_succ h)).1 (Disjoint.preimage _ w)
  unfold witness; rw [map_smul,ht,expires Y H D G room χ s M p,zero_mul,smul_zero]
lemma not_paid {y:Altitude.Cloud Ω}(q:y∈ higherOnly Y H s): Γ (J*y) = 0 ∧ Γ (R*y)=0:= ⟨costs_none Y H D G room χ s J (inside_budget Y H (local_witness Y H D G room χ s M p)) (finish_zero Y H D G room χ s M p) q,costs_none Y H D G room χ s R (inside_budget Y H (positionD Y H D G room χ s M p)) (expires Y H D G room χ s M p) q⟩
omit p in
lemma no_coarse {Z:Set RSpace}(f:∀ (i:ℕ),i ≤ s → ∀ x:Cover, ¬ collar Λ l i x ⊆ Z) :
    loosePol Y H Z Set.univ ≤ higherOnly Y H s:= by
  rw [loosePol,generating]; apply Algebra.adjoin_le
  intro x hx; obtain ⟨i,hi⟩:= Set.mem_iUnion.mp hx; obtain ⟨_,y,hy,rfl⟩:= Set.mem_iUnion.mp hi
  change y ∈ keep Λ l i K true (handstamp Z) at hy
  rcases le_or_gt i s with g|g
  · obtain ⟨B',h,t⟩:= (keeps ..).mp hy
    have hs : B'=∅:= Finset.eq_empty_iff_forall_notMem.mpr (fun u p=> f i g u (fit_collar Λ l u i p t))
    subst B'
    obtain ⟨r,w⟩:= emptySupport_scalar ((locates K ∅ true).mp h)
    have v : y = r • (1 : Dome K) := Subtype.ext w
    change pinhole Ω i y∈ higherOnly Y H s
    rw [v,map_smul,map_one]; exact (higherOnly Y H s).smul_mem ((higherOnly ..).one_mem) r
  rw [higherOnly_eq]; apply Algebra.subset_adjoin
  exact Set.mem_iUnion.mpr ⟨i,Set.mem_iUnion.mpr
    ⟨Set.mem_Ici.mpr g,Set.mem_image_of_mem _ (Set.mem_univ y)⟩⟩

def evaluations (Ω' : Subalgebra ℂ (Cloud Ω)) : Set ℂ :=
    closure ((fun X' : Cloud Ω => Γ (J*X')) '' (Ω':Set _))
/-- Arbitrarily good evaluation approximation, so test already gives a necessary test. -/
theorem gap (θ:ℝ)(b:θ≠0)(e:|θ| < Real.pi / 2):
    X ∈ Pol Y H U ∧ J∈ Pol Y H O ∧ Tχ (J * X)=1 ∧
    ∃ P:Set RSpace, IsOpen P ∧ Bornology.IsBounded P ∧ footprint Λ l s (early M) ⊆ P ∧
     let W' := roll (Tilt.tilt θ) '' P
     IsOpen W' ∧ IsBounded W' ∧ loosePol Y H W' Set.univ ≤ higherOnly Y H s ∧
     evaluations Y H D G room χ s M p (loosePol Y H W' Set.univ) ⊆ {0}:=by
  obtain ⟨_,_,_,_,_,h,_⟩:=p.paid_box Y H D G room χ s M
  obtain ⟨W',v,Wb,z',t⟩:= Tilt.no_fit Λ l s (early_flat M) θ b e
  let W₀:= roll (Tilt.tilt θ) '' W'; have h': loosePol Y H W₀ Set.univ≤higherOnly Y H s:= no_coarse Y H s t
  obtain ⟨i,o⟩:= rigid_image (Tilt.tilt θ) v Wb
  refine ⟨pol_of_level Y H h, pol_of_level Y H (local_witness Y H D G room χ s M p),(masked_price Y H D G room χ s M p).1,W',v,Wb,z',i,o,h',?_⟩
  apply closure_minimal ?_ isClosed_singleton
  rintro x ⟨t,g,rfl⟩; exact Set.mem_singleton_iff.mpr (not_paid Y H D G room χ s M p (h' g)).1

/-- The reach/price test for even a proposed SO extension of this macroscopic
field, in its local region budget. No assumption on the continuity of the
character or re-weighting: actually retesting on this very χ. -/
def Reach (F:SO→ℂ) := ∀ᶠ θ : ℝ in 𝓝[≠] (0:ℝ), ∀ Xp : Set RSpace, IsOpen Xp → IsBounded Xp → footprint Λ l s (early M) ⊆ Xp →
    F (Tilt.tilt θ)∈ evaluations Y H D G room χ s M p (loosePol Y H (roll (Tilt.tilt θ) '' Xp) Set.univ)

theorem discontinuous (F : SO→ℂ) (x : Reach Y H D G room χ s M p F) (y:F 1= Tχ (J*X)): ¬ ContinuousAt F 1:=by
  intro e; have H' : Tendsto (F ∘ Tilt.tilt) (𝓝[≠] (0:ℝ)) (𝓝 (1:ℂ)):=by
     rw [←(masked_price Y H D G room χ s M p).1,←y]
     refine e.tendsto.comp ?_; rw [←Tilt.t_zero]; exact Tilt.t_cont.continuousWithinAt
  have p': (F ∘ Tilt.tilt) =ᶠ[𝓝[≠] (0:ℝ)] fun _=> (0:ℂ):=by
     filter_upwards [x,_root_.YM.SU5Rotation.Plane.eventually_angles] with θ u v; obtain ⟨_,_,_,Z,hv,b,t,_,_,_,e⟩:= gap Y H D G room χ s M p θ v.1 v.2; exact Set.mem_singleton_iff.mp (e (u Z hv b t))
  exact one_ne_zero (tendsto_nhds_unique_of_eventuallyEq H' tendsto_const_nhds p')

end Blind
end Siam
end YM.CF.Buffered.Afterglow.Tower.Selection.Home
open YM.CF.Buffered.Afterglow.Tower.Selection.Home.Siam.Blind
#print axioms not_paid
#print axioms masked_price

#print axioms gap
#print axioms discontinuous
