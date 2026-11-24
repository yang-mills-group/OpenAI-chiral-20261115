import SatinFixedContrastNovember4
import SatinThinDisclosedPure

/-!
# Finite presentation of the margins

Build plans on any of these smears decomposing them to raw-marginal inputs,
so that all the pure marginal prices actually needed (in the advertised
comparison rule) are available from the actual singles' functional, even
before the limits. Location of each input included. NOT claiming paths or
component fields after any of those limits. These are computations on the
selected character.
-/
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 3000
set_option maxHeartbeats 380000
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common Ballad Cordial
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
open Germ Alliance Lamour.Bridge.Celeste Designs Twah Prototype
open Lamour.Bridge.Celeste.Morn
namespace Spine
open Aria Casting Six OS.Semigroup OS.Semigroup.Balloon
open MacroGrid SatinNucleus SatinJets DoseTravel Set
variable (P:Spine)
local notation "K" => P.calibration
local notation "e₁"=> PulsePiece (K)

structure PulseComponent (s:ℕ)(U:Set Vantage) where
 budget : Finset Cover
 addr : P.pinFoot s budget ⊆ U
 stamp : PulsePiece P.calibration budget
variable (s t:ℕ)(U V:Set Vantage)
variable {P s U V}
namespace PulseComponent
variable (p:P.PulseComponent s U)
abbrev link := p.stamp.rawLink
abbrev matter := p.stamp.B
abbrev representation : P.Test := p.link * p.matter
end PulseComponent
variable (P s U V)
local notation "ζ₀"=> PulseComponent.representation
-- plans lie in *precisely that region* at height s, even if using many pieces
-- note no assumption of continuity of these assignments.
def stitchPlan (f: P.PulseComponent s U  →₀ℂ)(a:P.Test): Prop:= ∑ i∈ f.support,f i • ζ₀ i = a
private lemma arrange {a:P.Test}(h:a∈ Submodule.span ℂ (Set.range fun i:P.PulseComponent s U => ζ₀ i)) :
    ∃ f: P.PulseComponent s U →₀ℂ,P.stitchPlan s U f a:=by
 rw [← Finsupp.range_linearCombination] at h; obtain ⟨f,e⟩:= h; exact ⟨f,e⟩
private lemma pulsed_span (S:Finset Cover) (q:P.pinFoot s S ⊆ U) (b:Bool)(x:P.Test)(e:x∈ P.sensing S s b): x∈ Submodule.span ℂ (Set.range fun i:P.PulseComponent s U => ζ₀ i):=by
 refine Submodule.span_le.mpr ?_ e
 rintro w ⟨A,B,V,h,t,v,u,a⟩; apply Submodule.span_mono _ (Six.spanning_pulses K b A B V S h t (P.pin_disjoint s A B v) u a)
 rintro f ⟨k,rfl⟩; exact ⟨⟨S,q,k⟩,rfl⟩
variable (A:P.Apron) (F:SampleDose) {b:Bool}
theorem stitchPlan_footprint (z: Cover)(a:P.Sensor A b)(h:A.s≤t) :
    ∃ f, P.stitchPlan t (P.Aperture A (P.meshPose t z)) f (P.issuing t A z):=
 P.arrange _ _ (P.pulsed_span _ _ (P.plotSet ..) (P.inside_now t z A h) b _ (P.issuance_senses b t z A h a))
lemma stitchPlan_budget (a:P.Sensor A b)(h:A.s≤t) :
    ∃ f, P.stitchPlan t (P.spacePrice A F) f (P.prepared t A F):=by
  let Z:= Submodule.span ℂ (Set.range fun i:P.PulseComponent t (P.spacePrice A F) => ζ₀ i)
  refine P.arrange _ _ (Z.sum_mem ?_); intro i t'; refine Z.smul_mem _ (P.pulsed_span t _ (P.plotSet t A i) (Subset.trans (P.inside_now t i A h) ?_) b _ (P.issuance_senses b t i A h a))
  exact subset_iUnion₂_of_subset (P.meshPose t i) ((P.usedPose t F i).1 t') Subset.rfl

variable (x:P.Spectrum0 3)
local notation "p[" t "]"=> P.singleState 3 t x
local notation "σ[" t "]"=> P.thinSplit x t
lemma singles_pure_ward : GaugeWard K p[t] ∧ MatterWard K p[t]:=by
 have h (v:Cover→SU.E)(f:P.Test) : p[t] (pennant K v f)=p[t] f:=by rw [P.single_state,P.single_state,P.reading_gauge]
 exact ⟨fun a b _=> h a b,fun a b _=> h a b⟩
-- pure components remain in this part of the prediction, not promoted independently
def linkMarginal (f:P.PulseComponent t U) : ℂ:= p[t] f.link
def matterMarginal (f:P.PulseComponent t U) : ℂ:= p[t] f.matter
variable (f:P.PulseComponent t U)(g:P.PulseComponent t V)
def linkLink : ℂ:= p[t] (f.link*g.link)
def matterMatter : ℂ:= p[t] (f.matter*g.matter)
lemma queries_marginal : P.linkMarginal t U x f=0 ∧ P.matterMarginal t U x f=0:=
 ⟨f.stamp.link_zero _ (P.singles_pure_ward t x).1,f.stamp.matter_zero _ (P.singles_pure_ward t x).2⟩
lemma earns_marginal (D:Disjoint U V) : P.linkLink t U V x f g = 0 ∧ P.matterMatter t U V x f g=0:=by
 have p:=P.pin_disjoint t f.budget g.budget (D.mono f.addr g.addr)
 exact ⟨f.stamp.ward_link _ p (PulsePiece.rawGauge _) g.stamp.rawHere (P.singles_pure_ward t x).1,f.stamp.ward_matter _ p g.stamp.matter g.stamp.mhere (P.singles_pure_ward t x).2⟩
lemma predicted_marginal : σ[t] (ζ₀ f) = P.linkMarginal t U x f * P.matterMarginal t U x f := P.thin_split_is_raw x t _ _ f.stamp.rawGauge f.stamp.matter
-- actual split must use AFTER-advancement decomposition throughout
lemma predicted_opposite : σ[t] (ζ₀ f* ζ₀ g) = P.linkLink t U V x f g * P.matterMatter t U V x f g:=
 (congrArg σ[t] (mul_mul_mul_comm f.link f.matter g.link g.matter)).trans (P.thin_split_is_raw x t _ _ (gaugePure_mul K f.stamp.rawGauge g.stamp.rawGauge) (matterPure_mul K f.stamp.matter g.stamp.matter))
variable {P t U V}
lemma stitchPlan.single_reports (F:P.Test)(L:P.PulseComponent t U →₀ℂ)(h:P.stitchPlan t U L F):
    σ[t] F = ∑ i ∈ L.support,L i * (P.linkMarginal t U x i * P.matterMarginal t U x i):=by
 unfold Spine.stitchPlan at h; rw [←h,map_sum]; exact Finset.sum_congr rfl fun i _=> (map_smul σ[t] _ _).trans (congrArg (L i * ·) (P.predicted_marginal t U x i))
lemma stitchPlan.product_reports (F G:P.Test)(L:P.PulseComponent t U →₀ℂ)(M:P.PulseComponent t V →₀ℂ)(h:P.stitchPlan t U L F)(p:P.stitchPlan t V M G):
    σ[t] (F*G)= ∑ i∈L.support, ∑ j∈ M.support,L i * (M j * (P.linkLink t U V x i j * P.matterMatter t U V x i j)):=by
 unfold Spine.stitchPlan at h p; rw [←h,←p,Finset.sum_mul,map_sum]; refine sum_congr rfl fun i _=> ?_; rw [Finset.mul_sum,map_sum]; refine sum_congr rfl fun j _=> ?_
 rw [smul_mul_assoc,mul_smul_comm,map_smul,map_smul,P.predicted_opposite]; rfl
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
#print axioms YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine.stitchPlan_budget
#print axioms YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine.earns_marginal
