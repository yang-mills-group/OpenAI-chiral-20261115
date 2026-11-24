import YM.SU5.Same.Lab

/-!
# Physical support sectors diagnostic: the marginal components themselves

What would the given registration do to the inputs of `Spine.linkLink`, `matterMatter` etc?
Not separately physical observables then assembled without charge: **each time strip
operator exactly zero**, even at finite Mark resolution. Not a spontaneous symmetry restoration
statement. Comes from their gauge frames at that preparation. Warning that this doesn't
address what a comparison between theories with different dynamics on their own charged
spaces would perceive.
-/
set_option autoImplicit false
set_option synthInstance.maxSize 30000
set_option maxRecDepth 4000
set_option maxHeartbeats 500000
set_option quotPrecheck false
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
open Set
open FirstWindows FirstWindows.LightBudget FirstWindows.Chambers FirstWindows.ChargeFrame
variable (P : Spine) (x : P.Spectrum0 3) (j : Axis)
local notation "Y" => P.run
local notation "H" => P.large
local notation "V" => P.law
local notation "G" => P.projection
local notation "R" => P.glassSpace 3 x j
local notation "c" => P.glassAxis 3 x j
local notation "K" => P.calibration
local notation "N" => timeMesh P.par
variable (t w : ℕ)
local notation "d" => notch N t (w:ℤ)
local notation "I" => Chambers.strip j 0 ((d: marks N):ℝ)
local notation "Λ" => FirstWindows.ticket Y H G t
local notation "T" => Follows Y H V G j (P.room j) c

abbrev PulseFollows (f : P.Test) (A : (P.glassSpace 3 x j).Op) :=
  Follows Y H V G j (P.room j) c (Λ f) (notch (timeMesh P.par) t (w:ℤ)) A

lemma seat_from_foot (D : Finset Cover) (e : P.pinFoot t D ⊆ I) : Between K j 0 (ruler P.par.block * w) D := by
  apply (strip_seats Y H j t w).1
  have ht : PhaseChoice.SupportedPhysically P.par P.width t D (P.pinFoot t D) := by
    rw [P.usual_footprint]
    exact Tower.Reconstruction.has_footprint P.par P.width t D
  rw [show (whenly N t w:ℝ) = ((d:marks N):ℝ) from Eq.symm (natural_time ..)]
  exact (FirstWindows.supported_iff ..).2 (((FirstWindows.supported_iff ..).1 ht).trans e)

/-- Loose Card **operator** interpretation; not in general a strict field. -/
def looseCard {D : Finset Cover} (e : Between K j 0 (ruler P.par.block * w) D)
    (f : P.Test) (hf : f∈bay K D true) : P.Card j t w :=
  ⟨P.positiveVox j t D f hf (fun i h=> (e i h).1),D,hf,e⟩

lemma pulse_gauge_price {D : Finset Cover} (g : Cover → SU.E) (e : P.pinFoot t D ⊆ I)
    (v : 0 < w) (f : P.Test) (hf : f∈bay K D true) :
    ∃ X : (R).Op, P.PulseFollows x j t w f X ∧ P.PulseFollows x j t w (pennant K g f) X := by
  let W := P.seat_from_foot j t w D e
  have ht := pennantLocal K D g hf
  let A := P.looseCard j t w W f hf
  let B := P.looseCard j t w W (pennant K g f) ht
  have he : P.glassEntryOp 3 x j t w v A = P.glassEntryOp 3 x j t w v B :=
    congrArg (Selected.procession Y H V P.history P.projection.clipped j false (P.room j) c)
      (Selected.color_slab Y H V t P.history P.projection.clipped j false (P.room j)
        v A B ((Tapestry.locates ..).1 hf) ((Tapestry.locates ..).1 ht) W g (pennantTrace K D g hf))
  refine ⟨_,(show P.PulseFollows x j t w f (P.glassEntryOp 3 x j t w v A) from arrangement Y H V G j (P.room j) c t w A v),?_⟩
  rw [he]; exact arrangement Y H V G j (P.room j) c t w B v

lemma gauge_null {D : Finset Cover} (g : Cover → SU.E) (e : P.pinFoot t D ⊆ I)
    (v : 0 < w) (f : P.Test) (hf : f∈bay K D true) : P.PulseFollows x j t w (pennant K g f - f) 0 := by
  obtain ⟨X,p,q⟩ := P.pulse_gauge_price x j t w g e v f hf
  have he := subScore Y H V G j (P.room j) c q p
  change T _ _ (X-X) at he
  unfold PulseFollows; rw [map_sub]
  rwa [sub_self] at he

lemma matter_null {D : Finset Cover} (g : Cover → SU.E) (e : P.pinFoot t D ⊆ I)
    (v : 0 < w) (f : P.Test) (hf : f∈bay K D true) (z : ℂ) (vz : z ≠ 1)
    (u : pennant K g f = z • f) : P.PulseFollows x j t w f 0 := by
  obtain ⟨X,p,q⟩ := P.pulse_gauge_price x j t w g e v f hf
  have a : T (z • (Λ f)) d X := by unfold PulseFollows at q; rwa [u,map_smul] at q
  have eq : z • X = X := unique_op Y H V G j (P.room j) c _ (scaleScore Y H V G j (P.room j) c p z) a
  have he : (z-1) • X = 0 := by rw [sub_smul,one_smul,eq,sub_self]
  rwa [show X = 0 from (smul_eq_zero.mp he).resolve_left (sub_ne_zero.mpr vz)] at p

variable {U : Set Vantage} (f : P.PulseComponent t U)

lemma pulseOp_zero (e : U ⊆ I) (v : 0 < w) : P.PulseFollows x j t w f.link 0 ∧
    P.PulseFollows x j t w f.matter 0 :=
  ⟨P.gauge_null x j t w _ (f.addr.trans e) v _ f.stamp.lhere,
    P.matter_null x j t w _ (f.addr.trans e) v _ f.stamp.mhere f.stamp.θ f.stamp.price f.stamp.tilt⟩

local notation "F" => P.reflectTest j

lemma pulseOp_earlier_zero (e : mirrorΩ j '' U ⊆ I) (v : 0 < w) :
    P.PulseFollows x j t w (F f.link) 0 ∧ P.PulseFollows x j t w (F f.matter) 0 := by
  let A := f.budget
  have hx : P.pinFoot t (Tower.reflectedBox j 0 A) ⊆ I := fun y hy=> e
    ⟨mirrorΩ j y,f.addr (P.mirror_back_pin t A j hy),reflectPose_twice j y⟩
  let g := reflectGauge j (0:ℤ) f.stamp.g
  have hg : ∀ k : P.Test, F (pennant K f.stamp.g k) = pennant K g (F k) := fun k => by
    unfold reflectTest; rw [pennantReflect K g, show reflectGauge j (0:ℤ) g = _ from gauges_of_mirror j 0 f.stamp.g]
  constructor
  · let a := f.stamp.G
    change P.PulseFollows _ _ _ _ (F (pennant K f.stamp.g a - a)) _
    rw [map_sub,hg]; exact P.gauge_null x j t w g hx v _ (aureoleBay K A true j 0 a f.stamp.lhere)
  have hk : star f.stamp.θ ≠ 1 := fun h=> f.stamp.price (star_injective (h.trans (star_one ℂ).symm))
  refine P.matter_null x j t w g hx v _ (aureoleBay K A true j 0 f.matter f.stamp.mhere) _ hk ?_
  rw [←hg]; change F (pennant K f.stamp.g f.stamp.B)=_; rw [f.stamp.tilt,P.scale_mirror]

#print axioms pulseOp_zero
#print axioms pulseOp_earlier_zero
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
