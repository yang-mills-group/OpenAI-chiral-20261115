import YM.SU5.Selected.Gap

/-!
# A component demand, witnessed already on the same E and coherent Q

Checkpoint 1. Selection on abelian ground algebra; all arguments have physical translation,
positions, locations and further realizations and the nonzero pair estimate uses the approved
gauge-law extension. Does not claim that the character found has its own OS Hilbert with
unique vacuum (cf. discussion YM/Phase for other systems). That choice and stronger dynamical
claims are separate obligations.
-/
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 4500
set_option maxHeartbeats 330000
set_option quotPrecheck false
noncomputable section

namespace YM.CF.Buffered.Afterglow.Tower.Selection
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory
open RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder
open scoped InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Heat Fock Analysis SlabMark OS.Semigroup MeshClock
open Vacancy

variable {Λ : Preparation} {l : ℕ} (Y : Course Λ (VolumeCape.Dream.Nimbus l))
  (H : Real.exp 1 ≤ Λ.x)
local notation "K" => tent Y H
variable {i k : ℕ → ℕ} {I : ℕ → Family (tent Y H) → ℕ → ℂ}
  {E : ℕ → Family (tent Y H) → ℂ} (V : Universal Y H i k I E)
  {D : ℕ → Family (tent Y H) → Family (tent Y H)} {a b : ℕ → ℕ}
  (Q : Coherent (i := i) (k := k) (E := E) Y H D a b)
  (Qc : Clipped Y H (i ∘ a) (k ∘ b))
  (j : Axis) (C : Arena Y H Q.circuit j 0 false)
local notation "R" => Aurora Y H V Q j false C
local notation "A" => Ark.Ht Y H Q.circuit j 0 false C
local notation "W" => floorV Y H Q.circuit j 0 false C
local notation "F₊" n:max => Tower.Field Y H n j 0 false
local notation "φ" n:max => actor Y H n Q.circuit j 0 false C
local notation "Ω" => seat0 Y H V Q j false C
local notation "π₀" => (R).orthogonalProjectionOnto
local notation "N" n:max => cap Y H V n Q Qc j false C
local notation "Test" => Vacancy.observable (tent Y H) false
local notation "Lab" => Beacon (tent Y H) false

local notation "Ch" => CapCharacter Y H V Q Qc j false C
local notation "χR" => phaseRead Y H V Q Qc j C
open CF.Pannier.Chancel Tapestry Papal SatinVerification

structure Witness (χ : Ch) (F : Family K) (w : SU.Slot) (s : ℕ)
    (X : Finset Cover) {m : ℕ} (u : Fin m → Cover) (O : Set RSpace) (e : ℝ) : Prop where
  physical : PhysicalTexture Y H F w s X u O (2 / precisionAt Λ s)
  before : 1/4 ≤ ‖E s F‖
  margin : e < ‖(χR χ) s F‖
  survives : ¬ CF.Pannier.Chancel.Parcel K (Window.family w) u X ((χR χ) s)
  ward (t : ℕ) (S : Finset Cover) : Scopes K S ((χR χ) t)
  -- All sufficiently large placements, with literal disjoint shields in physical RSpace
  -- even inside subsequent rungs (Projection/Placement.physical). Lower bounds paid upfront
  -- (Euclidean axis)
  separated (δ : ℝ) (p : 0 ≤ δ) : ∀ᶠ z in atTop, ∃ c : ℕ,
    Placement Y H j X s z δ c ∧ (¬ pairFactors j K z X (Window.family w) u ((χR χ) s)) ∧
      ∀ n : ℕ,
        let P := plow K j z X
        let x := relocate K j z F
        let G := stream Y H D s n (mirror K j 0 x)
        let F' := stream Y H D s n x
        G ∈ observ K (volumeAround Λ l n (reflectedBox j 0 P)) true ∧
        F' ∈ observ K (volumeAround Λ l n P) true ∧
        stream Y H D s n (afterShift j K z F F) = G * F' ∧
        (χR χ) (s+n) (G*F') = (χR χ) s (afterShift j K z F F) ∧
        (↑(e^2) : ℂ) < (χR χ) (s+n) (G*F')

lemma witnesses {χ : Ch} {F : Family (tent Y H)} {O : Set RSpace} {m s : ℕ} {X : Finset Cover}
    {u : Fin m → Cover} {w : SU.Slot} {e : ℝ} (he : 0 ≤ e)
    (p : PhysicalTexture Y H F w s X u O (2 / precisionAt Λ s))
    (q : 1/4 ≤ ‖E s F‖) (hc : e < ‖(χR χ) s F‖) :
    Witness Y H V Q Qc j C χ F w s X u O e := by
  refine ⟨p,q,hc,fun a=>?_,fun t S => phase_unit Y H V Q Qc j C t χ S,fun d z=>?_⟩
  · exact (norm_pos_iff.mp (lt_of_le_of_lt he hc)) ((phase_unit Y H V Q Qc j C s χ X).detects p.inject a p.initiates)
  exact (eventually_placement Y H j X s z).mono (fun v ⟨c,u⟩ => ⟨c,u,pair_survives Y H V Q Qc j C χ p he hc u⟩)

lemma excited (w : SU.Slot) (x : Cover) {q d v : ℕ} {A0 Z : ℝ} (p : Cornet Y H q d v A0 Z)
    (n₀ : ℕ) : ∃ (F : Family K) (s c : ℕ), n₀ ≤ s ∧
    (∀ j : Axis, ∀ C : Arena Y H Q.circuit j 0 false, ∃ χ,
      Witness Y H V Q Qc j C χ F w s (Sen x (payout d q v)) (booty x d q) (cabin c) (1/8)) := by
  obtain ⟨s,c,F,P,t,h⟩ := choose_fixed Y H V p n₀ w x
  refine ⟨F,s,c,P,fun j C=>?_⟩
  obtain ⟨f,r⟩ := excels Y H V Q Qc j false C s (e:=1/8) (by norm_num) (t.enter Y H false)
    (lt_of_lt_of_le (by norm_num) h)
  refine Exists.intro f (witnesses Y H V Q Qc j C (by norm_num) t h ?_)
  change 1/8 < ‖phaseRead Y H V Q Qc j C f s (t.enter Y H false).val‖
  rw [phase_read]; exact r

/-- Buy this component-diagnostic conclusion outright. One E, I and the same ground extensions
of it. For each slot (color index here), location, each maturity threshold; there is one test,
with actual stencil giving Witness on every axis. At this milestone, the character may still be
axis-dependent. -/
theorem bought_excitation (ε η : ℝ) (p : 0 < η) :
    ∃ (Λ : Preparation) (l : ℕ) (Z : ℝ), ε < Λ.x ∧ Λ.d ≤ η ∧
      Λ.nominated (VolumeCape.Dream.Nimbus l) ∧
      ∃ (H : Real.exp 1 ≤ Λ.x) (Y : Course Λ (VolumeCape.Dream.Nimbus l))
        (q d w : ℕ) (c : ℝ) (_ : Cornet Y H q d w c Z)
        (a b : ℕ → ℕ) (I : ℕ → Family (tent Y H) → ℕ → ℂ)
        (E : ℕ → Family (tent Y H) → ℂ)
        (V : Universal Y H a b I E) (D : GroundExtension (i := a) (k := b) (E := E) Y H),
        ∀ (z : SU.Slot) (x : Cover) (u : ℕ), ∃ (F : Family (tent Y H)) (s c' : ℕ), u ≤ s ∧
          (∀ j : Axis, Nonempty (Arena Y H D.history.circuit j 0 false) ∧
            ∀ C : Arena Y H D.history.circuit j 0 false, ∃ χ,
              Witness Y H V D.history D.clipped j C χ F z s (Sen x (payout d q w)) (booty x d q) (cabin c') (1/8)) := by
  obtain ⟨P, l, Z, large, bound, nom, H, Y, q, d, w, c, g, a, b, I, E, V, ⟨G⟩, _⟩ :=
    mixed_law_with_ground ε η p
  refine ⟨P,l,Z,large,bound,nom,H,Y,q,d,w,c,g,a,b,I,E,V,G,fun z x u=>?_⟩
  obtain ⟨F,s,c',w',v⟩ := excited Y H V G.history G.clipped z x g u
  exact ⟨F,s,c',w',fun j=> ⟨voyage_H Y H V G.history.circuit j 0 false,v j⟩⟩

end YM.CF.Buffered.Afterglow.Tower.Selection

open YM.CF.Buffered.Afterglow.Tower.Selection

#check @Placement
#check @Placement.physical
#check @PhysicalTexture
#check @PhysicalTexture.inGround
#check @CapCharacter
#check @square_cover
#check @rp_of_char
#check @ground_abelian
#check @gauge_in_cap
#check @access_scopes
#check @pairFactors
#check @Witness
#check @pair_survives
#check @bought_excitation
#print axioms PhysicalTexture.inGround
#print axioms cap_size
#print axioms gauge_in_cap
#print axioms ground_abelian
#print axioms Placement.physical
#print axioms pair_survives
#print axioms resolved_parts
#print axioms bought_excitation
