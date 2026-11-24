import YM.SU5.Selected.Arrive
import YM.SU5.Selected.JointAverages
/-!
# Test on the joint ground of the very same pre-Lorentz resolution Hilbert space

Ground selection using every integer `mesh-when` even step of every positive-time pose,
every analogous spatial movement from that resolution. Fixed space of MANY Vec is a limit of
explicit arithmetic inside the pruner. Needed before disintegrating. These spatial parameters
are in *same* double-step units as mesh; spatial test spacing halving/multiplication below.
-/
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 4500
set_option maxHeartbeats 320000
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
  (j : Axis) (r : Bool) (C : Arena Y H Q.circuit j 0 r)
local notation "R" => Aurora Y H V Q j r C
local notation "A" => Ark.Ht Y H Q.circuit j 0 r C
local notation "W" => floorV Y H Q.circuit j 0 r C
local notation "F₊" n:max => Tower.Field Y H n j 0 r
local notation "φ" n:max => actor Y H n Q.circuit j 0 r C
local notation "Ω" => seat0 Y H V Q j r C
local notation "π₀" => (R).orthogonalProjectionOnto
local notation "N" n:max => cap Y H V n Q Qc j r C
local notation "Test" => Vacancy.observable (tent Y H) r
local notation "Lab" => Beacon (tent Y H) r

local notation "B" => groundAlgebra Y H V Q Qc j r C
local notation "Β" => pruner Y H V Q Qc j r C
local notation "M" s:max => liftCap Y H V Q Qc j r C s
local notation "uℋ" => basisRoom Y H V Q j r C
local notation "U₀" s:max => timePruner Y H V Q Qc j r C s
local notation "p₀" s:max => spacePruner Y H V Q Qc j r C s
local notation "τ" s:max => tick Y H s j 0 r
local notation "ρ" s:max => ripple Y H V s Q.circuit j 0 r C
local notation "P₀" s:max => stretches Y H V Q Qc j r C s
variable {χ : CapCharacter Y H V Q Qc j r C} (U : Birthplace Y H V Q Qc j r C χ)
local notation "λ₀" => vacuum Y H V Q Qc j r C U
local notation "η" s:max => markedActor Y H V Q Qc j r C U s
local notation "η₀" => leave Y H V Q Qc j r C U
open Companies
abbrev Exercise (a : Axis) := ℕ × (ℕ ⊕ (Trans a × ℤ))
def exercise : ℕ → Exercise j := (exists_surjective_nat (Exercise j)).choose
lemma used : Surjective (exercise j) := (exists_surjective_nat (Exercise j)).choose_spec

local notation "F₀" => journey Y H V Q Qc j r C U
local notation "F" => Exercise j

def hat (x : Exercise j) : Β := Sum.elim (fun i => (U₀ x.1) (2*i)) (fun i => (p₀ x.1) i.1 (2*i.2)) x.2
abbrev queue (n : ℕ) := hat Y H V Q Qc j r C (exercise j n)
local notation "L₀" => queue Y H V Q Qc j r C

abbrev efforts (n : ℕ) := (L₀ n).val
local notation "Υ" => efforts Y H V Q Qc j r C

include V Q Qc C
lemma hat_le (n : ℕ) : ‖Υ n‖≤1:=by
  rcases h : exercise j n with ⟨i,t|⟨t,k⟩⟩ <;> unfold efforts queue <;> rw [h]
  exact atom_smalls Y H V Q Qc j r C _ _
  exact space_cost Y H V Q Qc j r C _ _ _

lemma turnoff : stationary A Υ= R := by
  ext x
  rw [standing (A) Υ x (hat_le Y H V Q Qc j r C), Vacancy.Aurora, Submodule.mem_iInf]
  let D₀ := clockdrive Y H V Q.circuit j 0 r C
  constructor
  · intro t
    have w (e : F) : (hat Y H V Q Qc j r C e).val x=x:= by obtain ⟨i,rfl⟩ := used j e; exact t i
    have h(i t : ℕ): (ρ i) (2*t) x=x:= w ⟨i,Sum.inl t⟩
    intro i; apply (formal Y H V i Q j r C x).2; exact ⟨D₀.track_invariant x h, fun v k => w ⟨i,Sum.inr (v,k)⟩⟩
  intro p i; have hv (i:ℕ):= (formal Y H V i Q j r C x).1 (p i)
  rcases h : exercise j i with ⟨i,t|⟨t,k⟩⟩ <;> unfold efforts queue <;> rw [h]
  · exact (show (D₀.double i t) x=x by rw [←D₀.track_even]; exact (hv i).1 _)
  exact (hv i).2 t k

abbrev phaseMoves (n : ℕ) := η₀ (L₀ n)
local notation "T" => phaseMoves Y H V Q Qc j r C U
abbrev bottom := Companies.stationary U.H T
local notation "Θ" => bottom Y H V Q Qc j r C U -- P₀ existing (overload) fix
include U
lemma motion_cost (n : ℕ) : ‖T n‖ ≤ 1:= (reserve_norm Y H V Q Qc j r C U (L₀ n)).trans (hat_le Y H V Q Qc j r C n)

omit V Q Qc C U in
private lemma play_i (X : Hilbert) (Y : Mesh) (F' : Many Y X) (K' : Exercise j→ X.Op) (x : X) :
    (∀ n,K' (exercise j n) x=x) ↔ ((∀ i n,K' ⟨i,Sum.inl n⟩ x=x) ∧ (∀ i (v : Trans j) (z:ℤ),K' ⟨i,Sum.inr (v,z)⟩ x=x)) := by
  constructor
  · intro h; have he (s : Exercise j) : K' s x=x:=by obtain ⟨i,rfl⟩:=used j s; exact h i
    exact ⟨fun _ _=>he _,fun _ _ _=>he _⟩
  intro p i; rcases h:exercise j i with ⟨a,k|⟨k,t⟩⟩; exact p.1 _ _; exact p.2 _ _ _
omit V Q Qc C U in
private lemma through (X : Hilbert) (Y : Mesh) (F' : Many Y X) (x : X):
    (∀ i n,F'.double i n x=x) ↔ (∀ t:ℝ≥0,F'.track t x=x) :=
 ⟨fun p=>F'.track_invariant x p, fun h i n=> (congrArg (fun z:X.Op=> z x) (F'.track_even i n).symm).trans (h _)⟩
lemma grounded (x : U.H) : x∈ Θ ↔ (∀ t:ℝ≥0,(F₀).track t x=x) ∧
    ∀ (i:ℕ) (v : Trans j) (z:ℤ), travel_χ Y H V Q Qc j r C U i v (2*z) x=x :=
  ((Companies.standing U.H T x (motion_cost Y H V Q Qc j r C U)).trans
    (play_i j U.H (timeMesh Λ) F₀ (fun v:Exercise j=>η₀ (hat Y H V Q Qc j r C v)) x)).trans (and_congr (through _ _ (F₀) x) Iff.rfl)
lemma apt_floor : λ₀ ∈ Θ:= (grounded Y H V Q Qc j r C U λ₀).2
    ⟨time_floor Y H V Q Qc j r C U, fun i v z => travel_floor Y H V Q Qc j r C U i v _⟩

abbrev rounder (n : ℕ) : Β := Companies.blend (L₀) n
abbrev verdict (n i : ℕ) : Β := Companies.mix (rounder Y H V Q Qc j r C n) i
omit U
lemma round_main (n i : ℕ) :
    (verdict Y H V Q Qc j r C n i).val=Companies.mix (Companies.blend Υ n) i := by
  let f := ((Β).subtype).toAlgHom
  have hk : f ∘ L₀ = Υ := rfl
  change f (Companies.mix (Companies.blend (L₀) n) i) = _; rw [Companies.mix_map,blend_map,hk]
include U
lemma round_after (n i : ℕ) :
    η₀ (verdict Y H V Q Qc j r C n i)=Companies.mix (Companies.blend T n) i :=
  (Companies.mix_map (η₀).toAlgHom (rounder Y H V Q Qc j r C n) i).trans (congrArg (fun x => Companies.mix x i) (blend_map (η₀).toAlgHom (L₀) n))
end YM.CF.Buffered.Afterglow.Tower.Selection
