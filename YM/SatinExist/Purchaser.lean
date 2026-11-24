import SatinProbeCompatibilityNovember6
import YM.SatinExist.Relume
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 2000
set_option maxHeartbeats 280000
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
open OS.Semigroup (F)
open OS.Semigroup.Balloon
open Set
variable (P:Spine)(x:P.Spectrum0 3)(Z:Lead.Clan)(k:Street)(s:ℕ)(c r:ℕ→ℕ)
local notation "β" => P.otherSpectrum 3 3 x
local notation "S" => P.physicalEnergy 3 (β)
local notation "V" => P.ColorHil 3 (β)
local notation "Ψ" => P.voyageF 3 (β)
local notation "yb@" i:max=> P.shard x Z (c (i:ℕ)) (r (i:ℕ))
local notation "ρ" i:max=> P.dew (c (i:ℕ)) (r (i:ℕ))
local notation "Γ" => marks (timeMesh P.par)
local notation "Nt" => notch (timeMesh P.par)
open Aria Casting Six
local notation "H"=> P.ColorHil 3 (β)
local notation "B"=> P.par.block
local notation "l₀"=> P.width
local notation "Λ"=> P.par
local notation "K"=> P.calibration
local notation "q@" n:max => P.asked_at n
local notation "ρₛ" t:max=> Selected.gaugeMesh Λ t
local notation "θ" t:max => Selected.gaugePosition Λ t
local notation "ℓ"=> P.calibration.ℓ
-- horizontal/integer growth from ANY mixed roster, keeping every stencil at SAME height. useful later for pure/pure.
variable (j:Axis)
private lemma academy (n:ℤ)(f: Family K)(h:LinkIndependent K f) : LinkIndependent K (Tower.mirror K j n f):=by intro i a b; change _root_.YM.CF.Fock.theta _ _=_root_.YM.CF.Fock.theta _ _; exact congrArg _ (h i _ _)
lemma copyIndependent {u:P.Test}(h:PureMatter K u)(n:ℤ): PureMatter K (P.shifts j n u):= P.academy j _ _ (P.academy j _ _ h)
lemma stamp_title (n:ℤ)(z:P.Test): P.singleState 3 s x (P.shifts j n z)= P.singleState 3 s x z:=by
 rw [←P.single_agrees 3 j x, ←P.single_agrees 3 j x _ z,P.single_state,P.single_state]
 exact congrArg _ (P.shifted_read j s n z)
local notation "ϕ"=> P.singleState 3 s x
local notation "ξ"=> P.advocate 3 x j
local notation "ω"=> P.ColorHil j ξ
local notation "e₀"=> P.physicalEnergy j ξ
lemma mint_ordered_label (f g:P.Test) (a:P.birthF j s (P.reflectTest j f))(b:P.birthF j s g)(n:ℕ):
    ϕ (f*P.shifts j (n:ℤ) g)=inner ℂ (P.viewF j ξ s a) ((e₀).E (whenly (timeMesh Λ) s n) (P.viewF j ξ s b)):=by
 rw [← P.single_agrees 3 j x, ← P.releasedLater j ξ s n b]
 exact (P.released_gram j ξ s a _|>.trans (congrArg (P.singleState j s ξ ∘ (· * P.shifts j (n:ℤ) g)) (aureoleTwice K j 0 f))).symm
variable (F G: Lead.Clan→ P.Test)
def ticketRank : CrossRead := Matrix.of (fun i j=> ϕ (F i * G j))
lemma stroll_price (e:∀ i,P.birthF j s (P.reflectTest j (F i))) (f:∀ i,P.birthF j s (G i)) (h:ReadsSix (P.ticketRank x s F G)) :
    ∃ᶠ n:ℕ in atTop, ReadsSix (P.ticketRank x s F (fun i=> P.shifts j (n:ℤ) (G i))) := by
 let X(i):= P.viewF j ξ s (e i); let Y(i):= P.viewF j ξ s (f i)
 let Q:= _root_.YM.SatinExist.Lancet.ahead (e₀) X Y; let L:= mill (timeMesh Λ) s
 have Hp(n:ℕ): P.ticketRank x s F (fun i=> P.shifts j (n:ℤ) (G i))=Q (n * (L:ℝ)) := by
    have ht:(((n:ℝ)*(L:ℝ)).toNNReal)= whenly (timeMesh Λ) s n:= by ext; unfold whenly; push_cast; rw [Real.coe_toNNReal _ (by positivity)]
    ext a b
    change ϕ _=inner ℂ (P.viewF j ξ s (e a)) ((e₀).E _ _)
    rw [P.mint_ordered_label x s j (F a) (G b) (e a) (f b) n,ht]
 have hv : Q 0=P.ticketRank x s F G:=by
    rw [show (0:ℝ)=(0:ℕ)*(L:ℝ) by simp,←Hp]; simp_rw [Nat.cast_zero,P.shifts_zero]
 let Z:= _root_.YM.SatinExist.Lancet.happy_clock e₀ X Y (show ReadsSix (Q 0) from hv.symm ▸ h) (L:ℝ) (mill_pos ..) -- tune
 exact Z.mono fun i q=> (Hp i).symm ▸ q
private lemma translated_bill (p:ℤ): P.ticketRank x s (fun i=> P.shifts j p (F i)) G= P.ticketRank x s F (fun i=>P.shifts j (-p) (G i)):=by
 ext i k; change ϕ _=ϕ _
 rw [← P.stamp_title x s j (-p) _,map_mul,P.shifts_sum,neg_add_cancel,P.shifts_zero]
lemma pre_stroll_price (e:∀ i,P.birthF j s (P.reflectTest j (F i))) (f:∀ i,P.birthF j s (G i)) (h:ReadsSix (P.ticketRank x s F G)) :
    ∃ᶠ n:ℕ in atTop, ReadsSix (P.ticketRank x s (fun i=> P.shifts j (-(n:ℤ)) (F i)) G) := by
 refine (P.stroll_price x s j F G e f h).mono (fun i p=> ?_); simpa only [translated_bill,neg_neg] using p
-- support height s packages. collinear monotone clearance all axes. Two directions separately at this layout.
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
