import YM.SU5.Selected.Pioneer

/-!
# Component on the SAME gauge polynomial resolution algebra as `SeasonCert`. Support and
heights as in that UV/period-limit theorem. For physical tests use `well` or `keep` (neutral)
as appropriate. Specify on the extended full even-mark space; use all operators at every level
with the same chosen parameter. Accounting off `FiniteGaugeDataPoly` is NOT a theorem here. Also ensure
coherence under Sunlight RP, locations, gauge Ward. Covariance from charge vanishing is not an
interaction price; see `Batten+Probe`. Uniqueness on neutral etc not included here yet.
-/
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 4500
set_option maxHeartbeats 240000
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

open Tapestry Exhibition Altitude
local notation "ℳ" => Dome (tent Y H)
-- satisfy all widths at the indicated preparations
local notation "pS" => Cloud (Dome (tent Y H))
local notation "Q₀" => FiniteGaugeDataPoly (tent Y H)
variable {Z: Rack Λ l} {P: Clay Λ l} (U: Exhibition Y H i k I E Z P)
local notation "L" => vistaDressing Y H U
local notation "q" => auxiliaryPad (tent Y H)
local notation "q₀" => groundAlgebra Y H V Q Qc j false C
variable (χ : CapCharacter Y H V Q Qc j false C)
local notation "M" s:max => liftCap Y H V Q Qc j false C s
local notation "f" s:max => marked Y H V Q Qc j false C χ s
variable (s:ℕ)

-- base & bridge lemma
abbrev bidding (x:ℳ) : Test:= ⟨x.val,x.property,fun p=>by cases p⟩
local notation "I₀" => bidding Y H

def capHeight : ℳ→ₗ[ℂ] ↑q₀ where
 toFun x:=(M s) (I₀ x)
 map_add' x y := read_add Y H V Q Qc j false C s (I₀ x) (I₀ y)
 map_smul' z x := read_scale Y H V Q Qc j false C s (I₀ x) z
local notation "h" s:max => capHeight Y H V Q Qc j C s
abbrev ray (χ:CapCharacter Y H V Q Qc j false C) : ℳ→ₗ[ℂ]ℂ:= χ.toAlgHom.toLinearMap.comp (h s)
local notation "k" χ:max s:max => ray Y H V Q Qc j C s χ -- binder order? definition s before χ? explicit #check tune!
-- do not bind k index later
include V Q Qc C
lemma arc_read (x:ℳ) : ray Y H V Q Qc j C s χ x=(f s) (I₀ x) := rfl
lemma arc_unit : (k χ s) 1=1:= (all_together Y H V Q Qc j false C χ).one s
lemma plastered_arc (s:ℕ) : (k χ (s+1)).comp ((L).surge s)=k χ s:= LinearMap.ext fun x=>by
 change (f (s+1)) (I₀ (liftD Y H s U x))=(f s) (I₀ x)
 rw [show I₀ (liftD Y H s U x)=upward Y H Q false (I₀ x) s 1 from Subtype.ext (seamless Y H Q U s x)]; exact (all_together Y H V Q Qc j false C χ).upward _ _ _

def bill (χ: CapCharacter Y H V Q Qc j false C) : pS→ₗ[ℂ] ℂ:= Decking.fadeRead (L) q (fun s=> k χ s) (plastered_arc Y H V Q Qc j C U χ)
local notation "uF" s:max=> vistaFinish Y H s U
local notation "J" χ:max=> bill Y H V Q Qc j C U χ
lemma cardHeight {x:pS}(u:x∈boardedDB (tent Y H) s): (J χ) x= (k χ s) ((uF s) x) := (L).fate s x q (fun s=> k χ s) _ u
lemma ultimately (x:pS)(p:x∈Q₀): ∀ᶠ s in atTop,(J χ) x=(f s) (I₀ ((uF s) x)):=by obtain ⟨t,w⟩:= Altitude.curve.mp p; refine (eventually_ge_atTop t).mono (fun i h0=>?_); exact cardHeight Y H V Q Qc j C U χ i (Altitude.climbs (Dome (tent Y H)) h0 w)
lemma ball_unit : (J χ) 1=1:= Decking.fadeOne _ _ _ (plastered_arc Y H V Q Qc j C U χ) (arc_unit Y H V Q Qc j C χ 0) -- arguments
lemma engaged (x:ℳ): (J χ) (pinhole ℳ s x)=(f s) (I₀ x):=by rw [cardHeight Y H V Q Qc j C U χ s (Altitude.short_pinhole s x),vistaFinish,Decking.outcrop]; rfl

lemma height_gauge(u:GPhysical)(x:pS)(p:x∈Q₀) : (J χ) (rainfall Λ K u x) = (J χ) x := by
 obtain ⟨i,v⟩:= curve.mp p; let t:= restrictG Λ i u; rw [cardHeight Y H V Q Qc j C U χ i (Tapestry.raining_height Λ K i u v),cardHeight Y H V Q Qc j C U χ i v, U.vistaRain Y H _ u x v]
 let w:= vistaFinish Y H i U x; obtain ⟨S,v⟩:= findsBay K w
 exact congrArg χ ((gauge_in_cap Y H V Q Qc j C i S t (I₀ w) (I₀ (pennant K t w)) ((Tapestry.locates ..).1 v) ((Tapestry.locates ..).1 (pennantLocal K S t v)) (pennantTrace K S t v)).symm)

-- orientation and locality. Projective-limit Euclidean polygram.
variable (a0:Axis)(p : Sunlight Λ)
local notation "α" => a0
local notation "ϑ" => Sunlight.oppose Λ α p K
local notation "Eplus" => Sunlight.sanctum Λ l α p K
local notation "Ec" n:max=> Sunlight.cloister Λ l α p K n
include U
lemma jurisdiction (R':Set ℕ)(X:Set RSpace){e:Bool}{x:pS}(v: x∈ jetty Λ l K e X (R' ∩ Set.Iic s)) : (uF s) x ∈ keep Λ l s K true X := crownShelter Λ l s (L) q (fun _ _=>rfl) X (fun i _=> roofline Λ l i true X U) (exposes _ _ _ _ _ _ v)
lemma conserveNeutral {t:Bool}{R':Set ℕ}{X:Set RSpace}{x:pS}(v:x∈ well Λ K l t X (R' ∩ Set.Iic s)): (uF s) x∈ keep Λ l s K true X ∧ (uF s) x∈ enclave K :=
 ⟨jurisdiction Y H V Q Qc j C U s R' X ((well_spec ..).mp v).1, U.finishCoherent Y H s x v (gateIssued Λ K l t X R' s v)⟩ -- tune
lemma marksRule (s':ℕ)(x y:pS)(p':p.start ≤ s')(e : x∈ Ec s')(v:y∈ Ec s'):
    (J χ) (ϑ x*y)= (k χ s') (aureole K α (p.marks s') ((uF s') x) * ((uF s') y)) := by
 rw [cardHeight Y H V Q Qc j C U χ s' ((shorter (Dome (tent Y H)) s').mul_mem (p.respectsCut Λ l α K e) (jettyBan Λ l K true _ (p.arena Λ) s' v))]; unfold vistaFinish; rw [reflectionHat Λ l α p s' (L) q (U.glass Y H a0 p) p' e v]

lemma tier_pos (x:pS)(e:x∈Eplus) : 0≤ (J χ) (ϑ x*x):=by
 obtain ⟨s,u,v⟩:= p.limitsArena Λ l α K e; let F:= vistaFinish Y H s U x
 obtain ⟨S,l',t⟩:= (show F∈keep Λ l s K true (flank a0 (p.hinge Λ)) from jurisdiction Y H V Q Qc j C U s (p.arena Λ) (flank α (p.hinge Λ)) v)
 have k':= (Tapestry.locates K S true).1 l'; have ht:= (p.rents Λ l α s u).1 t; obtain ⟨w,h'⟩:= p.shifted s u
 rw [marksRule Y H V Q Qc j C U χ α p s x x u v v,h']; rw [h'] at ht
 exact (all_together Y H V Q Qc j false C χ).rp s α w (I₀ F) S k' ht
lemma crossVolume {L':Type*}[Fintype L'](x:L'→pS)(e:∀ i,x i∈Eplus):
    (Matrix.of fun i j'=> (J χ) (ϑ (x i)*x j')).PosSemidef:= lustred (lustre (J χ) ϑ (Eplus).val.toLinearMap) (fun x=> tier_pos Y H V Q Qc j C U χ α p x.val x.property) (fun i=>(⟨x i,e i⟩: ↥Eplus))

-- μ barycenter on all such observables (gauge included with these laws). since support all, uniqueness probe concerns separate spacetime
variable (Z': Horizon Y H V Q Qc j false C)(hz: Law Y H V Q Qc j false C Z')
include hz
lemma full_measure (x:pS)(e:x∈ Q₀):
    Continuous (fun i=> (J (Z'.character i)) x) ∧ (∫ i,(J (Z'.character i)) x∂Z'.μ)= vistaTake Y H U x:=by
 obtain ⟨s,u⟩:= curve.mp e
 let F:= (uF s) x
 simp_rw [show ∀ i,(J (Z'.character i)) x= marked Y H V Q Qc j false C (Z'.character i) s (I₀ F) from fun i=> cardHeight Y H V Q Qc j C U (Z'.character i) s u]
 rw [vistaCall Y H s x U u]; exact many_accept Y H V Q Qc j false C Z' hz s (I₀ F)
end YM.CF.Buffered.Afterglow.Tower.Selection
