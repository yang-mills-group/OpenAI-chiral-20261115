import YM.SU5.CompassRose.Vista

noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxHeartbeats 500000
set_option quotPrecheck false
set_option linter.unusedSectionVars false

namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine

open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common Ballad Cordial
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
open Germ Alliance Lamour.Bridge.Celeste Designs Twah Prototype
open Lamour.Bridge.Celeste.Morn
open Spine Preparation.Yoke
open CF.Velvet CF.Pannier.Chancel CF.Pannier.Chancel.Rous Pressure
open YM.Stationary (Gaia)
open Onyx Regis.Circuit Regis.Head Regis.Head.Brecht Exterior Hiro

namespace Rose
open EmberWind Jewel
open Lamour Lamour.Bridge
variable (P:Spine)(s:ℕ)(A:ℝ)(β:ℕ→ℝ)
local notation "K"=> P.calibration
local notation "K!" f:max => Papal.household P.calibration f
local notation "P$" s:max => P.eReadL s
local notation "ζ⇒" => P.reflectTest 3
local notation "M$" => P.halfShift 3
local notation "lamp" X:max => temp (hat P.par.R.L P.par.x X)
open Fixture Shuttle Arrival
open Aria Casting DoseTravel SpinReceipt Basilica Vista
open Pitching.Focus QuadClock Preparation.Yoke

/-! # Compass Rose checkpoint (C1)
All estimates on the elected Spine P with shared field, positive block trajectory and actual
singleState on height `s`. Includes fixed physical separation after picking from AA
microscope appointments. Buys a `preserveEU` consultation on compact Mink-spacelike footprints
at that s (unlimited querying resolution t≥s) and genuine simultaneous payments of both marginals.
See `maintained`. This is a SPIN-CURVATURE Wake installment. Not (pure-gauge,pure-matter):
each field is itself mixed. and not a thin-field estimate; height dials of `sunset`, `sunrise`
are COSTED, they don't shrink with t. First unpaid estimates in checkpoint C1 writeup.
-/
namespace Forum
variable (x:P.Spectrum0 3)(v c:ℕ→ℕ)(T:Pools P v β)
local notation "k0" s:max=> request P A s
abbrev Earlier (i:ℕ) := arrivalW P i A β copper (downLey (k0 i))
abbrev LaterC (i:ℕ) := arrivalW P i A β copper 0
local notation "E0" s:max=> Earlier P A β s
local notation "E1" s:max=> LaterC P A β s
local notation "A0" s:max=> sunset P s A β
local notation "A1" s:max=> sunrise P s A β
local notation "p0" s:max=> viewQ P s A
local notation "p1" s:max=> viewT P s
abbrev foyer (i:ℕ) := entryA P (request P A i)
abbrev archway (_:ℕ) := KEntrance P 0
local notation "$λ" s:max => P.singleState 3 s x
noncomputable def δ : ℝ:= ‖onLey‖/2
lemma δ_pos : 0<δ:= half_pos (norm_pos_iff.mpr weight_dead)
structure LampCosts : Prop where
 -- polls read at outer height variable. epoch holds x/s in ONE vacuum
 pane_past : Tendsto (fun i=> ($λ (c i)) (E0 (c i))) atTop (𝓝 0)
 pane_forward : Tendsto (fun i=> ($λ (c i)) (E1 (c i))) atTop (𝓝 0)
 together : Tendsto (fun i=> ($λ (c i)) ((E0 (c i))*(E1 (c i)))) atTop (𝓝 onLey)

-- change order of c and β? #check
lemma net_cast (U:LampCosts P A β x c) : Tendsto (fun i=> P.selectedPanel (E0 (c i)) (E1 (c i)) (c i) x) atTop (𝓝 onLey):= by
 exact (show onLey-0*0=onLey from (by simp)) ▸ U.together.sub (U.pane_past.mul U.pane_forward)

include T
variable (p:A>0) (Q:P.Register) (i n:ℕ) (z:ℝ)
universe w
variable (K₀:PreparedInvestment P Q z n) (U:QualifiedWakeReadout.{w} P Q)(V:PhysicalWakeGram P)
local notation "F₀"=> foyer P A
local notation "V₁"=> archway P
-- can piggyback countable supplementary Polls & a.e. conditions
abbrev Seasons (P:Spine)(A:ℝ)(c:ℕ→ℕ)(x:P.Spectrum0 3): Prop:= HoldRead P A c x (-leyline) 0 (foyer P A) (archway P)
include p K₀ U V
lemma make_poll {I:Type}[Countable I](d:ℕ→ℕ)(u:StrictMono d)(X:I→ℕ→P.Test)(Y:I→ℂ)(t:∀ i,WakePoll P (X i) (Y i)):∃ c:ℕ→ℕ,StrictMono c ∧
    ∀ H:P.Spectrum0 3→Prop,(∀ᵐ x∂ P.pillars 3,H x)→∃ x,H x∧JointTuple.{w} P Q x ∧ Seasons P A (d ∘ c) x ∧ LampCosts P A β x (d ∘ c) ∧ ∀ i,Tendsto (fun r=> P.singleState 3 (d (c r)) x (X i (d (c r)))) atTop (𝓝 (Y i)):=by
 obtain ⟨w,W⟩:=K₀.investment; let F:=F₀; let G:=V₁; let t₀:P.PencilLease A (-leyline) 0 F G:= Vista.fork_lease P A p; let L:=Earlier P A β; let D:=LaterC P A β; let J:=I⊕ Unit ⊕ Bool; let F':Unit ⊕ Bool→ℕ→P.Test := Sum.elim (fun _=>L*D) (usher L D); let f':Unit ⊕ Bool→ℂ:= Sum.elim (fun _=>onLey) (fun _=>0); let Z:J→ℕ→P.Test:=Sum.elim X F'; let R:J→ℂ:= Sum.elim Y f'
 have he(i:J):WakePoll P (Z i) (R i):=by
    rcases i with a|(a|(a|a))
    · exact t a
    · exact two_lamp P A β v T F G (-leyline) 0 p t₀.p0 t₀.p1 (neg_ne_zero.mpr ley_seen) copper copper rfl V W K₀.dispatch K₀.rocky.merit
    · exact one_lamp P A β v T F (-leyline) p t₀.p0 copper V W K₀.dispatch K₀.rocky.merit
    exact one_lamp P A β v T G 0 p t₀.p1 copper V W K₀.dispatch K₀.rocky.merit
 obtain ⟨C,f,g⟩:= U A p (-leyline) 0 F G J d u t₀ Z R he; refine ⟨C,f,fun H h=>?_⟩; obtain ⟨x,H,h,e,z⟩ :=g H h; exact ⟨x,H,h,e,⟨z (.inr (.inr false)),z (.inr (.inr true)),z (.inr (.inl ()))⟩,fun i=> z (.inl i)⟩
omit T K₀ U V

structure Ledger (F G:SampleDose)(a:ℝ) : Prop where
 plaza : Plaza P (A0 s) (A1 s) (p0 s) (p1 s)
 contact_lease : δ < ‖P.selectedPanel (E0 s) (E1 s) s x‖ -- not 'contact terms'; center alignment is spacelike
 consultation : Basilica.preserveEU P x 3 (A0 s) (A1 s) F G a δ

-- grind
variable (J:P.Ellis 3 x)
include J
lemma sighting (e:StrictMono c)(b:LampCosts P A β x c) : ∀ᶠ i in atTop,∃ F G a, Ledger P (c i) A β x F G a:=by
 have he:δ< ‖onLey‖:= half_lt_self (norm_pos_iff.mpr weight_dead)
 filter_upwards [(net_cast P A β x c b).norm.eventually (lt_mem_nhds he),e.tendsto_atTop.eventually (openDoors P A β p)] with i ei t
 let s:=c i; let V:=A0 s; let W:=A1 s; let L:= E0 s; let D:=E1 s; let Q:= P.selectedPanel L D s x
 let v:=viewQ P s A; let u:= viewT P s; let k:=pre0 (request P A s)
 have hx: P.issuing s V k= L:= exact_rit P s A β _ _; have hv:P.issuing s W sunrise0=D:=exact_rit P s A β _ _
 have hp: δ<‖P.bodyPair x V W v u-P.bodyOne x V v*P.bodyOne x W u‖:=by
    rw [← show ($λ s) (P.issuing s V k*P.issuing s W sunrise0)=_ from (pave_gram P s x J V W k sunrise0 (Eq.refl s|>.le) (Eq.refl s|>.le) t),← show ($λ s) (P.issuing s V k)=P.bodyOne x V v from (P.castAt_price x J V (Eq.refl s|>.le) k),← show ($λ s) (P.issuing s W sunrise0)= P.bodyOne x W u from (P.castAt_price x J W (Eq.refl s|>.le) sunrise0),hx,hv]; exact ei
 obtain ⟨F,G,d,y⟩:= sale P x J 3 V W v u δ t hp; exact ⟨F,G,d,t,ei,y⟩

omit p
local notation "PX₀" => A0 s
local notation "PX₁" => A1 s
-- flatten the local permissions: concrete Pair from a Ledger. including marginal convergence,
-- keep cost asserted on all finer resolution ESTIMATORS and on those fixed physical footprints.
theorem maintained (F G:SampleDose)(d:ℝ)(Q:Ledger P s A β x F G d):
    let L:= A0 s; let R:= A1 s
    let U(k):= P.prepared k L F; let V(k):= P.prepared k R G
    let G₀:= inner ℂ (DoseTravel.beam _ F (Basilica.Past P x 3 L d)) (DoseTravel.beam _ G (Basilica.FutureC P x 3 R d))
    let cL:= P.bodyOne x L (0:Vantage); let cR:= P.bodyOne x R (0:Vantage)
    let X:=P.spacePrice L F; let Y:=P.spacePrice R G
    F.Normalized ∧ G.Normalized ∧ δ>0 ∧
    (∀ y∈X,∀ z∈Y, (∀ i:Axis,y i< z i) ∧ (WithLp.toLp 2 (z-y):E4) ∈ Mink.spacelike) ∧
    IsCompact X ∧ IsCompact Y ∧ Disjoint X Y ∧
    -- factored point kernel assertion and Plaza around every smearing point pair
    (∀ a∈tsupport F.val,∀ b∈tsupport G.val, Basilica.Plaza P L R a b ∧
        P.bodyPair x L R a b = inner ℂ (Basilica.Past P x 3 L d a) (Basilica.FutureC P x 3 R d b)) ∧
    (∀ t≥s, U t∈enclave P.calibration ∧ P.asked_at t (U t) X ∧ V t∈enclave P.calibration ∧ P.asked_at t (V t) Y) ∧
    Tendsto (fun t=> P.singleState 3 t x (U t)) atTop (𝓝 cL) ∧
    Tendsto (fun t=> P.singleState 3 t x (V t)) atTop (𝓝 cR) ∧
    Tendsto (fun t=> P.selectedPanel (U t) (V t) t x) atTop (𝓝 (G₀-cL*cR)) ∧
    δ < ‖G₀-cL*cR‖ ∧ ∀ᶠ t in atTop, δ< ‖P.selectedPanel (U t) (V t) t x‖ :=by
 intro L R V W G0 cL cR X Y; let Z:= Q.consultation; let he(t:ℕ)(p:s≤ t):= EU_local P t x 3 L R F G d δ p p Z; let G':= he s le_rfl; obtain ⟨g,f,k,r⟩:= EU_read P x J 3 L R F G d δ Z; refine ⟨Z.normF,Z.normU,δ_pos,G'.1,G'.2.2.1,G'.2.2.2.1,G'.2.1,fun y p z e=> ⟨Z.billing _ p _ e,two_born P x J 3 L R d y z (Z.past y p) (Z.soon z e)⟩,fun t p=> ?_, g,f,k,Z.more,r⟩
 obtain ⟨a,b⟩:= (he t p).2.2.2.2; exact ⟨a.1,a.2,b⟩
omit J
-- A ↑ in inspection granularity (Z tint may chosen externally in Lean but is existence binder only)
open SpinReceipt
lemma t_Ellis (B':JointTuple.{w} P Q x):∃ _:P.Ellis 3 x,True:=by
 obtain ⟨w,r,R,Y⟩:=B'; exact ⟨R,trivial⟩

-- public milestone type. Preserves initiated both pool indexes and A/f heights extraction and any extra a.e. consents without losing other appointment cost `Seasons`.
structure PorchLedger (P:Spine)(Q:P.Register)(n:ℕ)(z:ℝ) : Prop where
 investment : PreparedInvestment P Q z n
 pose : PureForce.CakeL.SignedPoseBudget P
 read : QualifiedWakeReadout.{w} P Q
 gram : PhysicalWakeGram P
 unfoldsFive (v:ℕ→ℕ)(p:StrictMono v) :∃ (β:ℕ→ℝ)(g:ℕ→ℕ),StrictMono g ∧ Pools P (v ∘ g) β ∧
    ∀ A>0, P.PencilLease A (-leyline) 0 (foyer P A) (archway P) ∧
      ∀ (I:Type) [Countable I](f:ℕ→ℕ), StrictMono f→∀ (Z:I→ℕ→P.Test)(Y:I→ℂ),(∀ i, WakePoll P (Z i) (Y i))→
      ∃ (b:ℕ→ℕ), StrictMono b ∧ ∀ U:P.Spectrum0 3→Prop,(∀ᵐ x ∂ P.pillars 3, U x) →∃ x:P.Spectrum0 3,
      U x∧JointTuple.{w} P Q x∧ LampCosts P A β x (f ∘ b)∧ Seasons P A (f∘b) x ∧ (∀ i,Tendsto (fun t=> P.singleState 3 (f (b t)) x (Z i (f (b t)))) atTop (𝓝 (Y i))) ∧ ∀ᶠ i in atTop, ∃ F G a, Ledger P (f (b i)) A β x F G a

theorem produce (b:PreparedInvestment P Q z n)(k:PureForce.CakeL.SignedPoseBudget P)(p:QualifiedWakeReadout.{w} P Q)(S:PhysicalWakeGram P): PorchLedger.{w} P Q n z:=by
 refine ⟨b,k,p,S,fun v w=>?_⟩; obtain ⟨g,β,h,g'⟩:= warp_pool P v w; refine ⟨β,g,h,g',fun A z'=>⟨Vista.fork_lease P A z',?_⟩⟩; intro I wi f t Z Y H; obtain ⟨c,y,Y'⟩:= make_poll P A β (v∘g) g' z' Q n z b p S f t Z Y H; refine ⟨c,y,fun U e=>?_⟩; obtain ⟨x,h,W,Q',C,N⟩:= Y' U e; obtain ⟨J,u⟩:=t_Ellis P x Q W; exact ⟨x,h,W,C,Q',N,sighting P A β x _ z' J (t.comp y) C⟩
theorem compass_rose_installment (X : TintDemand) (n:ℕ): ∃ (P:Spine)(Q:P.Register)(z:ℝ), PorchLedger.{w} P Q n z:=by
 obtain ⟨P,K₀,E,i,p,r,g⟩:= Spine.wakeElectionWithPhysicalGram.{w} X n; exact ⟨P,K₀,E,produce P K₀ n E i p r g⟩
#print axioms maintained
#print axioms compass_rose_installment
end Forum
end Rose
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine
