import YM.SU5.Registration.Rasp.PitchJet
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 3000
set_option maxHeartbeats 400000
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
open Spine
open CF.Velvet CF.Pannier.Chancel
open QuadClock
open Aria Casting MacroGrid Preparation.Yoke Yoke.Travel
open SatinNucleus Six DoseTravel Set
open SatinRegistration
namespace Spine
variable (P:Spine)
-- geometry ANY axes
local notation "Χ"=>P.Spectrum0
local notation "Θ"=>P.advocate 3
local notation "E₀"=>P.ColorHil
local notation "H₀"=>P.ManyF
local notation "qz"=>P.wealth
local notation "S₀"=>P.seasons
variable (x:P.Spectrum0 3)(a:Axis)
local notation "ξ"=>Θ x a
local notation "S"=>(P.seasons a (P.advocate 3 x a))
local notation "H"=>(P.ColorHil a (P.advocate 3 x a))
local notation "G"=>(P.ManyF a (P.advocate 3 x a))
local notation "pc"=>P.cartage a (P.advocate 3 x a)
local notation "T₀"=> (S).E
local notation "Ω"=> P.heaven a ξ
local notation "T"=> timeMesh P.par
open Swatch
local notation "τ" p:max=> Real.toNNReal (p:ℝ)
local notation "GOp" x:max=> (P.ManyF a (P.advocate 3 x a)).Op
local notation "Θ'" x:max=> P.seasons a (P.advocate 3 x a)
local notation "Φ"=>P.Spectrum0 3
open _root_.YM.SatinEdge.RealSheet Boundary Probe
open SatinRegistration
open Grading
open scoped CF.Buffered.Afterglow.Hierarchy.Seld
open Swatch Aria Casting SatinJets OS.Semigroup
/-!
 # Unpadded jets for ALL stamps in the M8 passport extension

 These are fields on the very M5 domain. In the given M4 interpretation,
 the real-time cross experiments are prices on such point-operator limits.
 Include support rule for the identification; not Lorentz covariance yet.
 Use the positive time prices; the reading of M4 Smears remains Eu.
-/
variable (Y:P.Swatch)
-- simplify address. same field at any dense budget (in this axis).
local notation "D"=> radial S
abbrev temporalField (u:Y.WPermit x a):= SatinRegistration.field (P.seasons a (P.advocate 3 x a)) u.delivery.accepts u.delivery.isSound u.delivery.paid
lemma turn_ticket (u:Y.WPermit x a)(v:(Y.turn a).WPermit x a): v.atHeat=fun s=>(u.atHeat s).adjoint:= u.delivery.reverse v.delivery (fun s i=> (Y.Wstage_turn x a i s s).symm)
lemma turn_public (u:Y.WPermit x a): P.temporalField x a (Y.turn a) (u.reflector x a Y)= SatinRegistration.adj S u.atHeat u.delivery.isSound u.delivery.paid:=by
 have h:= P.turn_ticket x a Y u (u.reflector x a Y)
 unfold adj temporalField; congr
lemma temporal_inner (u:Y.WPermit x a)(x₁ x₂:D) (f:Test4) : inner ℂ (P.temporalField x a Y u f x₁).1 x₂.1= inner ℂ x₁.1 (P.temporalField x a (Y.turn a) (u.reflector x a Y) (bar f) x₂).1 := (by rw [P.turn_public x a Y u]; exact field_adjoint ..)

variable (A:ℕ→ P.Apron)(s: Set P.Swatch)
lemma point_published (u:(ordinary A).WPermit x 3) (t:P.CapReady x A): P.temporalField x 3 _ u=P.pointField x A t:=P.affine_field x A t
universe v
local notation "j₁"=> (3:Axis)
local notation "ξ₁" x:max=> P.advocate 3 x j₁
local notation "G₁" x:max=> P.ManyF j₁ (ξ₁ x)
local notation "T₁" x:max=> P.seasons j₁ (ξ₁ x)
local notation "𝒯"=>P.temporalField x 3
local notation "QA"=> ordinary A
local notation "QB"=> ordinary (fun i=> P.drumStep (A i))
local notation "Qc" n:max=> ordinary (fun i=> P.festival (A i) n)
variable (q:Tendsto (fun i=>(A i).s) atTop atTop) (w:Prism) (U:(Swatch.ordinary A).WPermit x 3)
include q
lemma issuerJet (v:(QB).WPermit x j₁) (f:Test4): P.temporalField x j₁ QB v f=P.temporalField x j₁ QA U (timeJet j₁ f):=
 roster_jet (T₁ x) U.atHeat U.delivery.paid U.delivery.isSound v.atHeat v.delivery.isSound v.delivery.paid (fun s t=>P.paysMusic x A s t U v q) f -- order? check
omit q
noncomputable def rideScore : ℕ→ Test4→L[ℂ] Test4
 | 0=>ContinuousLinearMap.id ℂ Test4
 | n+1=> (rideScore n).comp (timeJet 3)
lemma ride_respects (n:ℕ)(f:Test4) : tsupport (rideScore n f)⊆tsupport f:=by induction n generalizing f with| zero=> exact _root_.le_refl _|succ n ih=> exact subset_trans (ih (timeJet 3 f)) (time_reach 3 f)
variable (h:StillCurtain.{v} P 3 s (Swatch.ordinary A)) -- careful macros in variable
include q h
lemma stageBoot (n:ℕ)(Z:(Qc n).WPermit x 3)(f:Test4) : P.temporalField x 3 _ Z f= P.temporalField x 3 _ U (rideScore n f):=by
 induction n generalizing f with
 | zero=> rfl
 | succ n ih=>
    let Bₙ (i):= P.festival (A i) n; let t:= ((P.festival_all_peaks x A s h q n).card P 3 s _).all x; exact (P.issuerJet x Bₙ (by simpa only [Bₙ, P.festival_s] using q) t Z f).trans (ih t _)
noncomputable def drumF (f:Test4) : Test4:= ∑ i∈w.support,w i • rideScore (i+1) f
lemma stageReady (W:(P.selectionBand A w).WPermit x j₁) (f:Test4): P.temporalField x 3 _ W f=P.temporalField x 3 _ U (drumF w f):=by
 let T'(i:ℕ):= ((P.festival_all_peaks x A s h q (i+1)).card P 3 s _).all
 have he(s':ℝ≥0)(t:0<s'): W.atHeat s' = ∑ i∈ w.support,w i • (T' i x).atHeat s':= (issuing_music P x A s h q w).all_heat P x 3 _ _ _ _ T' W s' t
 have hu:= field_score (T₁ x) W.atHeat W.delivery.paid W.delivery.isSound w.support (fun i=>(T' i x).atHeat) (fun i=>w i) f (fun i=>(T' i x).delivery.isSound) (fun i=>(T' i x).delivery.paid) he; have ht:(𝒯 _ U) (drumF w f)=∑ i∈ w.support,w i • ((𝒯 _ U) (rideScore (i+1) f)):=by unfold drumF; rw [map_sum]; simp only [map_smul]
 rw [ht]; refine hu.trans (sum_congr rfl (fun i _=> congrArg ((w i) • ·) (P.stageBoot x A s q U h _ (T' i x) f))) -- `stageBoot` order `q U h`? see `#check`
omit q h
private lemma test_pay (w:ℂ)(f:Test4) : tsupport (w • f) ⊆ tsupport f:= tsupport_comp_subset (g:=fun x:ℂ=>w • x) (smul_zero _) f
lemma drum_time (f:Test4): tsupport (drumF w f) ⊆ tsupport f:=by
 -- Mathlib tsupport Finset sums or simple induction pass
 have hz(l:Finset ℕ): tsupport ((∑ i∈ l,w i • rideScore (i+1) f):Test4) ⊆ tsupport f:=by
    induction l using Finset.induction_on with
    | empty=> rw [sum_empty]; change tsupport (0:E4→ℂ) ⊆ _; simp
    | insert i l p u=> rw [sum_insert p]; exact subset_trans (tsupport_add _ _) (union_subset (subset_trans (test_pay ..) (ride_respects ..)) u)
 exact hz w.support

-- Transfer to actual stencil; use ONE protagonist for Handle even on all-spectrum read statements.
section filings
variable (y:P.Spectrum0 3) (c r n:ℕ→ℕ)(w:Lead.Clan→ Prism)(Z:Lead.Clan)(X:P.HandleWith y c r A n)(T':P.ThinHere (P.ClaimedAt c r n A Z))(V:∀ x:P.Spectrum0 3,P.Guest x c r A n)(b:Tendsto (fun i=> c (n i)) atTop atTop)
local notation "W₁"=> ordinary (P.soldTrumpet A c r n w Z)
local notation "U₁"=> ordinary (P.ClaimedAt c r n A Z)
local notation "ζ"=> (purePrice Z:ℂ)
local notation "Qν"=>P.ClaimedAt c r n A Z
include h X T' V b
noncomputable abbrev stageTest (W:Lead.Clan→ Prism) (Z:Lead.Clan) (f:Test4):Test4 := (purePrice Z:ℂ) • drumF (W Z) f -- binder `ζ` with macros? omit b V etc
lemma signatureAct (T₁':(W₁).WPermit x j₁) (f:Test4): P.temporalField x j₁ _ T₁' f = P.temporalField x j₁ _ U (stageTest w Z f):=by
 let v:= h.card P 3 s QA; let g:= P.seam_score_all y A c r n Z X T' V v; -- maybe order? y before A StillMusic.
 let Xν:=(g.cinematic P 3 s _ _ _ _ (fun _=>h) (P.material_thin A c r n Z T')); let Yν:= Xν.card P 3 s U₁; let q:= Yν.all x
 let U':=v.all; have hz(t:ℝ≥0)(p:0<t): q.atHeat t=ζ • (U).atHeat t:=by
    rw [g.all_heat P x j₁ _ _ _ _ (fun _=>U') _ t p]; simp -- proof irr maybe tune
 let Z':=drumF (w Z) f
 have hX:= field_score (T₁ x) q.atHeat q.delivery.paid q.delivery.isSound (@Finset.univ Unit _) (fun _=> U.atHeat) (fun _=>ζ) Z' (fun _=> U.delivery.isSound) (fun _=> U.delivery.paid) (fun t p=>by simpa using hz t p)
 simp only [Fintype.sum_unique] at hX
 refine (P.stageReady x _ s (show Tendsto (fun i=>(Qν i).s) atTop atTop from b) (w Z) q Xν T₁' f).trans (hX.trans ?_) -- pencil card q naming. `P.stageReady` order q w U h tested.
 exact (map_smul (P.temporalField x 3 (QA) U) (purePrice Z:ℂ) Z').symm
-- on kiss too: if paying as local adjoint, take `bar ∘ physical test meta`.
lemma signature_adj (T₁':(W₁).WPermit x j₁) (f:Test4): P.temporalField x 3 _ (T₁'.reflector x 3 (W₁)) f= P.temporalField x 3 _ (U.reflector x 3 QA) (bar (stageTest w Z (bar f))):=by
 ext1 yy; apply Subtype.ext; apply (bands (T₁ x)).grade_dense.eq_of_inner_right ℂ -- maybe `Dense.eq_of_inner_left ℂ` & implicit vectors
 intro xZ z
 let g:=bar f; let z':= stageTest w Z g; let X':= (𝒯 _ T₁') g
 let a₁:= (𝒯 _ (T₁'.reflector x 3 (W₁))) f; let b₁:= (𝒯 _ (U.reflector x 3 QA)) (bar z'); let x₀: radial (T₁ x) := ⟨xZ,z⟩
 change inner ℂ x₀.1 (a₁ yy).1=inner ℂ x₀.1 (b₁ yy).1
 have hx:= P.temporal_inner x 3 (W₁) T₁' x₀ yy g; rw [show bar g=f from Probe.bar_twice f] at hx
 have hv:=P.signatureAct x A s U h y c r n w Z X T' V b T₁' g
 rw [hv] at hx; exact hx.symm.trans (P.temporal_inner x 3 QA U x₀ yy z')
omit h X T' V b
lemma sig_support (f:Test4): tsupport (stageTest w Z f)⊆ tsupport f:= subset_trans (test_pay ..) (drum_time (w Z) f)
lemma sig_bar_support (f:Test4): tsupport (bar (stageTest w Z (bar f))) ⊆ tsupport f:=by rw [bar_reach,← bar_reach f]; exact sig_support w Z (bar f)
end filings
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open YM.CF.Buffered.Afterglow.Tower.VacuumSelection
#print axioms Spine.issuerJet
#print axioms Spine.stageReady
#print axioms Spine.signatureAct
#print axioms Spine.drum_time
#print axioms Spine.sig_bar_support
#print axioms Spine.signature_adj
