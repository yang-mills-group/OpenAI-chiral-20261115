import YM.SU5.Registration.Heave.Sovereign
import YM.SU5.Registration.Heave.BigDrum
set_option autoImplicit false
set_option maxHeartbeats 380000
noncomputable section
set_option synthInstance.maxSize 28000
set_option maxRecDepth 2000

set_option quotPrecheck false
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection

open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase
     MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound
     Common Ballad Cordial
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker
     ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy
     Tapestry Germ Alliance Lamour.Bridge.Celeste Designs Twah Prototype
open YM.Stationary (Gaia)
open CF.Onyx (riseX moor)
open Lamour.Bridge.Celeste.Morn

open CF.Velvet CF.Pannier.Chancel
open Spine Pitching.Focus
open QuadClock
open Aria Casting MacroGrid Preparation.Yoke Yoke.Travel
namespace Spine
open Aria Casting Six OS.Semigroup OS.Semigroup.Balloon
open MacroGrid SatinNucleus SatinJets Drums
open _root_.YM.SatinRegistration
/-!
# Sharper diagnosis of same-vacuum comparator

It is intentional that in obtaining op estimates we get an EXACT GAUGE SUBSTITUTE
up to the same G/Fields test (not asserting every same election must have this).
Conclude within this diagnosis how `SatinEdgeBareProbe` assessment strengthens.
It is a genuine diagnostic on this interpretation (build no counterfeit snapshots),
not a disproof of possible protocols or other choices of local field including boosts.
And the collapse here is in thermal *operator limits* on G: does not identify arbitrary
microscopic Ward measurements.
-/
variable (P:Spine)(x:P.Spectrum0 3)(c r n:ℕ→ℕ)(A:ℕ→P.Apron)(Z:Lead.Clan)
local notation "θ"=> (3:Axis)
local notation "ξ"=> P.advocate 3 x 3
local notation "E"=> (P.seasons 3 ξ)
local notation "ζ"=> (purePrice Z:ℂ)
local notation "H₁"=> P.ManyF 3 ξ
section cost
variable (s u:ℕ)(D:P.Apron)(v:D.s≤ s) (z:P.Spectrum0 3)
local notation "B"=> P.gaugeStitch Z D s u
local notation "t"=> (B).allowance P θ
local notation "q"=> D.allowance P θ
local notation "S"=> timeMesh P.par
local notation "U"=>(B).u θ
include v in
lemma gate_price (a:ℝ≥0)(h:t ≤ a): P.stageH θ z (P.gaugeStitch Z D s u) a a= ζ • P.stageH θ z D (a+q) (a-q):=by
 have he: D.zoom P s θ+D.zoom P s θ ≤ (B).u θ:=by
    change D.zoom P s θ+D.zoom P s θ≤ (P.stitchApron Z D s u).u θ; rw [P.stitch_quote]; omega
 let p:= add_pos ((B).pos θ) ((B).pos θ); let V:=P.shifted_deposit θ z s U p D (D.zoom P s θ) v he;
 rw [← P.zoomMoney θ D s v]; exact P.deposit_at_finger θ z (B) (V.scale P θ z s U p ζ) a h
end cost
abbrev MildAt (i:ℕ):= P.gaugeStitch Z (A i) (c (n i)) (r (n i))
local notation "B" i:max=> P.MildAt c r n A Z i
local notation "q" i:max => (A i).allowance P θ
variable (V:P.ThinHere (P.ClaimedAt c r n A Z))(F:P.CapReady x A)(X:P.HandleWith x c r A n)
include V F X
lemma mild_dense (l:ℝ≥0)(h:0<l):∀ᶠ i:ℕ in atTop, (B i).allowance P θ ≤ l ∧ P.stageH θ ξ (B i) l l= ζ • P.stageH θ ξ (A i) (l+q i) (l-q i):=by
 have he:Tendsto (fun i=>(B i).realWidth P θ) atTop (𝓝 0):= V θ; simp_rw [Apron.width_real] at he; filter_upwards [(NNReal.tendsto_coe.mp he).eventually (ge_mem_nhds h)] with i v; exact ⟨v,P.gate_price Z _ _ _ (X.already _) ξ l v⟩
lemma mild_flight (l:ℝ≥0)(h:0<l): Flying (H:=H₁) (fun i=>P.stageG θ ξ (B i) l l) (ζ • P.managed x A F l):=by
 have he:Tendsto (fun i=>q i) atTop (𝓝 0):= P.all_width_paid x A 3 F
 let b:= P.uniform_pit x A l _ _ (g1:= (show Tendsto (fun i=>l+q i) atTop (𝓝 l) from by simpa using he.const_add l)) (g2:= (show Tendsto (fun i=>l-q i) atTop (𝓝 l) from by simpa using (Tendsto.sub (tendsto_const_nhds (x:=l)) he))) h F
 refine (Flying.scaled (tendsto_const_nhds (x:=ζ)) b).late ?_; filter_upwards [P.mild_dense x c r n A Z V F X l h] with i p; change _ = P.stageG _ _ (B i) l l; rw [stageG, stageG,p.2,map_smul]
omit F
lemma mild_bought (h:P.Bought3 x A): P.Bought3 x (P.MildAt c r n A Z):=by
 let W:= h.card; have he:Tendsto (fun i=>q i) atTop (𝓝 0):= P.all_width_paid x A 3 W
 let Y(l:ℝ≥0)(i:ℕ):= P.stageH θ ξ (A i) (l+q i) (l-q i)
 have hx:RisePrice Y:= h.moving P x A _ _ (fun t _=> by simpa using he.const_add t) (fun t _=> by simpa using (Tendsto.sub (tendsto_const_nhds (x:=t)) he))
 obtain ⟨k,C,v,h'⟩:= RisePrice.smul hx ζ; refine P.toBought x _ ⟨k,C,v,fun s g e=>?_⟩ (fun t g=> (P.mild_flight x c r n A Z V W X t g).Cauchy) ?_
 · filter_upwards [P.mild_dense x c r n A Z V W X s g,h' s g e] with i k e; rw [k.2]; exact e
 exact fun j=> V j
include F
lemma mild_limit (W:CapReady P x (P.MildAt c r n A Z)) {l:ℝ≥0}(u:0<l) : P.managed x _ W l= ζ • P.managed x A F l:= (P.received_moves x _ _ W u).unique (P.mild_flight x c r n A Z V F X l u)
omit F V X
lemma paid_zero {A:ℕ→P.Apron}(p:P.CapReady x A): P.managed x _ p 0=0:=by rw [managed,Delivery.accepts,dif_neg (lt_irrefl _)]
include V X
variable (J:Tendsto (fun i=> c (n i)) atTop atTop)(w:Lead.Clan→ Prism)(T:P.Guest x c r A n)(h:P.Bought3 x A)
local notation "R"=> P.gaugeTrumpet A c r n w Z
local notation "W"=> P.soldTrumpet A c r n w Z
include J h
lemma mild_trumpet : Bought3 P x (P.gaugeTrumpet A c r n w Z):= P.trumpet_bought x (w Z) _ (show Tendsto (fun i=>(B i).s) atTop atTop from J) (P.mild_bought x c r n A Z V X h)
include T
lemma fiery_trumpet : Bought3 P x (P.soldTrumpet A c r n w Z):= by
 let C' := P.ClaimedAt c r n A Z; exact P.trumpet_bought x (w Z) _ (show Tendsto (fun i=>(C' i).s) atTop atTop from J) (P.seam_powered x c r n A Z V T X h)
omit T
lemma gauge_trumpet_timing (h':CapReady P x R) (t:ℝ≥0)(g:0<t):
    P.managed x (R) h' t=P.drumPrice x (w Z) (fun l=> ζ • P.managed x A h.card l) t :=by
 let H:= P.mild_bought x c r n A Z V X h
 have he:P.managed x _ H.card= fun l=> ζ • P.managed x A h.card l:=funext (fun l=>by
    rcases eq_zero_or_pos l with a|a
    · subst l; rw [P.paid_zero,P.paid_zero,smul_zero]
    exact P.mild_limit x c r n A Z V h.card X H.card a)
 exact (P.drum_paid x (w Z) t _ J H h' g).trans (by rw [he])
include T
lemma sold_trumpet_timing (h':CapReady P x W) (t:ℝ≥0)(g:0<t):
    P.managed x (W) h' t=P.drumPrice x (w Z) (fun l=> ζ • P.managed x A h.card l) t :=by
 let H':= P.seam_powered x c r n A Z V T X h
 have he:P.managed x _ H'.card= fun l=> ζ • P.managed x A h.card l:=funext (fun l=>by
    rcases eq_zero_or_pos l with a|a
    · subst l; rw [P.paid_zero,P.paid_zero,smul_zero]
    exact P.seam_identifies x c r n A Z V T X h.card H'.card a)
 exact (P.drum_paid x (w Z) t _ J H' h' g).trans (by rw [he])
lemma same_trumpets (a:P.CapReady x (P.gaugeTrumpet A c r n w Z))(b:P.CapReady x (P.soldTrumpet A c r n w Z)) : P.managed x (R) a=P.managed x (W) b:=funext fun l=>by
 rcases eq_zero_or_pos l with v|v
 · subst l; rw [P.paid_zero,P.paid_zero]
 exact (P.gauge_trumpet_timing x c r n A Z V X J w h a l v).trans (P.sold_trumpet_timing x c r n A Z V X J w T h b l v).symm
lemma same_fields (a:P.CapReady x (P.gaugeTrumpet A c r n w Z))(b:P.CapReady x (P.soldTrumpet A c r n w Z)) : P.pointField x (R) a=P.pointField x (W) b ∧ P.pointField x (fun i=> ((R) i).kiss P θ) (P.cap_partner x (R) a)=P.pointField x (fun i=> ((W) i).kiss P θ) (P.cap_partner x (W) b):=by
 have u:= P.same_trumpets x c r n A Z V X J w T h a b
 rw [P.field_partner,P.field_partner]; exact useB _ _ u _ _ _ _
where useB (f g:ℝ≥0→(P.ManyF 3 (P.advocate 3 x 3)).Op)(u:f=g)(v:SatinRegistration.Sound E f)(z:PadPaid f)(q':SatinRegistration.Sound E g)(z':PadPaid g):field E f v z=field E g q' z' ∧ SatinRegistration.adj E f v z=SatinRegistration.adj E g q' z' := by subst g; exact ⟨rfl,rfl⟩
omit T h J V X
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open YM.CF.Buffered.Afterglow.Tower.VacuumSelection
#print axioms Spine.same_trumpets
#print axioms Spine.same_fields
#print axioms Spine.gate_price
#print axioms Spine.mild_trumpet
#print axioms Spine.fiery_trumpet
