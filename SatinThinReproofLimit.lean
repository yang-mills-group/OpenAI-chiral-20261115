import SatinFixedContrastNovember4
import SatinThinReproofClock
/-!
# CP16. Test on the genuine limit itself (not merely on approximants)

If wanting to continue after pricing ANY symmetric positive heat padding
(and thus using remaining Euclidean *gap* in the CenterPays sense) here are the
costs. On a positive-rank signed pair at ONE spatial displacement, **no
such local continuation**. Uses pointPrice not an assumption about all
positions in overlap. And any attempt to continue on JUST our center argument
of pointPrism (λ=0 no such padding), but invoke a positive-energy system still
retaining time extension allowance as specified (`HasPadding` on its B proper,
not the adjoint prices!), is impossible. No conclusion when ALL positive heat
padding/further-extension assumptions dropped at the limit. Not general Wightman
distributions; read types, proof docs and `YM.SU5.Macro`.
-/
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 3000
set_option maxHeartbeats 330000
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
open MacroGrid SatinNucleus SatinJets DoseTravel Set
open YM.SatinMacro YM.SatinEdge
variable (P:Spine)(x:P.Spectrum0 3)
local notation "ξ"=> P.advocate 3 x 3
local notation "H"=> P.ColorHil 3 ξ
local notation "G"=> P.ManyF 3 ξ
local notation "Ω"=> P.heaven 3 ξ
local notation "ω"=> P.colorZero 3 ξ
local notation "S"=> P.seasons 3 ξ
local notation "π'"=> P.wealth 3 ξ
local notation "E!"=> (S).E
local notation "U!"=> (S).U
local notation "κ"=> (S).unit
local notation "ℒ"=> Lead.Clan
variable (V:∀ j:Axis,List Axis→ℝ→ P.ColorHil j (P.advocate 3 x j))(w:Lead.Clan→ Prism)
variable (z:Lead.Clan)(p:Vantage)
local notation "v!" => sameRest p
local notation "V!" => P.profilesZ x V w z
def limitStripe (t:ℝ):ℂ:= P.pointPrism x V w (rollCall p t) z z
local notation "K!"=> P.limitStripe x V w z p
lemma stripe_exact (t:ℝ): K! t= inner ℂ (V! (t/2)) (U! v! (V! (t/2))):=by
 change inner ℂ (V! ((rollCall p t 3)/2)) (P.cartage 3 ξ _ (V! ((rollCall p t 3)/2)))=_; rw [roll_price_time,P.roll_uses x p t]
-- continuation in future time: any r
lemma stripe_shift (h:SatinJets.Positive (S) (V!)) (r:ℝ≥0)(e:0<r) (t:ℝ)(f:0 ≤ t): K! (t+ ↑r + ↑r)= SatinMacro.kernel (S) (V! ↑r) (V! ↑r) v! t.toNNReal:=by
 let a:ℝ:= t+↑r + ↑r; have w':0< a/2:=by unfold a; linarith only [f,show (0:ℝ)< ↑r from e]
 have hr: V! ((r:ℝ) + t) = E! t.toNNReal (V! ↑r):=by
   rw [h (r:ℝ) ((r:ℝ)+t) e (by linarith), add_sub_cancel_left]
 rw [P.stripe_exact,SatinJets.spectrum_meet (S) _ (fun a=> (S).independent a v!) V! V! h h w' w' (show (0:ℝ)< ↑r from e) (show (0:ℝ)< ↑r+t from add_pos_of_pos_of_nonneg (show 0<(r:ℝ) from e) f) (by unfold a; ring),hr]; rfl
lemma stripe_pays (h:SatinJets.Positive (S) (V!)) (r:ℝ≥0)(e:0<r) : CenterPays v! K! (S) (V! ↑r) (V! ↑r) r:= (eventually_ge_atTop _).mono fun a v=> P.stripe_shift x V w z p h r e a v
-- additionally POSITIVE padding at r. use earlier heat *despite* width removed. Never assert uniform in r.
private lemma stripe_l (Z:Hilbert)(T:OS.Semigroup Z (3:Axis))(U:ℝ→Z)(h:SatinJets.Positive T U)(r:ℝ≥0)(e:0<r): HasPadding T (U ↑r):= by
 let a:ℝ:= (r:ℝ)/2; have f:0<a:= half_pos (show (0:ℝ)< ↑r from e); have t:a< ↑r:=half_lt_self (show (0:ℝ)< ↑r from e)
 exact ⟨(↑r-a).toNNReal,Real.toNNReal_pos.mpr (sub_pos.mpr t),U a,h a ↑r f t.le⟩
lemma stripe_padded (h:SatinJets.Positive (S) (V!)) (r:ℝ≥0)(e:0<r) : HasPadding (S) (V! ↑r):= stripe_l G (S) V! h r e
-- cost at SOME point; any positive T at same p. f beyond horizon still at same position of original test (may offset time only).
lemma stripe_witness (h:SatinJets.Positive (S) (V!)) {t:ℝ} (q:t ∈ Set.Ioi 0)(g:K! t≠0) : ∃ᶠ t:ℝ in atTop, K! t ≠0:=by
 apply traveler K! 0; constructor; swap; · exact ⟨t,q,g⟩
 rw [show K! = (fun t:ℝ=>inner ℂ (V! (t/2)) (U! v! (V! (t/2)))) from funext (P.stripe_exact x V w z p)]; exact SatinJets.analytic_meet (S) _ (fun a=>(S).independent a v!) V! V! h h
lemma stripe_falls (h:SatinJets.Positive (S) (V!)) (f':∀ t:ℝ, 0<t → (S).orth (V! t)=0) : Tendsto K! atTop (𝓝 0):= by
 let K(t:ℝ):=SatinMacro.kernel (S) (V! 1) (V! 1) v! t.toNNReal
 have e: Tendsto (K ∘ fun a:ℝ=> a+(-2)) atTop (𝓝 0):= (falls v! (S) _ _ (f' _ (by norm_num))).comp (tendsto_atTop_add_const_right atTop (-2:ℝ) tendsto_id)
 refine e.congr' ?_; filter_upwards [eventually_ge_atTop (2:ℝ)] with t ht
 let p:= (1:ℝ≥0); change K (t+-2)=_; unfold K
 exact ((P.stripe_shift x V w z _ h p (by simp [p]) _ (show 0 ≤ t+ -2 by linarith)).symm.trans (by unfold p; simp; congr 1; ring)) -- tune local p shadow notation
structure PriceLimitRefuses : Prop where
 paid (r:ℝ≥0)(u:0<r) : CenterPays v! K! (S) (V! ↑r) (V! ↑r) r
 bright (r:ℝ)(u:0<r) : HasPadding (S) (V! r) ∧ (S).orth (V! r)=0
 lower (r:ℝ≥0)(u:0<r) : ThinRefusal v! K! r
 deep : ∃ᶠ t:ℝ in atTop, K! t ≠0
 late : Tendsto K! atTop (𝓝 0)
 smooth_center_failure (H':Hilbert)(S':OS.Semigroup H' timeAxis) (A A' B B':H') : HasPadding S' B → CenterPays v! K! S' A B 0 →
    ∀ a b:ℝ,a<b→∃ t∈ Ioo a b, ¬ swap S'.unit (joinST v! t) A A' B B'
lemma limit_refuses (h:SatinJets.Positive (S) (V!)) (f':∀ t:ℝ, 0<t → (S).orth (V! t)=0) {t:ℝ} (q:t ∈ Set.Ioi 0)(g:K! t≠0) : P.PriceLimitRefuses x V w z p:=by
 have s:= P.stripe_witness x V w z p h q g
 have f:= P.stripe_falls x V w z p h f'; refine ⟨P.stripe_pays x V w z p h,fun i u=> ⟨P.stripe_padded x V w z h ⟨i,u.le⟩ u, f' i u⟩, ?_, s, f,?_⟩
 · intro i u; exact padded_price_refuses _ _ (S) _ _ i (P.stripe_pays x V w z p h i u) s (f' (i:ℝ) u) (P.stripe_padded x V w z h i u)
 intro H' S' A A' B B' e p' a b u; exact kill v! K! S' A B 0 p' s (f.congr (fun a=>by simp only [NNReal.coe_zero,add_zero])) e u A' B'
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
#print axioms YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine.limit_refuses
