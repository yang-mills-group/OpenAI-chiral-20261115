import YM.SU5.Registration.Heave.AirCarry
import YM.SU5.Registration.Heave.OnRail
import YM.SU5.Registration.Heave.Waft
set_option autoImplicit false
set_option maxHeartbeats 380000
noncomputable section
set_option synthInstance.maxSize 28000
set_option maxRecDepth 2000

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

open SatinNucleus Six
namespace Spine
open _root_.YM.SatinRegistration
variable (P:Spine)(x:P.Spectrum0 3)(c r n:ℕ→ℕ)(A:ℕ→ P.Apron)(k:Lead.Clan)
set_option quotPrecheck false
local notation "H₁"=> P.ColorHil 3 (P.advocate 3 x 3)
local notation "G"=> P.ManyF 3 (P.advocate 3 x 3)
local notation "ξ"=> P.advocate 3 x 3
local notation "q" i:max=> (A i).allowance P 3
local notation "qF" i:max=> (A i).realWidth P 3
local notation "F"=> P.physicalEnergy 3 ξ
local notation "ζ"=> (purePrice k:ℂ)
-- evolving path
abbrev ClaimedAt (i:ℕ):= P.stitchApron k (A i) (c (n i)) (r (n i))
local notation "B" i:max=> P.ClaimedAt c r n A k i
variable (V:P.ThinHere (P.ClaimedAt c r n A k))
variable (T:P.Guest x c r A n)(Y:P.HandleWith x c r A n)
include V T Y
lemma seamCost {l:ℝ≥0}(u:0<l):
    ∀ᶠ i:ℕ in atTop, ‖P.stageH 3 ξ (B i) l l-ζ • P.stageH 3 ξ (A i) (l+q i) (l-q i)‖ ≤ P.macroStep i :=by
 have he:=V 3; simp_rw [Apron.width_real] at he
 filter_upwards [(NNReal.tendsto_coe.mp (show Tendsto _ atTop (𝓝 (↑(0:ℝ≥0):ℝ)) from he)).eventually (ge_mem_nhds u)] with i h
 refine (P.unseam ξ (A i) k _ _ (Y.already i) (T.covers i k) _ h).trans (le_trans ?_ (T.expenses i k)) -- goal ?_ tactic
 exact mul_le_mul_of_nonneg_right (le_add_of_nonneg_left zero_le_one) (norm_nonneg _)
variable (F₀:P.CapReady x A)
include F₀
lemma seamInFlight {l:ℝ≥0}(u:0<l): Flying (H:=G) (fun i=> P.stageG 3 ξ (B i) l l) (ζ • P.managed x A F₀ l):=by
 let w(i):ℝ≥0:= q i; let f(i):= P.stageG 3 ξ (A i) (l+w i) (l-w i)
 have he:Tendsto w atTop (𝓝 0):= P.all_width_paid x A 3 F₀
 have g:Flying f (P.managed x A F₀ l):= P.uniform_pit x A l _ _ (by simpa using he.const_add l) (by simpa using (Tendsto.sub (tendsto_const_nhds (x:=l)) he)) u F₀
 apply Flying.by_wages _ (Flying.scaled (tendsto_const_nhds (x:=ζ)) g)
 refine squeeze_zero' (Eventually.of_forall fun i=>norm_nonneg _) ((P.seamCost x c r n A k V T Y u).mono fun i h=> (?_ : ‖ P.stageG 3 ξ (B i) l l-ζ • f i‖ ≤ P.macroStep i)) P.macroStep_zero
 refine le_trans ?_ h; unfold f w stageG; rw [←map_smul, ←map_sub]; exact P.toG_cost ..
-- stronger H estimate retained for jets on the physically certified unprojected operators. (We do not need STOT_CAP at H level.)
omit F₀
lemma seam_powered (Q:P.Bought3 x A) : Bought3 P x (P.ClaimedAt c r n A k):=by
 have he:= P.all_width_paid x A 3 Q.card; let U(t:ℝ≥0)(i:ℕ):=P.stageH 3 ξ (A i) (t+q i) (t-q i);
 have hf:RisePrice U:= Q.moving P x A _ _ (fun t _=> by simpa using he.const_add t) (fun t _=>by simpa using (Tendsto.sub (tendsto_const_nhds (x:=t)) he))
 obtain ⟨p,C,b,f⟩:= hf; refine toBought P x _ ⟨p,1+‖ζ‖*C,by positivity,?_⟩ (fun t v=> (P.seamInFlight x c r n A k V T Y Q.card v).Cauchy) V; intro t u e
 filter_upwards [P.seamCost x c r n A k V T Y u,f t u e,P.macroStep_zero.eventually (ge_mem_nhds (show 0<(1:ℝ) from zero_lt_one))] with i h p' f'
 have hp₁:‖P.stageH 3 ξ (B i) t t‖≤ 1+ ‖ζ • U t i‖:= (norm_le_norm_sub_add _ _).trans (add_le_add (h.trans f') le_rfl); let u':ℝ:= (t:ℝ)^p; have hh:0<u':= pow_pos u p; change u'*_≤_
 rw [norm_smul] at hp₁; have v₁: u'≤1:=pow_le_one₀ (by positivity) (show (t:ℝ)≤1 from e)
 apply (mul_le_mul_of_nonneg_left hp₁ hh.le).trans; rw [mul_add,mul_one, mul_left_comm]; exact add_le_add v₁ (mul_le_mul_of_nonneg_left p' (norm_nonneg _))
include F₀
-- useful coherence; not claiming anything about interaction witness via margin.
lemma seam_identifies (B':CapReady P x (P.ClaimedAt c r n A k)) {l:ℝ≥0}(u:0<l): P.managed x _ B' l= (ζ • P.managed x A F₀ l):=
 (P.received_moves x _ l B' u).unique (P.seamInFlight x c r n A k V T Y F₀ u)
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open YM.CF.Buffered.Afterglow.Tower.VacuumSelection
#print axioms Spine.seam_powered
#print axioms Spine.seam_identifies
