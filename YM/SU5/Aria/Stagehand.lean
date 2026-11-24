import YM.SU5.Aria.Trellis
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 4500
set_option maxHeartbeats 220000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
open Germ Alliance
namespace Spine
variable (P: Spine) (j:Axis) (x:P.Spectrum0 j)
open Aria Set TopologicalSpace Metric
local notation "ω"=> P.colorZero j x
local notation "M"=> timeMesh P.par
local notation "Γ"=> marks M
local notation "Γ'"=> P.VMark
local notation "X"=> P.ColorHil j x
local notation "Y"=> P.ManyF j x
local notation "π"=> P.enter j x
local notation "ρ"=> P.wealth j x
local notation "U"=> P.truck j x
local notation "W"=> P.cartage j x
local notation "κ"=> P.laysM
-- Projections reused to everywhere; cartage facts
lemma uses_cart (r:Vantage): P.cartage j x r=(P.seasons j x).U (transverse j (fun i:Trans j=>r i.val)):= (P.sails_smooth ..).symm
lemma cart_empty (a:Vantage) : W a (P.heaven j x)=P.heaven j x:=by
 have h(g:Γ'): W (κ g) (P.heaven j x)=P.heaven j x:= (π).injective (by rw [← P.cart_and]; exact P.truck_empty ..)
 exact congrFun ((P.marksDense).equalizer (P.cart_cont j x (P.heaven j x)) continuous_const (funext h)) a
lemma cart_pay (z:Vantage): ‖W z‖≤1:=ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun _=>by rw [P.cart_norm,one_mul])
def tableau (p:Vantage) (A:(X).Op): (Y).Op:= (W p).comp ((ρ).comp (A.comp ((π).toContinuousLinearMap.comp (W (-p))))) -- notation (X).Op expands?
def charter (p:Γ') (A:(X).Op):(X).Op := (U p).comp (A.comp (U (-p)))
lemma charter_pay (A:(X).Op)(p:Γ') : ‖P.charter j x p A‖≤ ‖A‖:= ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) (fun u=> by simp only [charter,ContinuousLinearMap.comp_apply,P.truck_norm]; rw [←P.truck_norm j x (-p) u]; exact ContinuousLinearMap.le_opNorm ..) -- rewrite specific
lemma enter_wealth : ‖(ρ)‖ ≤ 1 := ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun b=> by rw [one_mul]; change ‖P.visitors j x b‖≤_; rw [P.visitors_op]; apply Submodule.norm_starProjection_apply_le)
lemma tableau_pay (A:(X).Op)(p:Vantage): ‖P.tableau j x p A‖≤‖A‖:=ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) (fun b=> by
 change ‖W p (ρ (A (π (W (-p) b))))‖ ≤ _ ; rw [P.cart_norm]; exact ((ContinuousLinearMap.le_of_opNorm_le (ρ) (P.enter_wealth j x) _)|>.trans (one_mul _|>.le) |>.trans ((A.le_opNorm _).trans_eq (by rw [(π).norm_map,P.cart_norm]))))
set_option maxHeartbeats 250000
variable (A: (P.ColorHil j x).Op)
lemma vclose_ball (r x:Vantage)(e:ℝ)(p:0<e): VClose (r-x) e ↔ dist r x<e:=by rw [dist_eq_norm,pi_norm_lt_iff p]; rfl
lemma gentle_room {r:Vantage}{D:ℕ→ Mist P.VMark}(p:P.gentle r D){S:Set Vantage}(t:S∈𝓝 r): ∀ᶠ n:ℕ in atTop,(D n).holds (fun z=>P.laysM z∈ S):=by
 obtain ⟨ε,q,h⟩:=Metric.mem_nhds_iff.mp t; exact (p ε q).mono fun n u=> (D n).promotes (fun i x=> h ((vclose_ball _ _ ε q).1 x)) u
lemma frugal_moves {g:ℕ→Mist P.VMark} (p:P.gentle 0 g) (q:ℕ→ P.VMark)(r:Vantage)(d:Tendsto (P.laysM ∘ q) atTop (𝓝 r)) :
    P.gentle r (fun i=> (g i).onFn (fun b=>q i+b)):=by
 intro ε e; filter_upwards [p (ε/2) (by positivity),Metric.tendsto_nhds.mp d (ε/2) (by positivity)] with i h u
 refine (Mist.hold_via ..).2 ((g i).promotes ?_ h); intro b p
 change VClose (κ (q i+b)-r) ε; intro j; have hr:= (vclose_ball _ _ (ε/2) (by positivity)).2 u j; simp only [Pi.sub_apply,Function.comp_apply] at hr
 specialize p j; simp only [sub_zero] at p; change |κ b j| < _ at p
 rw [P.lays_add,Pi.sub_apply,Pi.add_apply,add_sub_right_comm]; apply (abs_add_le ..).trans_lt; linarith
-- Vantage continuity product plus adjustable offset
lemma itinerary {g:ℕ→ Mist P.VMark}(p:P.gentle 0 g)
    (t:∀ x₁: X, Tendsto (fun i=>(g i).mean (fun z=> U z x₁)) atTop (𝓝 (π (ρ x₁))))
    (q:ℕ→P.VMark) (r:Vantage)(d:Tendsto (P.laysM ∘ q) atTop (𝓝 r))(b:X):
   Tendsto (fun i=>(g i).mean (fun z=> U (q i+z) b)) atTop (𝓝 (π (W r (ρ b)))):=by
 have he:Tendsto (fun i=>U (q i) (π (ρ b))) atTop (𝓝 (π (W r (ρ b)))):=by
   simp_rw [P.cart_and]; exact (((π).continuous.comp (P.cart_cont j x (ρ b))).tendsto r).comp d
 have h:= firmly (fun i=> U (q i)) zero_le_one (Eventually.of_forall fun n=> P.truck_pay j x _) he (t b)
 simp_rw [P.truck_paves,ContinuousLinearMap.comp_apply, Mist.mean_linear' _ (fun z=> U z b) (U _)]; exact h -- tune
lemma tableau_q {g:ℕ→ Mist P.VMark}(p:P.gentle 0 g)(q:ℕ→ P.VMark)(r:Vantage)(d:Tendsto (P.laysM ∘ q) atTop (𝓝 r))(b:Y): ∀ ε:ℝ,0< ε→ ∀ᶠ n:ℕ in atTop, (g n).holds fun z=> dist (U (-(q n+z)) (π b)) (π (W (-r) b))≤ε:=by
 intro ε e; let f(p:Vantage):=π (W (-p) b); have hv:ContinuousAt f r:= ((π).continuous.comp ((P.cart_cont j x b).comp continuous_neg)).continuousAt
 have hf:= P.gentle_room (P.frugal_moves p q r d) (Metric.tendsto_nhds.mp hv ε e)
 filter_upwards [hf] with i t; exact (g i).promotes (p:=fun z=> dist (f (P.laysM (q i+z))) (f r)<ε) (fun j x'=> (by rw [P.cart_and,P.lays_neg]; exact x'.le)) ((Mist.hold_via ..).1 t) -- t membership problem
section utility
variable {B E: Type*} [NormedAddCommGroup E][NormedSpace ℂ E]
lemma attains_mean {Bb:ℕ→Mist B}{f g:ℕ→B→ E}{z:E} (v:Tendsto (fun i=> (Bb i).mean (g i)) atTop (𝓝 z))(h:∀ ε>0, ∀ᶠ n in atTop,(Bb n).holds (fun b=> dist (f n b) (g n b)≤ ε)): Tendsto (fun i=> (Bb i).mean (f i)) atTop (𝓝 z):=by
 apply Metric.tendsto_nhds.mpr; intro ε e; filter_upwards [Metric.tendsto_nhds.mp v (ε/2) (by positivity),h (ε/2) (by positivity)] with n p q; exact lt_of_le_of_lt (dist_triangle _ ((Bb n).mean (g n)) _) ((add_lt_add_of_le_of_lt ((Bb n).mean_budget_dist _ _ _ q) p).trans_le (add_halves ε).le)
end utility
lemma tableau_arrives {g:ℕ→ Mist P.VMark}(p:P.gentle 0 g)(t:∀ b:X, Tendsto (fun i=>(g i).mean (fun z=> U z b)) atTop (𝓝 (π (ρ b))))
    (q:ℕ→ P.VMark)(r:Vantage)(d:Tendsto (P.laysM ∘ q) atTop (𝓝 r))(b:Y):
   Tendsto (fun i=>(g i).mean (fun z=> (P.charter j x (q i+z) A) (π b))) atTop (𝓝 (π ((P.tableau j x r A) b))):=by
 apply attains_mean (P.itinerary j x p t q r d (A (π (W (-r) b))))
 intro ε e; let δ:= ε / (‖A‖+1); have h:0<δ:=by positivity
 filter_upwards [P.tableau_q j x p q r d b δ h] with i u; apply (g i).promotes _ u; intro z v
 let y:=U (q i+z); let y':=U (-(q i+z)) (π b); let z':=(π (W (-r) b))
 change dist (y (A y')) (y (A z')) ≤ _; change dist y' z'≤δ at v
 rw [dist_eq_norm,←map_sub]; rw [dist_eq_norm] at v; unfold y; rw [P.truck_norm,←map_sub]; exact (A.le_opNorm _).trans ((mul_le_mul_of_nonneg_left v (norm_nonneg _)).trans ((mul_le_mul_of_nonneg_right (le_add_of_nonneg_right zero_le_one) h.le).trans_eq (mul_div_cancel₀ _ (show (‖A‖+1)≠0 by positivity)))) -- args mul order
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
#print axioms YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine.tableau_arrives
