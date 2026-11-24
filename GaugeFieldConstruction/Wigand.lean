import GaugeFieldConstruction.Appanage
set_option autoImplicit false
set_option quotPrecheck false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 30000
set_option synthInstance.maxSize 24000
noncomputable section
namespace YM.CF.TableF
open Function Filter Metric Lattice Wilson Finset MeasureTheory RG Precision Tree
open Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
open FlightFlux Fluxim
open Fock Tulip Lat Spire Phase Cube
attribute [local instance] opCStarAlgebra
open AnalyticBridge VerifiedReset Taxi
local notation "GS"=> SU.group
variable {n:Side}{p: BudgetPoint}{Q: InkD n}{o:Skye.Seat n}{X:Scree.Hub n}{h c:ℝ}
namespace Lenten
open Bank Laurent Bloch Tap Hove Spire
open Haro Hove Moto Tap
abbrev BasePrice(b:Bool):ℝ:=(FlightJet b).choose
lemma BP_u(b:Bool):0≤ BasePrice b:=(FlightJet b).choose_spec.1
def pilotS (M:Male)(b:Bool): Ole Plane Pal:= ((FlightJet b).choose_spec.2 M).choose
lemma kiosk_P (M:Male)(b:Bool): AptK (binor M b) (pilotS M b):=((FlightJet b).choose_spec.2 M).choose_spec.1
lemma cost_pkt (M:Male)(b:Bool): CostOle (pilotS M b) ≤ BasePrice b:= ((FlightJet b).choose_spec.2 M).choose_spec.2
-- anchor under integer coarsening
abbrev AnchorN (o:Skye.Seat n) := (assembly n).parent (o-1)
abbrev Caller (o:Skye.Seat n)(x:Site n): ℂ:= Rush.wind (AnchorN o) (stem (AnchorN o) x)
abbrev Pax (o:Skye.Seat n): Support (More n):= halo 24 ({o}:Support (More n))
abbrev Zhub (o:Skye.Seat n): Scree.Hub n := ⟨(o,Pax o), halo_spec.mpr ⟨o,mem_singleton_self _, by simp⟩⟩
abbrev pointF (o:Skye.Seat n)(x:Site n): Plane →L[ℝ]ℝ:= (1/2:ℝ) • rom (stem o (node x))
abbrev κviews(o:Skye.Seat n)(x y:Site n): Views→L[ℝ]ℝ := -(pointF o x|>.comp (ContinuousLinearMap.fst ℝ Plane Plane)) + (pointF o y|>.comp (ContinuousLinearMap.snd ℝ Plane Plane))
variable (o)
lemma call_bit (x:Site n): ‖Caller o x‖=1:=by unfold Caller; first|exact Rush.fee_norm (v:=Lattice.lift _) _ | exact Rush.fee_norm ..|exact fee_norm ..
def tautF {V:Type}[NormedAddCommGroup V][NormedSpace ℝ V]{E:Type}[NormedAddCommGroup E][NormedSpace ℝ E] (T:V→L[ℝ] E):ℝ:= ‖T‖
lemma point_est (x:Site n): ‖pointF o x‖ ≤2*(separation o (node x):ℝ):=by
 rw [pointF,norm_smul,Real.norm_of_nonneg (by norm_num : 0≤(1/2:ℝ))]; have H:= show (lateral (stem o (node x)):ℝ) ≤ 4*(separation o (node x):ℝ) from (by rw [separation_comm o (node x)]; exact_mod_cast stem_t ..); linarith only [H,radius_Z (stem o (node x))]
lemma peak_shifts(x y:Site n)(a:ℝ)(p:(separation o (node x):ℝ)≤a)(t:(separation o (node y):ℝ)≤a): ‖κviews o x y‖≤4*a:=by
 have h(k:Site n)(E:Views→L[ℝ]Plane)(v:‖E‖≤1): ‖(pointF o k).comp E‖ ≤ _:= (ContinuousLinearMap.opNorm_comp_le _ _).trans ((mul_le_of_le_one_right (norm_nonneg _) v).trans (point_est o k)); unfold κviews; apply (norm_add_le ..).trans; rw [norm_neg]; linarith only [p,t,h x (ContinuousLinearMap.fst ℝ Plane Plane) (ContinuousLinearMap.norm_fst_le ..),h y (ContinuousLinearMap.snd ℝ Plane Plane) (ContinuousLinearMap.norm_snd_le ..)] -- tune arguments unknown
-- fine input matrix pencil. Scale h^2 included in load.
def hill_Z (u: Op (Single n))(h:ℝ)(x y: Single n):ℂ:= (h^2:ℂ)* Caller o x.1.1*Caller o y.1.1*u x y
abbrev yardZ:= Single n ×Single n -- needs n binder
abbrev streamF (u: Op (Single n))(h:ℝ)(x: Views): Pal:=∑ i:yardZ (n:=n), flare_one (portB i.1) (portB i.2) (PayS (κviews o i.1.1.1 i.2.1.1) x * hill_Z o u h i.1 i.2)
abbrev mastF (u:Op (Single n))(h:ℝ)(i: Single n ×Single n): Ole Views Pal:= postF (bookP (κviews o i.1.1.1 i.2.1.1) (hill_Z o u h i.1 i.2)) (flare_one (portB i.1) (portB i.2))
-- hide Norm ambiguity by summing tagged before any use
abbrev oleSum {E F:Type}[NormedAddCommGroup E][NormedSpace ℝ E][NormedAddCommGroup F][NormedSpace ℝ F]{I:Type}(X:Finset I) (f:I→Ole E F):Ole E F :=∑ i∈X, f i
def markJet(u:Op (Single n))(h:ℝ):Ole Views Pal:=oleSum univ (mastF o u h)
lemma K_pays(u:Op (Single n))(h:ℝ): AptK (streamF o u h) (markJet o u h):=by
 let F(x: Single n×Single n)(y:Views):= flare_one (portB x.1) (portB x.2) (PayS (κviews o x.1.1.1 x.2.1.1) y * hill_Z o u h x.1 x.2); have hp:streamF o u h= ∑ i: Single n× Single n, F i :=funext fun i=>by unfold streamF; rw [Finset.sum_apply]
 rw [hp]; exact AptK.sumV _ _ _ (fun i _=> (factor_sale (κviews o _ _) (hill_Z o u h i.1 i.2)).geomF (flare_one (portB i.1) (portB i.2)))
def caboose :ℝ:=1+∑ i:Hove.Kt,∑ j:Hove.Kt,tautF (flare_one i j)
omit o
lemma taut_nonneg{E F:Type}[NormedAddCommGroup E][NormedSpace ℝ E][NormedAddCommGroup F][NormedSpace ℝ F](V:E→L[ℝ] F):0≤tautF V:= norm_nonneg _
lemma flare_bound (i j:Hove.Kt): tautF (flare_one i j) ≤ caboose:= by
 unfold caboose; apply le_trans _ (le_add_of_nonneg_left zero_le_one); apply (single_le_sum (f:=fun k=>tautF (flare_one i k)) (fun i _=>taut_nonneg _) (mem_univ j)).trans (single_le_sum (f:=fun i=>∑ j:Hove.Kt,tautF (flare_one i j)) _ (mem_univ i)); exact fun i _=> sum_nonneg (fun _ _=> taut_nonneg _)
lemma cab_pos :0<caboose:=by unfold caboose; refine add_pos_of_pos_of_nonneg one_pos (sum_nonneg fun _ _=>sum_nonneg fun _ _=>taut_nonneg _)
lemma post_cost {E F G:Type}[NormedAddCommGroup E][NormedSpace ℝ E][NormedAddCommGroup F][NormedSpace ℝ F][NormedAddCommGroup G][NormedSpace ℝ G](x:Ole E F) (v:F→L[ℝ] G): CostOle (postF x v)≤tautF v * CostOle x:= post_pay ..
lemma fund_non (x:Views→L[ℝ]ℝ)(a:ℂ) : 0 ≤ CostOle (bookP x a) := norm_nonneg (bookP x a)
include o
lemma ΞFare(u:Op (Single n))(h:ℝ)(i:Single n ×Single n): ‖hill_Z o u h i.1 i.2‖= h^2*‖u i.1 i.2‖:=by
 unfold hill_Z; simp only [norm_mul,norm_pow, call_bit, Complex.norm_real, mul_one]; rw [Real.norm_eq_abs,sq_abs]
set_option maxHeartbeats 45000 in
lemma mast_ticks (u:Op (Single n))(h:ℝ)(i:Single n ×Single n) : let l:=endL o (Haro.tray i.1 i.2);
    CostOle (mastF o u h i) ≤ caboose*((4*(1+(l:ℝ)))^2*(h^2*‖u i.1 i.2‖)):=by
 intro l; let a:=κviews o i.1.1.1 i.2.1.1; let b:=hill_Z o u h i.1 i.2; let L:ℝ:=4*(1+(l:ℝ)); let F:=flare_one (portB i.1) (portB i.2)
 have he:‖b‖= h^2*‖u i.1 i.2‖:= ΞFare o u h i
 have hp:1≤L:=by unfold L; linarith only [show 0≤ (l:ℝ) from by positivity]
 have hv(j:Scree.Dwell n)(v:j∈Haro.tray i.1 i.2): (separation o (node j.2.1.1):ℝ)≤ l:=by exact Nat.cast_le.mpr (show separation o (node j.2.1.1) ≤ l from le_sup (f:=fun j:Scree.Dwell n=>separation o (node j.2.1.1)) v)
 have hz: ‖a‖≤ L:= (peak_shifts o _ _ _ (hv (true,i.1) (by simp [Haro.tray])) (hv (false,i.2) (by simp [Haro.tray]))).trans (by unfold L; linarith only)
 apply (post_cost (bookP a b) F).trans; -- infer TC Norm order maybe stuck
 change _ ≤ caboose* (L^2*_)
 exact mul_le_mul (flare_bound ..) ((show CostOle (bookP a b)≤ L^2*‖b‖ from fundK _ _ hz hp).trans_eq (by rw [he])) (fund_non a b) cab_pos.le
omit o in
set_option maxHeartbeats 90000 in
lemma weights_n {I E F:Type}[NormedAddCommGroup E][NormedSpace ℝ E][NormedAddCommGroup F][NormedSpace ℝ F] (X:Finset I)(R:I→Ole E F): CostOle (oleSum X R) ≤ ∑ i∈X,CostOle (R i):=norm_sum_le X R
omit o
local notation "γ"=> X.val.1
lemma upper_far (F:Op (Single n))(t:Finset (Dwell n)→ℝ)(v:∀ i,0≤ t i)(p':0≤h)
 (b:(∑ i:Finset (Dwell n),tariff p γ h i*t i)≤ c)(f:∀ i j,‖F i j‖ ≤ t (Haro.tray i j)) : CostOle (markJet γ F h) ≤ (caboose*16)*c:=by
 apply (weights_n _ _).trans -- lhs weights_n metavars; tune
 let z:= caboose*16; have hz:0 ≤ z:=by unfold z; have h:=cab_pos; positivity
 let W(i):= z*(tariff p γ h i*t i)
 apply le_trans _ (mul_le_mul_of_nonneg_left b (show 0≤caboose*16 from hz)); rw [Finset.mul_sum]; refine le_trans (b:=∑ i∈ (univ:Finset (Single n ×Single n)).image (fun i: Single n ×Single n=> Haro.tray i.1 i.2),W i) ?_ (sum_le_sum_of_subset_of_nonneg (subset_univ ..) ?_)
 · rw [sum_image tray_in.injOn]; refine sum_le_sum fun i _=> (mast_ticks γ F h i).trans ?_; let q:= Haro.tray i.1 i.2; let a:ℝ:= endL γ q; have he:(1+a)^2 ≤ (1+a)^p.power:=pow_le_pow_right₀ (le_add_of_nonneg_right (Nat.cast_nonneg _)) p.power_ge; unfold W z tariff; rw [show (Haro.tray i.1 i.2).card=2 by simp [Haro.tray]]; change _*((4*(1+a))^2*_ ) ≤ _*(((1+a)^p.power*(h^2))*_); apply le_trans (b:= (caboose*16)* (((1+a)^2 * h^2)* (t q)))
   · have hx:(4*(1+a))^2=(16:ℝ)*(1+a)^2:=by ring
     unfold q; rw [hx]; linarith only [mul_le_mul_of_nonneg_left (f i.1 i.2) (show 0≤ 16*caboose*(1+a)^2*h^2 from by have hp:=cab_pos; positivity)] -- q let expand
   gcongr
   exact v q
 · intro i _ _; unfold W; exact mul_nonneg hz (mul_nonneg (mul_nonneg (by positivity) (pow_nonneg p' _)) (v i))
lemma lofty (t: PressB p X Q h c)(v:0≤ h) : CostOle (markJet γ (orbitPH (Q 1)) h) ≤ (caboose*16)*c:=by obtain ⟨b,h,o,y⟩:= t.worth; exact upper_far _ _ h v y (ortho_l _ _ _ (o _))
end Lenten
end YM.CF.TableF
end
