import YM.SU5.Registration.Rasp.Association
import Mathlib.Analysis.Complex.Schwarz
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
open Swatch Aria Casting SatinJets Drums OS.Semigroup
-- same calendar as M7. Operator costs in G project, no assumed Bought3 H at other γ
local notation "j₁"=> (3:Axis)
local notation "ξ₁" x:max=> P.advocate 3 x j₁
local notation "G₁" x:max=> P.ManyF j₁ (ξ₁ x)
local notation "T₁" x:max=> P.seasons j₁ (ξ₁ x)
variable (A:ℕ→ P.Apron)
local notation "QA"=> ordinary A
local notation "QB"=> ordinary (fun i=> P.drumStep (A i))
variable (t:ℝ≥0)(h:0<t)(q:Tendsto (fun i=>(A i).s) atTop atTop)
local notation "u₁" => t/2
local notation "Λ"=> t/2
local notation "xW" x:max i:max r:max s:max => (QA).Wstage x j₁ r s i
local notation "jW" x:max i:max r:max s:max=> (QB).Wstage x j₁ r s i
local notation "δ" i:max=> P.burst (A i).s
-- positive time price in G for one step. accounts Proof `M7`
lemma music_step (u: (QA).WPermit x j₁) (q:Tendsto (fun i=>(A i).s) atTop atTop): (QB).WPermit x j₁:=by
 let b:= P.yearly_cap x A u; let d(i):= P.burst (A i).s; have hd:Tendsto d atTop (𝓝 0):= P.burst_zero.comp q
 refine ⟨P.priceLimit x A q b,?_ ,?_⟩
 · let X(t:ℝ≥0)(i:ℕ):=P.stageG j₁ (ξ₁ x) (A i) t (t-d i)
   have ht:RisePrice X:= arcFare P x A hd u -- local helper
   obtain ⟨k,C,w,z⟩:= fare_action (T₁ x) d hd (Eventually.of_forall fun _=>P.burst_p _) ht
   refine ⟨k,C,w,fun t a v=>?_⟩; filter_upwards [z t a v, (P.priceLimit x A q b j₁).eventually (ge_mem_nhds (half_pos a))] with i x' h; rw [P.ordinary_paper x j₁ _ t t i]; change (t:ℝ)^k* ‖P.stageG j₁ (ξ₁ x) (P.drumStep (A i)) t t‖ ≤ C; rw [P.conductsG _ x _ h]; exact x'
 intro s h; change Travels (fun i=> (QB).Wstage x j₁ s s i); simp_rw [P.ordinary_paper]; exact (P.issue_budget x _ q b s h).Cauchy
where
  arcFare (P:Spine) (x:P.Spectrum0 3)(A:ℕ→ P.Apron){d:ℕ→ℝ≥0} (hd:Tendsto d atTop (𝓝 0))(u:(ordinary A).WPermit x 3): RisePrice (fun t i=> P.stageG 3 (P.advocate 3 x 3) (A i) t (t-d i)):=by
    obtain ⟨k,C,b,w⟩:= u.budget; refine ⟨k,2^k*C,by positivity,?_⟩; intro t a z; let s:= t/2; have h:s<t:=half_lt_self a; have he:0<s:= half_pos a
    have hp:Tendsto (fun i=>t-d i) atTop (𝓝 t):= by simpa only [tsub_zero] using Tendsto.sub (tendsto_const_nhds (x:=t)) hd
    filter_upwards [w s he (h.le.trans z),(u.thin 3).eventually (ge_mem_nhds he), hp.eventually (le_mem_nhds h)] with i h₁ h₂ h₃
    rw [← P.ordinary_paper x 3 A t (t-d i) i,(ordinary A).Wstage_more x 3 i h₂ h.le h₂ h₃]; apply le_trans (mul_le_mul_of_nonneg_left (P.stoves_price ..) (pow_nonneg (show 0≤(t:ℝ) from a.le) k)); rw [show (t:ℝ)=2*(s:ℝ) from ?_, _root_.mul_pow,mul_assoc]; exact mul_le_mul_of_nonneg_left h₁ (by positivity)
    unfold s; rw [NNReal.coe_div,NNReal.coe_ofNat]; ring
include h
lemma paysMusic (u:(QA).WPermit x j₁)(p:(QB).WPermit x j₁)(q:Tendsto (fun i=>(A i).s) atTop atTop): p.atHeat t= P.drumIssuer x u.atHeat t:= by
 let T':= P.yearly_cap x A u; let V:P.CapReady x (fun i=> P.drumStep (A i)):= P.yearly_cap x _ p
 rw [show u.atHeat=P.managed x A T' from P.affine_heat x _ T', show p.atHeat = P.managed x _ V from P.affine_heat x _ V]; exact P.uphill x A q T' rfl V t h -- implicit argument v related.
omit h
-- finite stencils Sponsor estimates with fixed offset δ(tolerance), bought at real widths eventually. For complex session all spectra, no moving amplitude costs.
def headlight (z:ℂ)(i:ℕ): (G₁ x).Op:= (T₁ x).F (duration (t/2)+z)*(QA).Wstage x j₁ (t/2) (t/2) i * (T₁ x).F (duration (t/2)-z)
local notation "W_sp" t:max i:max x:max=> (fun z=> P.headlight x A t z i)
-- disk of y
lemma staged_disk (z:ℂ)(h:z∈ ball (0:ℂ) ((Λ:ℝ≥0):ℝ)): duration (t/2)+z ∈ OS.Semigroup.inside ∧ duration (t/2)-z ∈ inside:=by
 have hz:= (Complex.abs_re_le_norm z).trans_lt (mem_ball_zero_iff.mp h)
 obtain ⟨c,v⟩:= abs_lt.mp hz; change 0<((t/2:ℝ≥0):ℝ)+ z.re ∧ 0< ((t/2:ℝ≥0):ℝ)- z.re; constructor<;>linarith only [c,v] -- LHS t NNReal + z.re? forces ℝ maybe coercion
lemma spot_price (A':ℝ)(i:ℕ)(B:‖xW x i (Λ) (Λ)‖≤ A') (z:ℂ)(h:z∈ball (0:ℂ) (((t/2:ℝ≥0)):ℝ)): DifferentiableAt ℂ (fun z=> P.headlight x A t z i) z ∧ ‖P.headlight x A t z i‖ ≤ A':=by
 let u:= t/2; let D:=duration u; let S':= T₁ x; let F:= xW x i u u
 obtain ⟨he,hq⟩:= staged_disk t z h
 unfold headlight; refine ⟨DifferentiableAt.mul (((S'.localHeat (D+z) he).differentiableAt.comp z (show DifferentiableAt ℂ (fun z:ℂ=>D+z) z from by fun_prop)).mul_const F) ((S'.localHeat (D-z) hq).differentiableAt.comp z (show DifferentiableAt ℂ (fun z:ℂ=>D-z) z from by fun_prop)),?_ ⟩
 exact (norm_mul_le ..).trans ((mul_le_of_le_one_right (norm_nonneg _) (S'.norm_row hq)).trans (((norm_mul_le ..).trans (mul_le_of_le_one_left (norm_nonneg _) (S'.norm_row he))).trans B)) -- norm_row implicit z
lemma headlight_at (d:ℝ≥0)(p:d<t/2)(i:ℕ)(h:(A i).allowance P 3 ≤ t/2): P.headlight x A t (duration d) i= xW x i (t+d) (t-d):=by
 let S':= T₁ x; let y:=t/2; have ht:t/2+t/2=t:= _root_.add_halves t; have hx:0≤d:=zero_le; have hy:y ≤ t:= half_le_self zero_le; have hu:d < t:= lt_of_lt_of_le p hy; have hz:0 < y+d:= add_pos_of_pos_of_nonneg (lt_of_le_of_lt (zero_le) p) (zero_le);
 have he:y≤t-d:= (le_tsub_iff_right hu.le).mpr ((add_le_add le_rfl p.le).trans ht.le)
 have hK:(t+d)-y=y+d:= by rw [←show y+y=t from ht,add_assoc,add_tsub_cancel_left]
 have ha:t-d-y=y-d:= by nth_rw 1 [←show y+y=t from ht,add_tsub_assoc_of_le p.le]; rw [add_tsub_cancel_left]
 unfold headlight; rw [show duration (t/2)+duration d=duration (t/2+d) from (by unfold duration; simp), show duration (t/2)-duration d=duration (t/2-d) from (by unfold duration; rw [NNReal.coe_sub p.le,Complex.ofReal_sub]), show (T₁ x).F (duration (t/2+d)) = _ from (T₁ x).roots_heat (show 0<t/2+d from hz), (T₁ x).roots_heat (tsub_pos_of_lt p), (QA).Wstage_more x j₁ i h (hy.trans (self_le_add_right ..)) h he,show t+d - t/2=y+d from hK,show t-d - t/2=y-d from ha] <;> try rfl -- tune
-- second-slope bound in target calendar, all γ
private lemma small_function {E:Type*}[NormedAddCommGroup E][NormedSpace ℂ E][CompleteSpace E](f:ℂ→E)(r C:ℝ)(h:0<r)(u:∀ z∈ball (0:ℂ) r,DifferentiableAt ℂ f z ∧ ‖f z‖≤ C): ∀ z∈ball (0:ℂ) r,DifferentiableAt ℂ (dslope f 0) z ∧ ‖dslope f 0 z‖ ≤ 2*C/r:=by
 intro z c; let A:= ball (0:ℂ) r; have he:DifferentiableOn ℂ f A:=fun x d=> (u x d).1.differentiableWithinAt
 have hp:Set.MapsTo f A (closedBall (f 0) (2*C)):= by intro x d; rw [mem_closedBall,dist_eq_norm]; exact (norm_sub_le ..).trans ((two_mul C) ▸ (add_le_add (u x d).2 (u 0 (mem_ball_self h)).2))
 exact ⟨((Complex.differentiableOn_dslope (ball_mem_nhds _ h)).mpr he).differentiableAt (isOpen_ball.mem_nhds c),Complex.norm_dslope_le_div_of_mapsTo_ball he hp c⟩
private lemma slope_lip {E:Type*}[NormedAddCommGroup E][NormedSpace ℂ E][CompleteSpace E](f:ℂ→E)(r C:ℝ)(h:0<r)(u:∀ z∈ball (0:ℂ) r,DifferentiableAt ℂ f z ∧ ‖f z‖≤C): ∀ z∈ball (0:ℂ) r,dist (dslope f 0 z) (dslope f 0 0) ≤ (2*(2*C/r)/r)*‖z‖:=by
 intro z c; by_cases e:z=0; · simp [e]
 have ht:0<‖z‖:= norm_pos_iff.mpr e; have hv:= (small_function (dslope f 0) r (2*C/r) h (small_function f r C h u) z c).2
 rw [dslope_of_ne _ e,slope_def_module,norm_smul,norm_inv,sub_zero,inv_mul_eq_div, div_le_iff₀ ht] at hv
 exact (dist_eq_norm ..).trans_le hv

private lemma dn (d:ℝ≥0):‖duration d‖=(d:ℝ):= by simp [duration,Real.norm_of_nonneg d.prop] -- maybe equality d ↑ issue
lemma light_music (z: P.Commission j₁ QA)(u:Tendsto (fun i=>(A i).s) atTop atTop) : P.Sponsor j₁ {QA} QB:=by
 -- omit h below first! shadow t h take from signature unwanted. tune
 intro t h β ε e p
 let r:=(t/2:ℝ≥0); have hr:0<(r:ℝ):= half_pos h; have hR:(r:ℝ) < (t:ℝ) := show t/2<t from half_lt_self h
 obtain ⟨C,b,pH⟩:= z.threshold r hr; let w:= 2*(2*C/(r:ℝ))/(r:ℝ); have hw:0≤w:= by unfold w; positivity
 let Y:= ε/(2*w+1); have hy:0<Y:= by unfold Y; positivity
 obtain ⟨c,hc,hz⟩:= exists_between (lt_min (lt_min hr hy) e); let d:=c.toNNReal; have hce:(d:ℝ)=c:=Real.coe_toNNReal c hc.le; have hd:0<d:= Real.toNNReal_pos.mpr hc; have hz₁:(d:ℝ)<(r:ℝ):= hce.trans_lt ((hz.trans_le (min_le_left ..)).trans_le (min_le_left ..)); let F₀:= (duration d)⁻¹
 let Q:P.Stunt:= ⟨ordinary A,F₀,c⟩; let bq:P.Stunt:=⟨ordinary A,-F₀,0⟩; let U: List P.Stunt:= [Q,bq]; refine ⟨U,?_,?_⟩
 · intro i g; change i ∈ [Q,bq] at g; rcases List.mem_cons.mp g with g|g
   · subst i; refine ⟨rfl,?_,?_⟩ <;> change |c|< _; rw [abs_of_pos hc]; exact hz.trans_le (min_le_right ..); rw [abs_of_pos hc]; exact (hce ▸ hz₁).trans hR
   rw [List.mem_singleton.mp g]; refine ⟨rfl,?_,?_⟩ <;> change |(0:ℝ)| < _; simpa using e; exact (abs_zero.le).trans_lt h -- avoid semicolon distribution across goals
 have he(i:ℕ)(a:ℝ≥0)(gq:0<a)(e:a<r)(g':(A i).allowance P 3≤ r) (x:P.Spectrum0 3): dslope (fun z=>P.headlight x A t z i) 0 (duration a)= (duration a)⁻¹ • (xW x i (t+a) (t-a) - xW x i t t):=by
    have ht:P.headlight x A t 0 i=xW x i t t:= by simpa only [duration,NNReal.coe_zero, Complex.ofReal_zero,add_zero,tsub_zero] using P.headlight_at x A t 0 (show 0<r from hr) i g'
    rw [dslope_of_ne _ (norm_pos_iff.mp ((dn a).symm ▸ (show (0:ℝ)< (a:ℝ) from gq))),slope_def_module,sub_zero,P.headlight_at x A t a e i g',ht]
 filter_upwards [(z.being j₁).eventually (ge_mem_nhds (show 0<r from hr)),pH,(P.burst_zero.comp u).eventually (ge_mem_nhds hd)] with i q k v x
 let h₀:= δ i; have hT:h₀≤ d:=v; let f(z:ℂ):=P.headlight x A t z i; have HP:= slope_lip f (r:ℝ) C hr (fun i h=> P.spot_price x A t C _ (k x) i h)
 let W':= (Q.wage • xW x i (t+d) (t-d) + bq.wage • xW x i t t); have hX: P.VistaSum x j₁ U t i = dslope f 0 (duration d):= by
    have hx: (ticketPlus t c) = t+d:= NNReal.eq (by unfold ticketPlus; rw [Real.coe_toNNReal _ (by positivity),NNReal.coe_add,hce]); have hx': ticketMinus t c=t-d:= by unfold ticketMinus; rw [NNReal.sub_def,hce];
    have hz: P.VistaSum x j₁ U t i=W':= by unfold U VistaSum; simp only [List.map_cons,List.map_nil,List.sum_nil,List.sum_cons,Stunt.toner,Q,bq,add_zero]; rw [hx,hx']; simp only [ticketPlus,ticketMinus,add_zero,sub_zero,Real.toNNReal_coe,W',Q,bq]
    rw [hz]; change W'= dslope _ 0 _; unfold W'; dsimp only [Q,bq,F₀]; unfold f; rw [he i d hd hz₁ q x, smul_sub, neg_smul,sub_eq_add_neg]
 have hpz: P.headlight x A t (duration h₀) i=xW x i (t+h₀) (t-h₀):= P.headlight_at x A t _ (lt_of_le_of_lt hT hz₁) i q
 have hk:(QB).Wstage x j₁ t t i= dslope f 0 (duration h₀):= by
    unfold f; rw [he i h₀ (P.burst_p _) (lt_of_le_of_lt hT hz₁) q x, P.ordinary_paper]; change P.stageG j₁ (ξ₁ x) (P.drumStep (A i)) t t=_; rw [P.step_price_G _ x t, P.ordinary_paper,P.ordinary_paper]; rw [step_s]; exact (add_le_add (show (A i).allowance P 3≤ r from q) ((hT.trans hz₁.le) : h₀≤r)).trans_eq (_root_.add_halves t)
 rw [hk,hX]; have HL: dist (dslope f 0 (duration h₀)) (dslope f 0 0)≤ w*(h₀:ℝ):= ((dn h₀) ▸ (HP (duration h₀) (mem_ball_zero_iff.mpr ((dn h₀).trans_lt (lt_of_le_of_lt (show (h₀:ℝ)≤(d:ℝ) from hT) hz₁)))))
 have HR : dist (dslope f 0 0) (dslope f 0 (duration d)) ≤ w*(d:ℝ):= (dist_comm ..).trans_le ((dn d) ▸ (HP (duration d) (mem_ball_zero_iff.mpr ((dn d).trans_lt hz₁))))
 have he:(d:ℝ) ≤ Y:= hce.trans_le (hz.le.trans ((min_le_left ..).trans (min_le_right ..)))
 have hp: Y*(2*w+1)= ε:= div_mul_cancel₀ _ (by positivity); refine (dist_triangle _ _ _).trans ((add_le_add HL HR).trans ?_); nlinarith only [hw,p,hp,he, show (h₀:ℝ)≤(d:ℝ) from hT,hy]

end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open YM.CF.Buffered.Afterglow.Tower.VacuumSelection
#print axioms Spine.Commission.wander
#print axioms Spine.headlight_at
#print axioms Spine.spot_price
#print axioms Spine.slope_lip
#print axioms Spine.music_step
#print axioms Spine.paysMusic
#print axioms Spine.light_music
