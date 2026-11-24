import GaugeFieldConstruction.Wilts
import YM.Work.F03.Transport
/-!
# Sector API. read hull, tied center, radius payments.
-/
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 25000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
noncomputable section
namespace YM.FlightFlux
open Lattice Function Finset Wilson RG Gauge Work.F03
open scoped Topology BigOperators Matrix.Norms.Frobenius Pointwise Matrix
variable {I:Type*} [DecidableEq I][Fintype I]
variable {E:Type*} [NormedAddCommGroup E][NormedSpace ℝ E]
local notation "b₁" i:max=> Pi.single i (1:ℤ)
open Fluxim
variable {n: Side}{G: Gauge}
abbrev stem(o i:Site n):= lift (i-o)
abbrev spread (x:Shape I):ℕ:=univ.sup (fun i=> (x i).natAbs)
lemma height_l (x:Shape I)(d:I): (x d).natAbs ≤lateral x:= single_le_sum (f:=fun i=>(x i).natAbs) (fun i _=> Nat.zero_le _) (mem_univ d) -- elaboration tune
lemma spread_money (x:Site n): spread (lift x)=pdist x:=rfl
lemma spread_zero : spread (0:Shape I)=0:=by simp [spread]
lemma stem_t (x y:Site n) : lateral (stem x y)≤4*separation y x:=by
 unfold lateral; apply (sum_le_sum (f:=fun i=> ((stem x y) i).natAbs) (g:=fun i=>pdist (y-x)) (fun _ _=>component_le ..)).trans_eq; simp [Axis,separation]
def camW (o:Site n) (v:Wheel Axis E)(e: Edge (Site n)):E:= v e.2 (stem o e.1)
def plot (o:Site n) (v: Wheel Axis G.Color)(r:ℝ): RG.Directions G n:= r • camW o v
lemma lift_path {p:Cover}{x:Site n}(h:x=wrap n p)(l:2*lateral p< n.val) : lift x=p:= lift_eq_iff.mpr ⟨h,fun i=> by have hp: (p i).natAbs ≤lateral p:=height_l ..; omega⟩
lemma stem_step (o v:Site n)(i:Axis)(p:10*(separation v o+1)<n.val): stem o (v+step i)=stem o v+(step i:Cover):=by
 apply lift_path; · rw [map_add,stem,wrap_lift,wrap_step]; abel
 have hp:= stem_t o v; have ht:lateral (step i: Cover)=1:= lateral_single i _; have hb:= lateral_add (stem o v) (step i:Cover); omega
-- tighter lift bounds even at minimum witness $|i-o|<n/10$. need n.val≥10.
lemma stem_f (o v:Site n)(i:Axis)(p:10*separation v o<n.val)(t:10≤ n.val): stem o (v+step i)=stem o v+(step i:Cover):=by
 apply lift_eq_iff.mpr; refine ⟨?_,fun j=>?_⟩
 · rw [map_add,stem,wrap_lift,wrap_step]; abel
 have he:=component_le (v-o) j; unfold separation at p; simp only [Pi.add_apply,step_apply,stem]; split_ifs <;> omega
open Exterior
abbrev mapCo (X:Directions G n): fieldDir G n 1:= fun i=> X (i.1,axisEquiv.symm i.2)
@[simp] lemma map_s (X:Directions G n): collect G (mapCo X)=X:=by funext x; unfold collect mapCo; rw [←coord_map, Equiv.symm_apply_apply]
@[simp] lemma map_R (v:fieldDir G n 1): mapCo (collect G v)=v:=by funext x; unfold mapCo collect; rw [← coord_map,Equiv.apply_symm_apply]
@[simp] lemma represent_p (X: Directions G n): Precision.represent (mapCo X)=increment 1 X:= by rw [Precision.represent,map_s]
lemma linkage (X:Directions G n)(s: Slot)(o:Site n): HasDerivAt (fun t:ℝ=> s.atSite (increment 1 (t • X)) o) (faceCurl (slotFace s o) (mapCo X)) 0:=by
 have he:=slot_deriv s o (mapCo X); simp_rw [show ∀ t:ℝ,t • mapCo X=mapCo (t • X) from fun t=>rfl, represent_p] at he; exact he
lemma liaison (F:Wheel Axis G.Color)(o v:Site n)(b:PlaqAxes)(p:10*separation v o<n.val)(t:10≤ n.val): faceCurl (v,b) (mapCo (camW o F))= CurlMap F b.val.1 b.val.2 (stem o v):=by
 ext j; unfold faceCurl dColor; dsimp only; change (d 1 n*ᵥ parts G 1 (mapCo (camW o F)) j) (v,plaquette b)=_; rw [d_plaquettes];
 unfold parts mapCo; simp_rw [← coord_map,Equiv.symm_apply_apply]; unfold camW; rw [stem_f o v _ p t,stem_f o v _ p t]; rfl
lemma liaison_h(F:Wheel Axis G.Color)(o v:Site n)(b:PlaqAxes)(p:10*separation v o<n.val)(t:10≤ n.val)(u:ℝ): faceCurl (v,b) (mapCo (plot o F u))= u • CurlMap F b.val.1 b.val.2 (stem o v):=by rw [← liaison F o v b p t,show mapCo (plot o F u)=u • mapCo (camW o F) from rfl]; ext j; unfold faceCurl dColor; dsimp only; change ((d 1 n) *ᵥ (u • parts G 1 (mapCo _) j)) _=u • _; simp only [Matrix.mulVec_smul,Pi.smul_apply]; rfl

-- Γ unit vectors in any Kind
lemma slope_est (v:I→ E)(x:Shape I)(d:ℝ)(h:0≤d)(p:∀ i,‖v i‖≤d): ‖slope v x‖ ≤ lateral x*d:=by
 apply (norm_sum_le ..).trans ((sum_le_sum (fun i _=>?_) : (∑ i:I,‖digit x i • v i‖) ≤ ∑ i:I,(↑(x i).natAbs:ℝ)*d).trans_eq ?_)
 swap; · unfold digit; rw [norm_smul,Real.norm_eq_abs,←Int.cast_abs,←Int.natCast_natAbs,Int.cast_natCast]; exact mul_le_mul_of_nonneg_left (p i) (Nat.cast_nonneg _)
 rw [←sum_mul,lateral, Nat.cast_sum]
lemma formC_norm (v:fluxV E I)(i:I)(x:Shape I): ‖formC v i x‖ ≤ (1/2:ℝ)*lateral x*‖v‖:=by
 change ‖(1/2:ℝ) • slope (fun j=>v.val j i) x‖ ≤ _; rw [norm_smul,Real.norm_of_nonneg (by norm_num : 0≤(1/2:ℝ)),mul_assoc]; apply mul_le_mul_of_nonneg_left _ (by norm_num); exact slope_est _ _ _ (norm_nonneg _) fun j=> (norm_le_pi_norm (v.val j) i).trans (norm_le_pi_norm v.val j)
lemma formT_norm (v:fluxT E I)(i:I)(x:Shape I): ‖formT v i x‖ ≤ (lateral x:ℝ) *(1+lateral x)*‖v‖:=by
 let H:ℝ:= lateral x; let M:=(1+H)*‖v‖; have h:0≤H:= Nat.cast_nonneg _; let F(j):= fun k=> v.val k j i; let Xop (j:I):=∑ k:I,lineSi x i k • v.val k j i
 have hp(j): ‖Xop j‖≤ M:=by
    rw [show Xop j=slope (F j) x+(1/2:ℝ) • _ from slender_out ..]; apply (norm_add_le ..).trans
    have ht(k): ‖F j k‖ ≤ ‖v‖:= (norm_le_pi_norm (v.val k j) i).trans ((norm_le_pi_norm (v.val k) j).trans (norm_le_pi_norm v.val k))
    unfold M; rw [norm_smul,Real.norm_eq_abs,abs_of_pos (by norm_num : (0:ℝ)<1/2)]; have hx: ‖slope (F j) x‖ ≤ H*‖v‖:= slope_est _ _ _ (norm_nonneg _) ht; change ‖slope (F j) x‖ +(1/2:ℝ) *‖F j i‖ ≤_; linarith only [hx,ht i,norm_nonneg v]
 change ‖(1/3:ℝ) • slope Xop x‖≤ _; rw [norm_smul,Real.norm_of_nonneg (by norm_num : 0≤(1/3:ℝ)),mul_assoc]; exact (mul_le_of_le_one_left (norm_nonneg _) (by norm_num)).trans (slope_est Xop x M (by positivity) hp)
lemma formC_life (v:fluxV G.Color Axis)(o:Site n)(p:BudgetPoint)(u:‖v‖ ≤ 1/50) : p.dirBound o (plot o (formC v) p.threshold):=by
 have hp:=p.threshold_pos; intro i; let H:ℝ:= separation i.1 o; have h:0≤H:=Nat.cast_nonneg _; unfold plot; rw [Pi.smul_apply,norm_smul, Real.norm_of_nonneg hp.le]; apply mul_le_mul_of_nonneg_left _ hp.le
 apply (formC_norm v _ _).trans; let X:= stem_t o i.1; let Y:ℝ:= lateral (stem o i.1); have hg:Y≤4*H:=by unfold Y H; exact_mod_cast X
 calc _ ≤ (1/2:ℝ)*(4*H)*(1/50) := by gcongr
      _ ≤ 1+H:=by linarith only [hg,h]
      _ ≤ _^p.power:= by exact le_self_pow₀ (le_add_of_nonneg_right h) (by have hp:=p.power_ge; omega) -- tune
lemma formT_life (v:fluxT G.Color Axis)(o: Site n)(p:BudgetPoint)(u:‖v‖ ≤ 1/50): p.dirBound o (plot o (formT v) p.threshold):=by
 have hp:=p.threshold_pos; intro i; unfold plot; rw [Pi.smul_apply,norm_smul,Real.norm_of_nonneg hp.le]; apply mul_le_mul_of_nonneg_left _ hp.le; apply (formT_norm v _ _).trans; let H:ℝ:= separation i.1 o; have h:0≤H:= Nat.cast_nonneg _; let Y:ℝ:= lateral (stem o i.1); have hg:Y≤4*H:=by unfold Y H; exact_mod_cast stem_t o i.1
 refine le_trans ?_ (pow_le_pow_right₀ (le_add_of_nonneg_right h : 1≤1+H) p.power_ge);
 calc _ ≤ (4*H)*(1+4*H)*(1/50):=by gcongr
      _ ≤ _ := by nlinarith only [h, sq_nonneg H]
end YM.FlightFlux
end
