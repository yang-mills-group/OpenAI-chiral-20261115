import YM.SU5.Circuit.Lieble
set_option autoImplicit false
set_option maxHeartbeats 250000
noncomputable section
namespace YM.Regis.Head.Brecht
open Function Filter Metric Lattice Laurent Next.Free Bloch Finset Exterior Precision RG Work.F03 Gleam MeasureTheory NormedSpace ProbabilityTheory Wilson Matrix
open Circuit
open scoped Matrix Topology BigOperators NNReal ENNReal InnerProductSpace ContDiff Classical
variable {ι J: Type*} [NormedAddCommGroup ι][InnerProductSpace ℝ ι] {G:Gauge} (x:ι){k:ℝ}(p:0 < k)
def barQ (k t:ℝ):ℝ:= (1+t^2/k)⁻¹
def drinkT (k:ℝ)(x:ι):ι:= barQ k ‖x‖ • x
include p
lemma volumeT (a:ℝ):0 ≤ barQ k a∧barQ k a ≤ 1:=by
 constructor; · unfold barQ; positivity
 exact (inv_le_one₀ (by positivity)).2 (le_add_of_nonneg_right (by positivity : 0≤ a^2/k))
lemma thirst (a:ℝ): 1-barQ k a≤ a^2/k:=by
 have hx: (1+a^2/k)*barQ k a=1:=mul_inv_cancel₀ (by positivity)
 have ht:=mul_le_of_le_one_right (show 0≤ a^2/k by positivity) (volumeT p a).2
 rw [add_mul] at hx; linarith
lemma tasteB : ‖drinkT k x‖≤ 1+k:=by
 unfold drinkT; rw [norm_smul,Real.norm_of_nonneg (volumeT p _).1,barQ,mul_comm,← div_eq_mul_inv,div_le_iff₀ (by positivity : 0<(1+ ‖x‖^2/k:ℝ))]; let y:=‖x‖; field_simp; nlinarith [sq_nonneg (k-y),mul_nonneg p.le (sq_nonneg y),norm_nonneg x]
private lemma slope_drink {x y:ι}(h:‖x‖≤‖y‖): dist (drinkT k x) (drinkT k y) ≤ 3* dist x y:=by
 let V:=‖x‖; let W:=‖y‖; let a:=barQ k V; let b:=barQ k W; let D:=V^2/k; let S:=W^2/k; have hx:0<V+1:= by unfold V; positivity; -- tune scope
 have ht:0≤D:= by unfold D; positivity
 have hs:0≤S:= by unfold S; positivity
 have he:0≤a-b:= sub_nonneg.mpr (by unfold a b barQ; exact inv_anti₀ (by positivity) (by gcongr))
 have hh:a-b≤(W-V)*(W+V)/k/(1+S):=by
    have hz:k*(1+S)>0:=by positivity
    have hl:a-b=(S-D)/(1+D)/(1+S):=by unfold a b barQ; change (1+D)⁻¹- _= _ ; change _-(1+S)⁻¹=_; field_simp; ring
    have hm:S-D=(W-V)*(W+V)/k:=by unfold S D; ring
    rw [hl, hm]; apply div_le_div_of_nonneg_right _ (by positivity); have hh:V≤W:=h; apply div_le_self ?_ (by linarith only [ht]); unfold V W at *; positivity
 rw [dist_eq_norm]; let t:= dist x y;
 change ‖a • x-b • y‖≤_; rw [show a • x-b • y=(a-b) • x+b • (x-y) from (by rw [sub_smul,smul_sub]; abel)]
 apply (norm_add_le ..).trans
 rw [norm_smul,norm_smul,Real.norm_of_nonneg he,Real.norm_of_nonneg (volumeT p _).1,←dist_eq_norm];
 have hp: W-V≤ dist x y:= by rw [dist_comm x y,dist_eq_norm]; exact norm_sub_norm_le ..
 have hw: (a-b)*V≤2*t:=by
    apply (mul_le_mul_of_nonneg_right hh (norm_nonneg _)).trans
    have hh:V≤W:= h; have hv: (W+V)*V/k/(1+S)≤2:=by rw [div_le_iff₀ (by positivity : 0<1+S)]; unfold S; field_simp; nlinarith only [p,mul_le_mul_of_nonneg_left hh (norm_nonneg y),pow_le_pow_left₀ (norm_nonneg x) hh 2]
    calc _=(W-V)*((W+V)*V/k/(1+S)):=by ring
         _≤_:= le_trans (mul_le_mul_of_nonneg_left hv (sub_nonneg.mpr h)) (by linarith only [show W-V≤t from hp])
 linarith only [hw, mul_le_of_le_one_left (show 0≤dist x y from dist_nonneg) (show b≤1 from (volumeT p _).2)] -- tune keyword
lemma speedK : LipschitzWith 3 (drinkT (ι:=ι) k):=by apply LipschitzWith.of_dist_le_mul; intro x y; norm_num; rcases le_total ‖x‖ ‖y‖ with u|u; exact slope_drink p u; rw [dist_comm,dist_comm x]; exact slope_drink p u
lemma taste_smooth: ContDiff ℝ 1 (drinkT (ι:=ι) k):=by
 have he: ContDiff ℝ 1 (fun x:ι=> (1+ ‖x‖^2/k)⁻¹):= (contDiff_const.add ((contDiff_norm_sq ℝ).div_const _)).inv (fun i=> by change 1+‖i‖^2/k≠0; positivity);
 exact he.smul contDiff_id
omit p
lemma taste_transform (U:G.El)(x:G.Color):drinkT k (G.adjoint U x)=G.adjoint U (drinkT k x):=by unfold drinkT; rw [G.norm_adjoint,map_smul]
-- both color curves anchored at same origin (relative to the fixed-reader cover); transports included for physical mark.
def plateView (K D:PlaqAxes)(a b:Cover){k:ℝ}(G:Gauge)(p:0<k): Etch G Bool where
 slot i:= if i then colorOf D b else colorOf K a
 f y:= inner ℝ (drinkT k (y false)) (drinkT k (y true))
 arc:= (1+k)^2
 bound i:=by
    apply (abs_real_inner_le_norm ..).trans; rw [pow_two]; exact mul_le_mul (tasteB _ p) (tasteB _ p) (norm_nonneg _) (by positivity)
 diff:= ((taste_smooth p).comp (contDiff_apply ℝ G.Color false)).inner ℝ ((taste_smooth p).comp (contDiff_apply ℝ G.Color true))
 favor:= ⟨6*(1+k),by positivity⟩
 steady:=LipschitzWith.of_dist_le_mul (fun i j=> by
    let X:=fun b=> drinkT k (i b); let V:=fun b=>drinkT k (j b); change |inner ℝ (X false) (X true)-inner ℝ (V false) (V true)| ≤ 6*(1+k)*_
    have hl(c): ‖X c-V c‖≤3*dist i j:=by rw [← dist_eq_norm]; refine ((speedK p).dist_le_mul (i c) (j c)).trans ?_; push_cast; apply mul_le_mul_of_nonneg_left _ (by norm_num); rw [dist_eq_norm (i c),dist_eq_norm i]; exact norm_le_pi_norm (i-j) c;
    let x:= inner ℝ (X false-V false) (X true); let y:=inner ℝ (V false) (X true-V true); rw [show inner ℝ (X false) (X true)-inner ℝ (V false) (V true)=x+y from (by unfold x y; rw [inner_sub_left,inner_sub_right]; ring)]; apply le_trans (abs_add_le ..); apply (add_le_add ((abs_real_inner_le_norm ..).trans (mul_le_mul (hl false) (tasteB _ p) (norm_nonneg _) (show 0≤3*dist i j by positivity))) ((abs_real_inner_le_norm ..).trans (mul_le_mul (tasteB _ p) (hl true) (norm_nonneg _) (by positivity)))).trans; exact Eq.le (by ring))
 move z i:= by
              simp_rw [taste_transform]
              let X:G.Color →ₗᵢ[ℝ] G.Color:= {G.adjoint z with norm_map':= G.norm_adjoint z }; exact X.inner_map_map _ _
end YM.Regis.Head.Brecht
#print axioms YM.Regis.Head.Brecht.taste_smooth
#print axioms YM.Regis.Head.Brecht.plateView
