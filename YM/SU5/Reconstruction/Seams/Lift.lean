import YM.CF.BProof.Floral.Hol
import YM.Analysis.Weak
import YM.Spectral.Projection
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.Analytic.IsolatedZeros
/-!
# Lift to operator analytic continuation from scalar data and real edge

Keeping unilateral spectral budget. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.ConePrice
namespace Sail
open Function Set Filter InnerProductSpace MeasureTheory Analysis Metric
open scoped Topology BigOperators NNReal ENNReal ComplexOrder InnerProductSpace
variable {H : Hilbert} {D : Set ℂ} (Q : H → ℂ→ℂ)
local notation "P" => Q
local notation "I"=> Complex.I

structure Candidate (D : Set ℂ) (Q : H → ℂ→ℂ) (F : ℝ→ H.Op) : Prop where
 ticket : IsOpen D
 closeUp : IsPreconnected D
 ground : ∀ x : ℝ, (x:ℂ)∈D
 straight (v:H): AnalyticOnNhd ℂ (Q v) D
 cost (v:H)(z:ℂ)(p:z∈D): ‖Q v z‖≤ ‖v‖^2
 initial (v:H)(t:ℝ): Q v t = inner ℂ v (F t v)
local notation "diag" T=> fun v:H=>inner ℂ v ((T) v) -- syntax
noncomputable def mixed (x y:H) (z:ℂ) :=
  (Q (x+y) z-Q (x-y) z-I*Q (x+I • y) z+I*Q (x-I • y) z)/4
local notation "M" => mixed Q
variable {F : ℝ→ H.Op} (L : Candidate D Q F)
include L
lemma current (x y:H)(p:ℝ): mixed Q x y p=inner ℂ x (F p y):=by
  unfold mixed; simp_rw [L.initial,map_add,map_sub,inner_add_left,inner_add_right,inner_sub_left,inner_sub_right,map_smul,inner_smul_left,inner_smul_right]
  simp only [Complex.conj_I]
  ring_nf
  simp
  ring

lemma hol_m (x y:H): AnalyticOnNhd ℂ (M x y) D:=
  fun z p=> AnalyticAt.div (((((L.straight _ _ p).sub (L.straight _ _ p)).sub (analyticAt_const.mul (L.straight _ _ p))).add (analyticAt_const.mul (L.straight _ _ p)))) analyticAt_const (by norm_num)
omit L Q
lemma pioneer {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {M₁ N : ℂ→E} {A : Set ℂ}
    (t:IsPreconnected A) {w : ℝ} (wA:(w:ℂ)∈ A) (u v:ℝ) (h : u < w ∧ w < v)
    (p: AnalyticOnNhd ℂ M₁ A) (q:AnalyticOnNhd ℂ N A) (e:∀ x ∈ Ioo u v, M₁ (x:ℂ)=N (x:ℂ)) : EqOn M₁ N A := by
  apply AnalyticOnNhd.eqOn_of_preconnected_of_frequently_eq p q t wA
  intro o
  have ht: Tendsto (fun x:ℝ=>(x:ℂ)) (𝓝[≠] w) (𝓝[≠] (w:ℂ)) := tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ((Complex.continuous_ofReal.tendsto _).mono_left nhdsWithin_le_nhds) ((show ∀ᶠ x in 𝓝[≠] w,x≠w from self_mem_nhdsWithin).mono (fun x h => fun (p : (x:ℂ)=(w:ℂ)) => h (Complex.ofReal_injective p)))
  obtain ⟨w,u',v'⟩:= ((ht.eventually o).and (mem_nhdsWithin_of_mem_nhds (Ioo_mem_nhds h.1 h.2))).exists
  exact u' (e w v')
include L Q
lemma left_part (x z y:H) (t:ℂ) (p:t∈D): M (x+z) y t=M x y t+M z y t:= by
  apply pioneer L.closeUp (L.ground 0) (-1) 1 (by norm_num) (hol_m Q L _ _) (AnalyticOnNhd.add (hol_m Q L _ _) (hol_m Q L _ _)) _ p
  intro x v; change mixed .. = mixed Q _ _ _ + mixed Q _ _ _; simp [current Q L,inner_add_left]
lemma right_part (x z y:H) (t:ℂ) (p:t∈D): M x (y+z) t=M x y t+M x z t:= by
  apply pioneer L.closeUp (L.ground 0) (-1) 1 (by norm_num) (hol_m Q L _ _) (AnalyticOnNhd.add (hol_m Q L _ _) (hol_m Q L _ _)) _ p
  intro x v; change mixed .. = mixed Q _ _ _ + mixed Q _ _ _; simp [current Q L,inner_add_right]
lemma left_scale (x y:H)(c t:ℂ) (p:t∈D): M (c • x) y t=star c*M x y t:= by
  apply pioneer L.closeUp (L.ground 0) (-1) 1 (by norm_num) (hol_m Q L _ _) (AnalyticOnNhd.mul analyticOnNhd_const (hol_m Q L _ _)) _ p -- pointwise mul
  intro x v; change mixed .. = star c*mixed Q _ _ _; rw [current Q L,current Q L, inner_smul_left]; rfl
lemma right_scale (x y:H)(c t:ℂ) (p:t∈D): M x (c • y) t=c*M x y t:= by
  apply pioneer L.closeUp (L.ground 0) (-1) 1 (by norm_num) (hol_m Q L _ _) (AnalyticOnNhd.mul analyticOnNhd_const (hol_m Q L _ _)) _ p -- pointwise mul
  intro x v; change mixed .. = _ * mixed Q _ _ _; rw [current Q L,current Q L,map_smul, inner_smul_right]

lemma norm_ticket (x y:H) (v: ‖x‖≤1) (u:‖y‖≤1)(t:ℂ)(p:t∈D) : ‖M x y t‖ ≤4:=by
  have he (x:H)(u:‖x‖≤2): ‖Q x t‖≤4 := (L.cost x t p).trans (by have h:= norm_nonneg x; nlinarith)
  have h(z:H)(p:‖z‖≤1) : ‖x+z‖≤2∧ ‖x-z‖≤2 := ⟨(norm_add_le ..).trans (by linarith),(norm_sub_le ..).trans (by linarith)⟩
  obtain ⟨h₁,h₂⟩:=h y u; obtain ⟨h₃,h₄⟩:=h (I • y) (by simpa [norm_smul] using u)
  unfold mixed; rw [norm_div,div_le_iff₀] -- use div_le_iff₀ of norm ; tune
  swap; · norm_num
  refine (norm_add_le ..).trans ?_
  simp only [norm_mul,Complex.norm_I,one_mul]
  refine le_trans (add_le_add_left (norm_sub_le ..) _) ?_
  simp only [norm_mul,Complex.norm_I,one_mul]; norm_num; nlinarith [norm_sub_le (Q (x+y) t) (Q (x-y) t), he _ h₁, he _ h₂, he _ h₃, he _ h₄]
lemma norm_fare (x y:H)(t:ℂ)(p:t∈D) : ‖M x y t‖ ≤ 4 * ‖x‖ * ‖y‖ := by
  by_cases c:x=0
  · rw [c,show M 0 y t=0 from by simpa using left_scale Q L x y 0 t p]; simp
  by_cases b:y=0
  · rw [b,show M x 0 t=0 from by simpa using right_scale Q L x y 0 t p]; simp
  let w (y:H):ℂ:= ((‖y‖:ℝ):ℂ); let φ(x:H):= (w x)⁻¹ • x
  have ht(x:H)(p:x≠0):‖φ x‖ ≤ 1:=by simp [φ,norm_smul,w,norm_ne_zero_iff.mpr p]
  have hp:=norm_ticket Q L _ _ (ht _ c) (ht _ b) t p; unfold φ at hp; rw [left_scale Q L _ _ _ _ p,right_scale Q L _ _ _ _ p] at hp; simp [w] at hp -- may simplify
  let hv : 0 < ‖x‖:= norm_pos_iff.mpr c; let hu : 0 < ‖y‖:= norm_pos_iff.mpr b
  calc
    _ = ‖y‖* ‖x‖ * (‖x‖⁻¹ * (‖y‖⁻¹ * ‖M x y t‖)) := by field_simp
    _ ≤ ‖y‖* ‖x‖ *4 := mul_le_mul_of_nonneg_left hp (by positivity)
    _ = _ := by ring

private def voice (t:ℂ)(p:t∈D)(y:H): H→L[ℂ]ℂ :=
  LinearMap.mkContinuous
    { toFun x:= star (M x y t)
      map_add' x z:=by rw [left_part Q L _ _ _ t p]; exact star_add ..
      map_smul' c x:=by rw [left_scale Q L _ _ _ t p,star_mul,star_star]; exact mul_comm .. } (4*‖y‖) (fun u=> by change ‖star _‖≤ _; rw [norm_star,mul_right_comm]; exact norm_fare Q L u y t p)
private def vessel (t:ℂ)(p:t∈D)(y:H) : H:= (InnerProductSpace.toDual ℂ H).symm (voice Q L t p y)
private lemma duct (t:ℂ)(p:t∈D)(x y:H): inner ℂ x (vessel Q L t p y)= M x y t:= by
  have h:inner ℂ (vessel Q L t p y) x= star (M x y t):= InnerProductSpace.toDual_symm_apply
  rw [←inner_conj_symm]; change star _=_; rw [h,star_star]
omit Q L
lemma from_voice (x:H)(C:ℝ)(h:∀ y:H,‖inner ℂ y x‖ ≤ C*‖y‖) (p:0≤C) : ‖x‖ ≤ C:=by
  rcases eq_or_ne x 0 with rfl|e; · simpa
  have he:=h x; rw [inner_self_eq_norm_sq_to_K] at he; simp only [norm_pow] at he
  simp at he; nlinarith [norm_pos_iff.mpr e]
include Q L
-- linear operator with this key. Only claim within the strip
private def bound (z:ℂ)(p:z∈D) : H.Op := LinearMap.mkContinuous
    { toFun y:= vessel Q L z p y
      map_add' x y:= by
        apply ext_inner_left ℂ; intro y; rw [inner_add_right,duct,duct,duct,right_part Q L _ _ _ z p]
      map_smul' c x:= by
        apply ext_inner_left ℂ; intro y; change inner ℂ y _=inner ℂ y (c • vessel Q L z p x); rw [inner_smul_right,duct,duct,right_scale Q L _ _ _ z p] } 4 (fun x=> from_voice _ _ (fun y=> by change ‖inner ℂ y (vessel Q L z p x)‖ ≤_; rw [duct,mul_right_comm]; exact norm_fare Q L _ _ z p) (by positivity))
noncomputable def sailing (z:ℂ) : H.Op := by classical exact if p:z∈D then bound Q L z p else 0
lemma attends (x y:H)(t:ℂ)(p:t∈D) : inner ℂ x (sailing Q L t y) = M x y t := by unfold sailing; rw [dif_pos p]; exact duct ..
lemma sailing_real (t:ℝ) : sailing Q L (t:ℂ)=F t:= by
   ext1 y; apply ext_inner_left ℂ; intro x; rw [attends Q L _ _ t (L.ground t),current Q L]
lemma sailing_cost (t:ℂ) (p:t∈D): ‖sailing Q L t‖≤4:= by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num); intro x; exact from_voice _ _ (fun y=> by rw [attends Q L _ _ _ p,mul_right_comm]; exact norm_fare Q L _ _ t p) (by positivity)

lemma hol_sail : AnalyticOnNhd ℂ (sailing Q L) D:= by
  let V (x y:H): H.Op→L[ℂ]ℂ := (innerSL ℂ x).comp (ContinuousLinearMap.apply ℂ H y)
  refine Analysis.lift_weak {v| ∃ x y,v=V x y} (fun x y h=>?_) L.ticket (fun z p=>?_) ?_
  · ext1 w; exact ext_inner_left ℂ fun u=> h (V u w) ⟨u,w,rfl⟩
  · obtain ⟨r,b,h⟩:= nhds_basis_closedBall.mem_iff.mp (L.ticket.mem_nhds p); let d:=r/2; let c:=4/d
    have hb: z∈ ball z d := mem_ball_self (by unfold d; positivity)
    have he (u:ℂ)(e:u∈ ball z d) : closedBall u d⊆D:= by
      intro y a; apply h; rw [mem_closedBall]
      have hx:=mem_closedBall.mp a; have hv:= mem_ball.mp e; unfold d at *; linarith [dist_triangle y u z]
    have hD : ball z d⊆D:=fun y v=> he _ v (mem_closedBall_self (by unfold d; positivity))
    have hv (u:ℂ)(e:u∈ ball z d) (x y:H):‖M x y u-M x y z‖≤ c*dist u z * ‖x‖ * ‖y‖:=by
      have h' := (hol_m Q L x y)
      refine ((convex_ball z d).norm_image_sub_le_of_norm_deriv_le (fun y p=> (h' y (hD p)).differentiableAt) (fun i g=> CF.Floral.c_deriv h'.differentiableOn (r:=d) (by unfold d; positivity) (he i g) (fun w hw=> norm_fare Q L x y w hw)) hb e).trans_eq ?_
      rw [dist_eq_norm]; unfold c; ring
    refine ContinuousAt.continuousWithinAt (Metric.tendsto_nhds.mpr (fun ε v=> ?_))
    let hc: 0<c:= by unfold c d; positivity
    filter_upwards [ball_mem_nhds z (ε:=ε/c) (by positivity), isOpen_ball.mem_nhds hb] with i hi g
    let k:=c*dist i z
    have hk : ‖sailing Q L i - sailing Q L z‖ ≤ k := by
      apply ContinuousLinearMap.opNorm_le_bound _ (by unfold k; positivity)
      intro x; refine from_voice _ _ (fun y=> ?_) (by unfold k; positivity)
      rw [sub_apply,inner_sub_right, attends Q L _ _ _ p,attends Q L _ _ _ (hD g),mul_right_comm]; exact hv i g y x
    rw [dist_eq_norm]; exact hk.trans_lt (by unfold k; rw [mul_comm]; exact (lt_div_iff₀ hc).1 hi)
  rintro v ⟨x,y,rfl⟩; apply (hol_m Q L x y).differentiableOn.congr; intro y' h; exact attends Q L x y _ h
end Sail
end YM.ConePrice
