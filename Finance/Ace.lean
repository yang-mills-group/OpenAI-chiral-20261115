import Finance.Hold
set_option autoImplicit false
set_option maxHeartbeats 520000
noncomputable section
namespace ThinGauge
open Real Filter
open scoped Topology
abbrev boost (d:ℝ):=gain/(d^4)
variable {g0 Δ Cℓ A d r R ζ:ℝ}
-- ζ= μ, qCorset:$q.H use W ≤ d^5*r. derivative receipt errors prior s=$r
lemma soloKing (p:Open g0 Δ Cℓ A d)(u:0<r)(v:R≤2*r)(hv:r≤R)(k:ℝ)
    (z t:ℝ) (ha:‖z-k*ζ*r‖ ≤ (lowerCost g0 A)*d^5*r)(hb:‖t‖ ≤ lowerCost g0 A*d^5*r)
    (ht:d^4/4 ≤ k)(e:Real.exp (-1) ≤ |ζ|):
   let V:=R/z; let U:= -t/z
   z≠0 ∧ |V|≤ Bmain/(d^4) ∧ |U|≤ (spineK g0 A)*d ∧
     V*z=R ∧ U*z+t=0 ∧ (|V| *(yolk Δ Cℓ*d^4*r)≤ A*R/4) ∧ boost d*( |U| *(yolk Δ Cℓ*d^4*r) + (shell Δ Cℓ A)*d^5*r ) ≤ A*R/4 :=by
 intro V U
 have hd:0<d:=p.hm
 have hr:0<d^4:=pow_pos p.hm _
 have hs:0≤ yolk Δ Cℓ:=mul_nonneg (abs_nonneg _) (by linarith only [exp_pos 1])
 have hu:0≤ lowerCost g0 A:=mul_nonneg (abs_nonneg _) (by linarith only [exp_pos 1,p.asset])
 have hv':0≤ shell Δ Cℓ A:=mul_nonneg (abs_nonneg _) (by linarith only [p.asset])
 have hk:0 ≤k:= (by positivity :0 ≤d^4/4)|>.trans ht
 have hp:slope*d^4*r≤ |k*ζ*r|:=by unfold slope; rw [abs_mul,abs_of_pos u,abs_mul,abs_of_nonneg hk]; apply mul_le_mul_of_nonneg_right _ u.le; rw [div_mul_eq_mul_div, mul_comm (exp _),←div_mul_eq_mul_div]; exact mul_le_mul ht e (exp_pos _).le hk -- ring maybe
 have hs' : lowerCost g0 A *d^5*r ≤ (slope/2)*d^4*r:=by rw [pow_succ',←mul_assoc,mul_comm _ d]; exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right p.faith hr.le) u.le
 rw [Real.norm_eq_abs] at ha hb
 have hy: slope/2*d^4*r≤|z|:=by have he:= abs_sub_abs_le_abs_sub (k*ζ*r) z; rw [abs_sub_comm] at he; linarith only [hp,he,ha,hs']
 have hm:0<slope/2*d^4*r:= mul_pos (mul_pos (div_pos slope_live (by norm_num)) hr) u
 have hg:0 < |z|:= hm.trans_le hy; have hz:z≠0:=abs_pos.mp hg
 have hV:|V|≤ Bmain/d^4:=by unfold V; rw [abs_div,abs_of_pos (u.trans_le hv),div_le_iff₀ hg]; calc
    _ ≤ 2*r:=v
    _ = Bmain/d^4*(slope/2*d^4*r):=by field_simp [Bmain,hr.ne',slope_live.ne']; ring_nf --
    _ ≤ _:=mul_le_mul_of_nonneg_left hy (div_pos bm_pos hr).le
 have hU:|U|≤ spineK g0 A *d:=by
    unfold U; rw [abs_div,abs_neg, div_le_iff₀ hg]; refine hb.trans ((le_trans ?_ (mul_le_mul_of_nonneg_left hy (mul_nonneg (mul_nonneg bm_pos.le hu) p.hm.le))))
    unfold spineK Bmain; have : lowerCost g0 A * d^5 *r * 1 ≤ (lowerCost g0 A)* d^5*r * 2:=mul_le_mul_of_nonneg_left (by norm_num) (by positivity)
    rw [mul_one] at this; apply this.trans_eq; field_simp [slope_live.ne']; ring
 refine ⟨hz,hV,hU,(by unfold V; field_simp),(by unfold U; field_simp; ring),?_,?_⟩
 · calc
     _ ≤ Bmain/d^4* (yolk Δ Cℓ * d^4*r):= mul_le_mul_of_nonneg_right hV (by positivity)
     _ = Bmain*yolk Δ Cℓ*r := by field_simp [p.hm.ne']
     _ ≤ _:=by
       have ht:=mul_le_mul p.crown hv u.le (show 0≤A/4 from by linarith only [p.asset]); linarith
 have he:= mul_le_mul_of_nonneg_right hU (show 0 ≤ yolk Δ Cℓ*d^4*r from by positivity)
 calc
   _ ≤ boost d* ((spineK g0 A*d)*(yolk Δ Cℓ*d^4*r)+shell Δ Cℓ A*d^5*r):=mul_le_mul_of_nonneg_left (add_le_add_left he _) ((div_pos gain_pos hr).le)
   -- OOPS boost= gain/d^4 then times d gives d YES.
   _= d*(gain*(spineK g0 A*yolk Δ Cℓ+shell Δ Cℓ A))*r:=by unfold boost; field_simp [hr.ne']
   _ ≤ _:=by have he:=mul_le_mul p.dut hv u.le (show 0≤A/4 from by linarith only [p.asset]); linarith
end ThinGauge
