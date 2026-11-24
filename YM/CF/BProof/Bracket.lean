import YM.CF.BProof.Chart

/-! Lie approximation (with uniform norm prices). -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BProof
open Filter Function MeasureTheory
open scoped Matrix.Norms.Frobenius Topology ContDiff
variable {G : Gauge}

namespace Chart
local notation "E" => G.lieExp
local notation "M" => G.mat
local notation "L" => G.colorMat
variable (K : Chart G)

lemma linear (x : G.Color) {r : ℝ} (hx : ‖x‖≤r) (h : r≤K.size) : ‖M (E x)-1-L x‖ ≤ K.C*r*‖x‖ := by
 simpa only [Gauge.mat_lieExp_zero,Gauge.mat_one,sub_zero] using K.error x 0 h hx (by simpa using (norm_nonneg _).trans hx)
lemma slope (x : G.Color) (hx : ‖x‖≤K.size) : ‖M (E x)-1‖≤ (K.C*G.colorScale)*‖x‖ := by
 have hp:= K.step x hx; unfold Gauge.chord at hp
 have he := (div_le_iff₀ G.colorScale_pos).mp hp; exact he.trans_eq (_root_.mul_right_comm ..)

lemma bracket_cost : ∃ C : ℝ,0<C ∧ ∀ (r : ℝ) (x y : G.Color),
    r≤K.size → ‖x‖≤r → ‖y‖≤r →
    ‖M (E x * E y*(E x)⁻¹*(E y)⁻¹)-1-L (G.ad x y)‖ ≤ C*r^3 := by
 let s:=G.colorScale; let k:=K.C * s; have hs:0<s:=G.colorScale_pos; have hz:=zero_lt_one.trans_le K.C_one
 have hv:0<k:=mul_pos hz hs
 let C:=(s+k)*K.C; have hc:0<C:=by dsimp only [C]; positivity
 refine ⟨2*C+4*s^2*k,by positivity,fun r x y hh hx hy=>?_⟩
 have hr:0≤r:=(norm_nonneg _).trans hx
 let a:= E x; let b:= E y; let A (x:G.Color) := M (E x)-1; let X:=L x; let Y:=L y
 have ha (x:G.Color)(hx:‖x‖≤r): ‖A x‖≤k*r := (K.slope x (hx.trans hh)).trans (mul_le_mul_of_nonneg_left hx hv.le)
 have hl (x:G.Color)(hx:‖x‖≤r): ‖L x‖ ≤ s*r:= (G.colorMat_norm x).trans_le (mul_le_mul_of_nonneg_left hx hs.le)
 have hp (x:G.Color)(hx:‖x‖≤r): ‖A x-L x‖≤K.C*r*r:=(K.linear x hx hh).trans (mul_le_mul_of_nonneg_left hx (mul_nonneg hz.le hr))
 have ht (x y:G.Color)(hx:‖x‖≤r)(hy:‖y‖≤r): ‖A x*A y-L x*L y‖ ≤ C*r^3:=by
   rw [show A x*A y-L x*L y=(A x-L x)*A y+ L x*(A y-L y) by noncomm_ring]
   apply (norm_add_le ..).trans; refine le_trans (add_le_add (le_trans (norm_mul_le ..) (mul_le_mul (hp _ hx) (ha _ hy) (norm_nonneg _) (le_trans (norm_nonneg _) (hp _ hx)))) (le_trans (norm_mul_le ..) (mul_le_mul (hl _ hx) (hp _ hy) (norm_nonneg _) (by positivity)))) (le_of_eq ?_)
   unfold C; ring
 let w:= (b*a)⁻¹; change ‖M _ - 1 - L _‖ ≤ _ -- wu
 have e : M w -1=M ((b*a)⁻¹)-1:=rfl
 have hm : ‖M w -1‖ ≤ 2*k*r:=by
   unfold w; rw [Gauge.mat_inv, ← star_one (R:=G.Mat), ← star_sub,norm_star,Gauge.mat_mul]
   rw [show M b*M a-1=M b*(M a-1)+(M b-1) by rw [_root_.mul_sub,mul_one]; abel]
   apply (norm_add_le ..).trans
   rw [Gauge.mul_frob_eq _ _ (G.mat_star_mul b)]
   exact (add_le_add (ha x hx) (ha y hy)).trans_eq (by ring)
 let B:=X*Y-Y*X
 have hb : ‖B‖≤s*r*(s*r)*2:=by
   apply (norm_sub_le ..).trans; apply (add_le_add (norm_mul_le ..) (norm_mul_le ..)).trans
   have ul:= hl x hx; have ur:= hl y hy
   dsimp only [X,Y]
   rw [mul_comm ‖L y‖,mul_two]; gcongr
 rw [show E x * E y*(E x)⁻¹*(E y)⁻¹=a*b*w by unfold w a b; group,G.colorMat_ad]
 change ‖M (a*b*w)-1-B‖≤_
 rw [show M (a*b*w)-1-B=((A x*A y-X*Y) - (A y*A x-Y*X))*M w + B*(M w-1) by
       have he : M b*M a*M w=1 := by rw [← G.mat_mul,← G.mat_mul]; unfold w; simp
       unfold A B
       change M (a*b*w)-1-(X*Y-Y*X)=((_)-_)*M w+(X*Y-Y*X)*_
       simp only [Gauge.mat_mul]; unfold a b at *; linear_combination (norm:=noncomm_ring) he
       -- tune
       ]
 apply (norm_add_le ..).trans; rw [Gauge.frob_mul_eq _ _ (G.mat_mul_star w)]
 refine le_trans (add_le_add ((norm_sub_le ..).trans (add_le_add (ht x y hx hy) (ht y x hy hx))) ((norm_mul_le ..).trans (mul_le_mul hb hm (norm_nonneg _) (by positivity)))) (le_of_eq ?_); ring
end Chart
end YM.CF.BProof
