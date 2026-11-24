import YM.CF.BProof.Bracket
import YM.CF.BProof.Grid.Lerp

/-! Taylor estimates for products relative to a reference magnetic link. Chord errors
keep physical normalization. Keep test margin pays separately from expansion. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BProof.Charge
open Function Filter NormedSpace MeasureTheory Gauge
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius InnerProductSpace
attribute [local instance] Gauge.frobInner
variable {G:Gauge}
local notation "E"=> G.El
local notation "M"=> G.mat
local notation "C"=> G.colorMat
local notation "s"=> G.colorScale
variable {a b u v:G.El}
variable (K:Chart G)

def Aff (G:Gauge)(a b:G.El)(x:G.Color)(p:ℝ) := ‖G.mat b-G.mat a-G.colorMat x‖≤G.colorScale*p
variable {m r R p q:ℝ}{x y:G.Color}
lemma Aff.le (u:Aff G a b x p)(g':p≤q): Aff G a b x q:= u.trans (mul_le_mul_of_nonneg_left g' G.colorScale_pos.le) -- name macro g
lemma Aff.inv (h:Aff G a b x p): Aff G a⁻¹ b⁻¹ (-x) p:= by
 unfold Aff; simp only [mat_inv,map_neg]; rw [← G.colorMat_skew x, ← star_sub, ← star_sub,norm_star]; exact h
lemma expense (h:Aff G a b x p) : |cd G a b - ‖x‖| ≤ p:=by
 unfold Aff at h; have ht:=abs_norm_sub_norm_le (M b-M a) (C x); rw [G.colorMat_norm x,show ‖M b-M a‖ =s*cd G a b from by have := G.colorScale_pos; rw [cd_symm,cd_norm]; field_simp] at ht; rw [←mul_sub,abs_mul,abs_of_nonneg G.colorScale_pos.le] at ht; exact le_of_mul_le_mul_left (ht.trans h) G.colorScale_pos -- tune
lemma Aff.product (h:Aff G a b x p)(hu:Aff G u v y q)(hp:G.chord a≤r)(hq:G.chord v≤R)(hx:‖x‖≤m){m':ℝ}(hy:‖y‖≤m'): Aff G (a*u) (b*v) (x+y) (p+q+s*(r*m'+R*m)):=by
 let A:=M a; let B:=M b; let U:=M u; let V:=M v; have hs:=G.colorScale_pos
 unfold Aff; rw [mat_mul,mat_mul,map_add]
 rw [show M b*M v-M a*M u-(C x+C y)=(M b-M a-C x)*M v+C x*(M v-1)+ M a*(M v-M u-C y)+(M a-1)*C y by noncomm_ring]
 have he (w:E){e:ℝ}(h:G.chord w≤e) : ‖M w-1‖≤s*e:=((div_le_iff₀ hs).1 h).trans_eq (mul_comm ..)
 apply (norm_add_le ..).trans; apply le_trans (add_le_add ((norm_add_le ..).trans (add_le_add (norm_add_le ..) le_rfl)) le_rfl)
 simp only [frob_mul_eq _ _ (G.mat_mul_star _),mul_frob_eq _ _ (G.mat_star_mul _)]
 have hg: 0≤s*r:=le_trans (norm_nonneg _) (he a hp); have hz:0≤s*m:=mul_nonneg hs.le ((norm_nonneg _).trans hx)
 refine le_trans (add_le_add (add_le_add (add_le_add h ((norm_mul_le ..).trans ?_)) hu) ((norm_mul_le ..).trans ?_)) (Eq.le (by ring : s*p+(s*m)*(s*R)+s*q+(s*r)*(s*m')=_)) -- tune ring
 · rw [G.colorMat_norm]; exact mul_le_mul (mul_le_mul_of_nonneg_left hx hs.le) (he v hq) (norm_nonneg _) hz
 apply mul_le_mul (he a hp); rw [G.colorMat_norm]; gcongr; exact norm_nonneg _; exact hg -- tune semis
lemma affine_mul (hx:‖x‖≤r)(hr:r≤K.size) (u:G.El)(g:G.chord u≤R) : Aff G u (u*G.lieExp x) x ((K.C/s*r+s*R)*r) := by
 have hs:=G.colorScale_pos; have hk:=K.C_one; have hp:0≤r:=(norm_nonneg _).trans hx
 let X:=C x; let A:=M u; unfold Aff; rw [mat_mul]
 rw [show M u*M (G.lieExp x)-M u-C x = M u*(M (G.lieExp x)-1-C x)+(M u-1)*C x by noncomm_ring]; apply (norm_add_le ..).trans; rw [mul_frob_eq _ _ (G.mat_star_mul u)]
 have ht: ‖M u-1‖≤ R*s:=(div_le_iff₀ hs).1 g
 refine le_trans (add_le_add (le_trans (K.linear x hx hr) (mul_le_mul_of_nonneg_left hx (by positivity))) ((norm_mul_le ..).trans (mul_le_mul ht (show ‖C x‖≤ s*r from (colorMat_norm G x).trans_le (by gcongr)) (norm_nonneg _) ((norm_nonneg _).trans ht)))) (le_of_eq ?_); field_simp
lemma Aff.noise (h:Aff G a b x p)(hx:cd G b v≤r): Aff G a v x (p+r):= by
 unfold Aff; apply le_trans (norm_le_norm_sub_add _ (M b-M a-C x)); simp only [sub_sub_sub_cancel_right]
 have hh:‖M v-M b‖≤r*s:=(norm_le_scale G).1 ((cd_symm G v b).trans_le hx); exact (add_le_add hh h).trans_eq (by ring)
lemma Aff.core (h:Aff G 1 u x p): ‖G.curvature u-x‖≤p:=by
 let z:=M u-1; let P:= G.projectColor; have e: G.curvature u-x=P ((1/2:ℝ) • ((z-C x)-star (z-C x))):=by
   nth_rw 1 [←project_colorMat G x]; unfold curvature z P; rw [mat_inv,← map_sub]; congr 1; simp only [star_sub,G.colorMat_skew,star_one]; module -- tune
 rw [e]; apply (G.project_norm _).trans; rw [div_le_iff₀ G.colorScale_pos,norm_smul,Real.norm_eq_abs,abs_of_nonneg (by norm_num : 0≤(1/2:ℝ)),mul_comm p]; apply le_trans (mul_le_mul_of_nonneg_left (norm_sub_le ..) (by norm_num)); rw [norm_star]; change ‖z-C x‖≤_ at h; linarith
lemma adj_cost {x:G.Color}{u:E}{r l:ℝ}(p:G.chord u≤r)(h:‖x‖≤l): ‖G.adjoint u x-x‖≤2*r*(s*l):=by
 let A:=M u; let X:=C x; apply le_of_mul_le_mul_left (a:=s) ?_ G.colorScale_pos
 rw [← colorMat_norm,map_sub,G.mat_adjoint]; unfold Gauge.conjugate; rw [show M u*C x*star (M u)-C x=(M u-1)*C x*star (M u) + C x* (star (M u)-1) by noncomm_ring]; apply (norm_add_le ..).trans; have ht:‖M u-1‖≤ r*s:=(div_le_iff₀ G.colorScale_pos).1 p; have hz : ‖C x‖≤ s*l:= (colorMat_norm ..).trans_le (mul_le_mul_of_nonneg_left h G.colorScale_pos.le); rw [frob_mul_eq _ _ (show star (M u)*star (star (M u))=1 from by simp), ← star_one (R:=G.Mat), ← star_sub] -- star_one rewrites wrong
 have he:=G.colorScale_pos; rw [star_one]; apply le_trans (add_le_add (norm_mul_le ..) (norm_mul_le ..)); rw [norm_star]; have hr:0 ≤ r:= (G.chord_nonneg _).trans p; have hl:0≤l:=(norm_nonneg _).trans h; refine le_trans (add_le_add (by gcongr) (by gcongr)) (Eq.le (by ring : (r*s)*(s*l)+(s*l)*(r*s)=_)) -- tune
end YM.CF.BProof.Charge
