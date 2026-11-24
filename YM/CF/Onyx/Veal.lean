import YM.CF.Onyx.Pay
set_option autoImplicit false
noncomputable section
namespace YM.CF.Onyx
open Function Filter Metric Fir Lattice Laurent Next.Free Bloch Finset Lat Ember Jill Flare
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix Matrix.Norms.L2Operator Kronecker
attribute [local instance] opCStarAlgebra
variable {N:Side}{j:ℕ}{r R C:ℝ}{M:Male}{a:Axis}
lemma stern (H:1≤j)(p:0<r):∃ c b:ℝ,0<c∧0<b∧∀ N:Side,∀ (M:Male)(s:Offset N)(k:Site N),Even N.val→ let x:=glen s k
      (c*pinch N≤ ‖x‖→ r*(pinch N)^2<disk j M x)∧ (r*pinch N^2<disk j M x→ pinch N ≤ b*‖x‖) :=by
 obtain ⟨c,h,K⟩:= high_frost H (mul_pos (by norm_num : (0:ℝ)<2) p); obtain ⟨d,y,hd,e,t⟩:=Jill.zip H; let b:=Real.sqrt (y/r); have hg:0<b:=by unfold b; positivity
 refine ⟨c,b,h,hg,fun N M s k g=>?_⟩; intro x; have hr:Bound Real.pi x:=orb k s g; have hp:=pinch_pos N; constructor
 · intro ht; refine lt_of_lt_of_le ?_ ((le_max_left ..).trans_eq (K N M x hr ht)); nlinarith [show 0< pinch N^2 by positivity]
 intro ht; apply (sq_le_sq₀ hp.le (mul_nonneg hg.le (norm_nonneg _))).mp; have he:b^2=y/r:=Real.sq_sqrt (by positivity); rw [mul_pow,he, div_mul_eq_mul_div,le_div_iff₀ p,mul_comm]; exact ht.le.trans (t M x hr).2
structure FormU(s:Offset N)(d:ℕ)(M:Male)(r C:ℝ)(A:Site N→Peb):Prop where
  far :∀ k:Site N,r*pinch N^2 <disk d M (glen s k) → A k=dip d M (tmap (glen s k))
  near :∀ k:Site N,disk d M (glen s k) ≤r*pinch N^2 →‖A k‖≤ C/pinch N -- syntax
variable {s:Offset N}{A:Site N→Peb}(h:FormU s j M r C A)
def flow(s:Offset N)(d:ℕ)(M:Male)(y:ℝ)(A:Site N→Peb)(k:Site N):=damp y (disk d M (glen s k)) • A k
lemma ice_h (g:Even N.val)(k:Site N)(j)(M:Male)(s:Offset N):shell j M.val (tmap (glen s k))=(disk j M (glen s k):ℂ):=express _ _ _ (base_subset_realCube zone_pos (b_base (orb _ s g))) M.property
include h
lemma flow_b (H:1≤j)(p:0<r)(u:0<C)(g:Even N.val)(l:ℝ)(hy:0<l)(y:ℝ)(hz:0<y)(k:Site N)(hr:0<R)(hu:R*pinch N≤1)(hv:R*‖glen s k‖≤ l)(c:ℝ)(P:∀ p:Bin,Bound Real.pi p→ ‖tail j y M (tmap p)‖≤ c*‖p‖)(e:0<c): ‖flow s j M y A k‖≤ max (c*l) (2*r*C)/R:= by
 let F:=glen s k; have hp:=pinch_pos N
 by_cases w:r*pinch N^2 < disk j M F
 · rw [flow,h.far k w, ← ice_h g k]; apply (P F (orb _ s g)).trans; rw [le_div_iff₀ hr]; refine le_trans ?_ (le_max_left ..); rw [mul_assoc]; change R*‖F‖≤_ at hv; nlinarith [mul_le_mul_of_nonneg_left hv e.le] -- tune R comm
 have hx:=h.near k (le_of_not_gt w); have he: disk j M F≤r*pinch N^2:=le_of_not_gt w; have hK:0≤disk j M F:=norm_nonneg _; have hj:= ion y hz (disk j M F) (show _ from hK); rw [Complex.norm_real, Real.norm_of_nonneg hK] at hj
 refine (le_trans ?_ (show (2*r*C)/R ≤_ from div_le_div_of_nonneg_right (le_max_right ..) hr.le)); unfold flow; change ‖damp y (disk _ _ F) • A k‖≤_; rw [norm_smul]; exact (mul_le_mul (hj.trans (mul_le_mul_of_nonneg_left he (by norm_num))) hx (norm_nonneg _) ((norm_nonneg _).trans hj|>.trans (mul_le_mul_of_nonneg_left he (by norm_num)))).trans (by rw [show 2*(r*pinch N^2)*(C/pinch N)=2*r*C*pinch N by field_simp,le_div_iff₀ hr,mul_assoc (2*r*C)]; exact mul_le_of_le_one_right (by positivity) (by linarith))
omit h
variable (N)
def extent (d:ℤ) : ℝ:= (2*pinch N)* d
def march(a:Axis)(d:ℤ):Site N:= wrap N (d • step a)
variable {N}
lemma march_a(d:ℤ)(t:Offset N)(i:Site N)(a:Axis): peers (glen t i+beam a (extent N d)) (glen t (i+march N a d)):=by
 unfold glen; rw [add_right_comm]; apply peers.both; convert tap_c i (d • step a) using 3; rename_i j; by_cases h:j=a <;>simp [beam,step,h,extent]
 rfl
lemma march_t (d v:ℤ): extent N (d*v)=(d:ℝ)*extent N v:=by unfold extent; push_cast; ring
lemma within_d(g:Even N.val)(k:Site N)(a:Axis)(d:ℤ)(l:ℝ)(w:|extent N d|≤l): |‖glen s k‖-‖glen s (k+march N a d)‖| ≤ l:=((neigh (orb k s g) (orb _ s g) (march_a ..)).trans (beam_cost ..)).trans w
end YM.CF.Onyx
