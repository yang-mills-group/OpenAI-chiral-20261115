import YM.CF.BProof.Bracket

/-! eq:B-blend estimates on two smooth-frame faces. Taylor only on fixed dimensional arguments. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BProof.Chart
open Function Set Metric NormedSpace Filter
open scoped Matrix.Norms.Frobenius Topology ContDiff
variable {G : Gauge} (K:Chart G)
local notation "M" => G.mat
local notation "E" => G.lieExp
local notation "L" => G.colorMat
local notation "A" => G.colorScale

def bump :ℝ:=2*K.C+(K.C*G.colorScale)^2
lemma bump_pos : 0<K.bump:=by unfold bump; have := zero_lt_one.trans_le K.C_one; positivity
lemma two (x y : G.Color){r:ℝ} (hk:r≤K.size)(hx:‖x‖≤r)(hy:‖y‖≤r): ‖M (E x*E y)-1-L (x+y)‖≤ K.bump*r^2 := by
 let a:=M (E x)-1; let b:=M (E y)-1; let d:=r^2; have hp:0≤r:=(norm_nonneg x).trans hx; have ht:=G.colorScale_pos; have hu:=zero_lt_one.trans_le K.C_one
 have he (x:G.Color)(hx:‖x‖≤r): ‖M (E x)-1-L x‖≤K.C*d:= (K.linear x hx hk).trans ((mul_le_mul_of_nonneg_left hx (by positivity)).trans_eq (by unfold d; ring))
 rw [show M (E x*E y)-1-L (x+y)=(a-L x)+(b-L y)+ a*b by rw [map_add,Gauge.mat_mul]; unfold a b; noncomm_ring]; apply le_trans (norm_add_le ..)
 let u:=(K.C*A)*r; have hf:0≤u:=by unfold u; positivity
 apply le_trans (add_le_add ((norm_add_le ..).trans (add_le_add (he x hx) (he y hy))) ((norm_mul_le ..).trans (show ‖a‖*‖b‖≤u*u from mul_le_mul ((K.slope _ (hx.trans hk)).trans (by unfold u; gcongr)) ((K.slope _ (hy.trans hk)).trans (by unfold u; gcongr)) (norm_nonneg _) hf)))
 unfold bump u d; exact le_of_eq (by ring)
lemma quad (x y p q : G.Color){r:ℝ}(hk:r≤K.size)(hx:‖x‖≤r)(hy:‖y‖≤r)(hp:‖p‖≤r)(hq:‖q‖≤r):
    ‖M (E x*E y)-M (E p*E q)-L (x+y-(p+q))‖ ≤ (K.bump*r^2)*2:=by
 calc
   _ = ‖(M (E x*E y)-1-L (x+y))-(M (E p*E q)-1-L (p+q))‖:=by rw [map_sub]; congr 1; abel
   _ ≤ _:=by rw [mul_two]; exact (norm_sub_le ..).trans (add_le_add (K.two x y hk hx hy) (K.two p q hk hp hq))

section
variable {X : Type*} [NormedAddCommGroup X][NormedSpace ℝ X]
def lerp (s : ℝ) (f g : X) : X:= (1-s) • f+s • g
@[simp] lemma lerp_zero (f g:X):lerp 0 f g=f:=by simp [lerp]
@[simp] lemma lerp_one (f g:X):lerp 1 f g=g:=by simp [lerp]
lemma lerp_bound (s : ℝ) (f g:X){K:ℝ}(hf:‖f‖≤K)(hg:‖g‖≤K)(h : s∈ Icc 0 1):‖lerp s f g‖≤K:=by
 unfold lerp; apply (norm_add_le ..).trans; rw [norm_smul,norm_smul,Real.norm_of_nonneg h.1,Real.norm_of_nonneg (sub_nonneg.mpr h.2)]; linarith only [mul_le_mul_of_nonneg_left hf (sub_nonneg.mpr h.2),mul_le_mul_of_nonneg_left hg h.1]
@[simp] lemma lerp_add (s : ℝ) (x y a b:X): lerp s x y+lerp s a b=lerp s (x+a) (y+b):=by unfold lerp; rw [smul_add,smul_add]; abel
@[simp] lemma lerp_sub (s : ℝ) (x y a b:X): lerp s x y-lerp s a b=lerp s (x-a) (y-b):=by unfold lerp; rw [smul_sub,smul_sub]; abel
lemma lerp_distance (s t:ℝ)(x y:X)(r:ℝ)(hx:‖x‖≤r)(hy:‖y‖≤r):‖lerp s x y-lerp t x y‖≤|s-t| *(2*r):=by
 rw [show lerp s x y-lerp t x y=(s-t) • (y-x) from by unfold lerp; simp only [smul_sub,sub_smul,one_smul]; abel,norm_smul]; apply mul_le_mul_of_nonneg_left (α:=ℝ); exact (norm_sub_le ..).trans ((add_le_add hy hx).trans_eq (two_mul ..).symm); exact abs_nonneg _ -- tune
end

lemma smooth_lerp {s r w:ℝ} (u:s∈ Icc 0 1)(h:r ≤ K.size)
   (f g : Fin 4→G.Color)(hv:∀ i,‖f i‖ ≤ r)(hy:∀ i,‖g i‖≤r) (F : (Fin 4→ G.Color)→ G.El) (hf:∀ t,F t=E (t 0)* E (t 1))
   (D : (Fin 4→ G.Color)→ G.El) (hb:∀ t,D t=E (t 2)*E (t 3))
   (hf': cd G (F f) (D f)≤w)(hd':cd G (F g) (D g) ≤ w):
       let z(i):=lerp s (f i) (g i); cd G (F z) (D z) ≤ w+(4*K.bump/A)*r^2 := by
 intro z; let a (x:Fin 4→G.Color):= x 0+x 1-(x 2+x 3)
 let C:=K.bump*r^2*2; have hq (v : Fin 4→ G.Color)(h':∀ i, ‖v i‖≤r): ‖M (F v)-M (D v)-L (a v)‖≤ C:= by rw [hf,hb]; exact K.quad _ _ _ _ h (h' _) (h' _) (h' _) (h' _)
 have he(x:Fin 4→G.Color)(p:∀ i,‖x i‖≤r)(k:cd G (F x) (D x)≤w):‖L (a x)‖≤ C+w*A:= (norm_le_norm_sub_add _ (M (F x)-M (D x))).trans (add_le_add (by rw [norm_sub_rev]; exact hq x p) ((norm_le_scale ..).mp k))
 rw [norm_le_scale]; refine (norm_le_norm_sub_add _ (L (a z))).trans ((add_le_add (hq _ (fun i=> lerp_bound _ _ _ (hv i) (hy i) u)) (show ‖L (a z)‖≤ C+w*A from ?_)).trans_eq ?_)
 · rw [show a z=lerp s (a f) (a g) from by simp [a,z],lerp,map_add,map_smul,map_smul]; exact lerp_bound _ _ _ (he f hv hf') (he g hy hd') u
 have := G.colorScale_pos; unfold C; field_simp; ring
end YM.CF.BProof.Chart
