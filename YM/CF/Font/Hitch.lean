import YM.CF.Font.Rise
set_option autoImplicit false
noncomputable section
namespace YM.CF.Font
open Function Filter Metric Lattice Wilson Laurent Precision Tree Finset Exterior Extra Bloch Fock NormedSpace Lat Rush Cube Scroll SU Drapes Fir Peaks Dial Paige Brace Vault Tulip Tenant
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix MatrixOrder Kronecker Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
variable {L c f n:Side}{a b:ℝ}
def gear (x y:Single n):ℝ:= ↑(separation (place_x x) (place_x y))
abbrev PrizeX (n:Side):= Wind (More n)
def notx(m:ℕ)(x y:Single n)(z:Fin m→PrizeX n) := gear x y+∑ i, (dial (place_x x) (z i) : ℝ)
lemma size_q (x y:Single n):gear x y ≤ (More n).val:=by unfold gear; exact_mod_cast pdist_leN ..
lemma notx_zero (m:ℕ)(x y:Single n)(z:Fin m→ PrizeX n):0 ≤ notx m x y z:=by unfold notx gear; positivity
lemma skull(m:ℕ)(x y:Single n)(z:Fin m→ Ps (More n)):notx m x y (Sum.inl ∘ z)=gear x y+∑ i,(separation (place_x x) (z i).1:ℝ):= rfl
lemma hurt(G:Ratio c f)(x v: Single f)(y u: Single c): gear y u ≤ gear x v/spanV (ratio G)+1+dish G x y+dish G v u:=by
 let g:=ratio G; let X:=place_x x; let V:=place_x v; let Y:=place_x y; let U:=place_x u
 have he := ((separation_triangle Y (g.parent X) U).trans (Nat.add_le_add_left (separation_triangle (g.parent X) (g.parent V) U) (separation Y (g.parent X))))
 have hy : (separation (place_x y) (place_x u):ℝ) ≤ ↑(dish G x y)+(separation (g.parent X) (g.parent V):ℕ)+↑(dish G v u):= by unfold dish; exact_mod_cast le_trans he (le_of_eq (by rw [separation_comm Y (g.parent X),←add_assoc]))
 apply hy.trans; unfold gear; change _≤ _+1+_+_; linarith [hleft (g:=ratio G) X V] -- tune
lemma foot_p(G:Ratio c f){m:ℕ}(x v:Single f)(y u:Single c)(z:Fin m→Ps (More f))(t:Fin m→ Ps (More c)):
 let h:=ratio G
 notx m y u (Sum.inl ∘ t) ≤ notx m x v (Sum.inl ∘ z)/spanV h+(m+1:ℝ)+((m+1:ℝ)*dish G x y+dish G v u+∑ i, (separation (h.parent (z i).1) (t i).1:ℝ)):=by
 intro h
 have hx(i): (separation (place_x y) (t i).1:ℝ)≤ (separation (place_x x) (z i).1)/spanV h+1+dish G x y+(separation (h.parent (z i).1) (t i).1:ℝ):=by
    have hp:= hleft (g:=h) (place_x x) (z i).1; let A:=(h.parent (z i).1); let Y:=place_x y; let X:=h.parent (place_x x); have hh:= separation_triangle X A (t i).1
    have he: (separation Y (t i).1:ℝ)≤ (separation X Y:ℕ)+(separation X A:ℕ)+(separation A (t i).1:ℝ):=by -- casts colon bug coercion
        exact_mod_cast ((separation_triangle Y X _).trans (Nat.add_le_add_left hh _) |>.trans (le_of_eq (by rw [separation_comm Y X, add_assoc]))) -- tune
    apply he.trans; unfold dish h Y X A at *; push_cast ; linarith
 rw [skull,skull]; apply (add_le_add (hurt G x v y u) (sum_le_sum fun i (_:i∈univ)=> hx i)).trans_eq; simp only [sum_add_distrib,sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul, ← sum_div]; unfold h; ring
private lemma growth(a:ℝ){b:ℝ}(h:0<a)(e:b≤a/2){m R Q t:ℝ}(g:0≤m)(u:0≤R)(v:0≤Q)(z:0≤t):
 nick b (R+(m+1)+((m+1)*Q+t))≤ nick b R * (nick a (m+1)*taxH a*Real.exp (a*((m+1)*Q+t))):=by
 apply le_trans (nick_add (show 0≤R+(m+1) by positivity) (show 0≤(m+1)*Q+t by positivity))
 calc
   _ ≤ (nick b R * nick a (m+1))*(taxH a* Real.exp (a*((m+1)*Q+t))):= by refine mul_le_mul ((nick_add u (by linarith)).trans (mul_le_mul_of_nonneg_left (nick_rate (by linarith) (by linarith)) (nick_pos _ u|>.le))) (dentH h e (by positivity)) (nick_pos _ (by positivity)|>.le) ?_; exact mul_nonneg (nick_pos _ u|>.le) (nick_pos _ (by linarith)|>.le)
   _ = _:=by ring

def cashH(a:ℝ)(m:ℕ):=nick a ((m:ℝ)+1)*taxH a
lemma wages {m:ℕ}(G:Ratio c f)(x v:Single f)(y u:Single c)(z:Fin m→Ps (More f))(t:Fin m→ Ps (More c))(h:0<a)(hp:0≤b)(e:b≤a/2): let R:=ratio G
 nick b (notx m y u (Sum.inl ∘ t)) ≤ cashH a m*nick b (notx m x v (Sum.inl ∘ z))*bolt (((m:ℝ)+1)*a) G x y * bolt a G v u*∏ i,Faro a (R.parent (z i).1) (t i).1:=by
 intro R
 let s:=notx m x v (Sum.inl ∘ z); have hs:0≤s:=notx_zero ..; let L:=spanV R; let A:=∑ i:Fin m, (separation (R.parent (z i).1) (t i).1:ℝ); let Q:= (dish G x y:ℝ); let H:= (dish G v u:ℝ); have hA:0 ≤ A:= Finset.sum_nonneg fun _ _=> by positivity
 have he:=nick_inc hp (notx_zero ..) (foot_p G x v y u z t)
 apply he.trans; rw [add_assoc ((↑m+1:ℝ)* ↑(dish G x y))];
 apply le_trans (growth a h e (Nat.cast_nonneg m) (show 0≤ s/L from div_nonneg hs span_pos.le) (show 0≤Q from Nat.cast_nonneg _) (show 0≤ H+A from add_nonneg (Nat.cast_nonneg _) hA))
 have hr:s/L≤s:= div_le_self hs period_one
 have hm: nick b (s/L)≤ nick b s:=nick_inc hp (div_nonneg hs span_pos.le) hr
 have hX:0<taxH a:=Iteration.momentPrice_pos _ (half_pos h)
 refine (mul_le_mul_of_nonneg_right hm (show 0≤ cashH a m* Real.exp (a*(((m:ℝ)+1)*Q+(H+A))) from mul_nonneg (mul_nonneg (nick_pos _ (by positivity)|>.le) hX.le) (by positivity))).trans_eq ?_
 unfold cashH Faro bolt s A H Q R; rw [← Real.exp_sum, mul_add, mul_add, Finset.mul_sum]; rw [Real.exp_add,Real.exp_add]; ring_nf
end YM.CF.Font
