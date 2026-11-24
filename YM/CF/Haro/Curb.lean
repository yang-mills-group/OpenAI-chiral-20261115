import YM.CF.Haro.Chord
set_option autoImplicit false
set_option maxHeartbeats 500000
set_option synthInstance.maxSize 24000
noncomputable section
namespace YM.CF.Haro
open Function Filter Metric Fir Lattice Laurent Next.Free Bloch Finset Lat Stationary Rush Cube Scroll SU Drapes Fir Peaks Dial Paige Brace Vault Fock Tulip Font Spire Nacre Ember Pec
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix Matrix.Norms.L2Operator Kronecker MatrixOrder Classical
attribute [local instance] opCStarAlgebra
open Tap Hake Urn Yaw Levier Proa Rill
variable {c f:Side}(j m:ℕ)(e:Even j)(h:2 ≤ j)
variable (G:Ratio c f)(ho:Odd G.count.val)
open Branch Laic
variable {t:ℝ}(Y: cro G t)(W: Meter TailB G t)(V: Meter Grave G t)
-- real tail matrix, moment estimate
variable {u b a C R:ℝ}{l n:ℕ} (X: ∀ i:TailB,(Support (More f))→Toll (Iota G))(p:∀ i D, Suite (badge _) (pinH G t true) (pinH G t false) D (X i D) (W i D))(v:∀ i, incline (hall G t) n R (fun _=> C) b (X i)) (u':0 ≤ R)
include p
abbrev α_o (d:Side)(x:Single d):=node x.1.1
abbrev pip(i:Single f)(y:Single c):= separation (α_o f i) ((ratio G).embed (α_o c y))
omit p
lemma smell(i y):dish G i y ≤ pip G i y+1:=by unfold dish pip α_o; have ht:=Work.E04.parent_separation (ratio G) (place_x i) ((ratio G).embed (place_x y)); rw [Ratio.embed_parent] at ht; exact ht
include ho p
lemma heatP (i:TailB)(D:(Support (More f)))(x:Single f)(y: Single c)(u:X i D ((switchG G).symm x) (patchQ G y)≠0): Grove (Tenant.terr _) D∧α_o f x∈D∧ (ratio G).embed (α_o c y)∈D:=by
 obtain ⟨g,z,f⟩:= ((p i D).expo ..).triggered u; change lookM G _∈D at f; rw [trK G y ho] at f; refine ⟨g,?_,f⟩; change node ((switchG G _).1.1)∈ D at z; rw [Equiv.apply_symm_apply] at z; exact z
abbrev polV(a:ℝ):=((a/(m+1:ℝ))⁻¹)^m
variable (hb:3*a≤b)(hp:0<a)(he:a ≤ 1)
open Push.Uniform (Decay)
def inkP (x:Single f)(y:Single c):ℝ:= Push.Uniform.Decay a (α_o f x) ((ratio G).embed (α_o c y))
abbrev frost(l:ℕ):=Real.exp (-(l:ℝ)*a)*(Real.exp a * polV m a)
include hb hp he v u'
lemma reachV (J:Finset (Support (More f)))(t:Bool)(x:Single f)(y:Single c)(l:ℕ)(h:∀ i∈J,l ≤ i.card):
 Tap.streak G m x y* ‖(∑ i∈J,openQ G Y W i t) x y‖ ≤ frost m (a:=a) l * inkP G (a:=a) x y*C:=by
 let z: TailB:= (true,t); let i:=(switchG G).symm x; let j:=patchQ G y
 let A(D:(Support (More f))):= X z D i j; let K:= frost m (a:=a) l * inkP G (a:=a) x y
 have hk:0≤K:= by unfold K frost polV inkP Decay; positivity
 have hv:=v z i; have hh(j'): 1≤(1+R*separation (lookM G i) (lookM G j'):ℝ)^n:= one_le_pow₀ (le_add_of_nonneg_right (by positivity)); have ht(j'):0≤ saleM b (X z) i j':= sale_nn (fun i=> (p z i).nonn) ..
 have hf:∑ D∈ J, Branch.rent b D*A D≤ C:=by
    apply le_trans (sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun i _ _=>mul_nonneg (rent_pos ..).le ((p z i).nonn ..))) _; refine le_trans (b:=(1+R*separation (lookM G i) (lookM G j):ℝ)^n*saleM b (X z) i j) (le_mul_of_one_le_left (ht _) (hh j)) ((Finset.single_le_sum (fun j _=> mul_nonneg (zero_le_one.trans (hh j)) (ht j)) (mem_univ _)).trans hv)
 rw [Matrix.sum_apply]
 refine (mul_le_mul_of_nonneg_left (norm_sum_le ..) (Tap.streak_pos ..)).trans (le_trans ?_ (mul_le_mul_of_nonneg_left hf hk)); rw [Finset.mul_sum,Finset.mul_sum]; apply sum_le_sum; intro D hd
 refine (mul_le_mul_of_nonneg_left (((p z D).expo i j).bounded Y) (Tap.streak_pos G m x y)).trans ?_; by_cases q:A D=0
 · change _*A D≤_; simp [q]
 rw [←mul_assoc]; change _* A D ≤ _; apply mul_le_mul_of_nonneg_right _ ((p z D).nonn i j); let B:ℝ := D.card; have hB:0≤B:=by positivity
 obtain ⟨g,p1,p2⟩:= heatP G ho W X p z D x y q
 have hz : (pip G x y:ℝ) ≤ B:=by unfold B; exact_mod_cast (g.lim _ p1 _ p2 |>.le : separation _ _ ≤ D.card)
 have hu:(dish G x y:ℝ) ≤ B+1:= by have he' : (dish G x y:ℝ)≤pip G x y+1:=(Nat.cast_le.mpr (smell G x y)).trans (by simp); linarith
 apply (alpine hp he m (↑(dish G x y)) (Nat.cast_nonneg _)).trans
 unfold frost polV inkP Decay Branch.rent
 let u:=polV m a; let Y:=inkP G (a:=a) x y; let V:ℝ:=pip G x y
 change u*Real.exp (a*dish G x y) ≤ (Real.exp _*(Real.exp _*u))*Real.exp (-a*V)*Real.exp (b*B) -- tune
 calc
    _ ≤ u*(Real.exp (-(l:ℝ)*a)*Real.exp a*Real.exp (-a*V)*Real.exp (b*B)) :=by
       simp_rw [← Real.exp_add]; have hy:(l:ℝ) ≤ B:= Nat.cast_le.mpr (h D hd); refine mul_le_mul_of_nonneg_left (Real.exp_monotone ?_) (by unfold u polV; positivity); change V ≤ B at hz; nlinarith only [mul_le_mul_of_nonneg_left hz hp.le,mul_le_mul_of_nonneg_left hu hp.le, mul_le_mul_of_nonneg_right hy hp.le, mul_le_mul_of_nonneg_right hb hB]
    _ = _:=by ring
end YM.CF.Haro
