import YM.CF.Haro.Curb
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
variable{n:Side}{a b c' C K R:ℝ}
private lemma node_l:Injective (@node n):= fun x y h => (assembly n).embed_injective (add_right_cancel (show _+(1:Site (More n))=_+_ from h))
open Push.Uniform (Decay countCost)
abbrev lurch(a:ℝ):ℝ:=Push.Uniform.countCost a*(Fintype.card (SpinIdx×Slot):ℕ)
section
variable (p:0<a)
include p
lemma yut (A:Site (More c)→ Site (More f))(h:Injective A)(i:Site (More f)): ∑ y:Single c,Decay a i (A (α_o c y))≤ lurch a:=by
 rw [←Equiv.sum_comp (Equiv.prodAssoc (Site c) SpinIdx Slot).symm]; rw [Fintype.sum_prod_type]; change ∑ j:Site c,(∑ y:SpinIdx × Slot, Decay a i (A (node j)))≤_
 have hp:Injective fun j:Site c=> A (node j):=h.comp node_l
 let S:= fun j:Site c=> A (node j); simp_rw [sum_const,card_univ,nsmul_eq_mul,←Finset.mul_sum]; unfold lurch; rw [mul_comm (countCost a)]; apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _); rw [← Finset.sum_image (g:=S) (f:=Decay a i) (fun i _ j _ h=>hp h)]; exact (sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun j _ _=> (Push.Uniform.decay_pos ..).le)).trans (Push.Uniform.decay_count p _)
lemma coin_l (x:Single f) : ∑ y:Single c,inkP G (a:=a) x y≤ lurch a:= yut p (ratio G).embed (ratio G).embed_injective _
lemma coin_r (x:Single c) : ∑ y:Single f,inkP G (a:=a) y x≤ lurch a:=by
 let A:=(ratio G).embed (α_o c x); apply le_trans _ (yut (c:=f) p id (fun _ _ e=>e) A); exact sum_le_sum fun j _=> (Push.Uniform.decay_comm a (α_o f j) A).le
end
lemma fuel_p(x y:Single c)(i j:Single f): perk m x y ≤ Tap.streak G m i x * (2:ℝ)^m *perk m i j* Tap.streak G m j y:=by
 let w(i:Single f):= (ratio G).parent (α_o f i); let a:ℝ:=dish G i x; let b:ℝ:=separation (place_x i) (place_x j); let d:ℝ:= dish G j y; change _≤ (1+a)^m*_*(1+b)^m*(1+d)^m; simp_rw [← mul_pow]; unfold perk
 have he := show separation (place_x x) (place_x y) ≤ dish G i x+ separation (place_x i) (place_x j)+1+dish G j y from (separation_triangle (place_x x) (w i) _).trans (by
    rw [separation_comm (place_x x) _]; have hv:=separation_triangle (w i) (w j) (place_x y); have hk: separation (w i) (w j)≤ separation (place_x i) (place_x j)+1:= Work.E04.parent_separation ..; change dish G i x+ _≤ _; change _ ≤ _+dish G j y at hv; omega)
 have hq:(separation (place_x x) (place_x y):ℝ)≤ a+b+1+d:=by unfold a b d; exact_mod_cast he
 have ha:0≤a:=Nat.cast_nonneg _; have hb:0≤b:=Nat.cast_nonneg _; have hd:0≤d:=Nat.cast_nonneg _
 apply pow_le_pow_left₀ (by positivity); nlinarith [mul_nonneg ha hb,mul_nonneg hb hd, mul_nonneg ha hd, mul_nonneg (mul_nonneg ha hd) hb]
variable (F:Op (Single f))(g:∀ x:Single f,paidX (perk m x) (fun y=>F x y)≤ K)
include g
lemma leaven(A B: Matrix (Single f) (Single c) ℂ)(hA:∀ x:Single c,∑ y:Single f, Tap.streak G m y x*‖A y x‖≤ b)(hB:∀ x:Single f,∑ y:Single c, Tap.streak G m x y*‖B x y‖≤ R)(x:Single c)(v:0 ≤ R)(h:0 ≤ K): paidX (perk m x) (fun y=>(Aᴴ*F*B) x y)≤ b*((2:ℝ)^m*(K*R)):=by
 unfold paidX; rw [Matrix.mul_assoc]; let q:= Tap.streak G m; let t:ℝ:=(2:ℝ)^m; let X(i:Single f):=q i x*‖A i x‖; let a (i j:Single f):=perk m i j*‖F i j‖; let Y(i:Single f)(y):= q i y*‖B i y‖
 have ht:0 ≤ t:=by unfold t; positivity
 have hx(i):0≤X i:=mul_nonneg (Tap.streak_pos ..) (norm_nonneg _); have hy(i j):0≤ a i j:=by unfold a perk; positivity
 simp only [Matrix.mul_apply,mul_sum]; calc
    _ ≤ ∑ i:Single f,X i*(t* (∑ j:Single f,a i j * ∑ y:Single c, Y j y)):=by
       simp_rw [Finset.mul_sum]; -- tune order
       let S (i j:Single f)(y:Single c):=X i*(t*(a i j*Y j y))
       change _≤ ∑ i: Single f,∑ j:Single f,∑ y,S i j y
       simp_rw [sum_comm (s:=(univ:Finset (Single f))) (t:=(univ: Finset (Single c)))]; apply sum_le_sum; intro y _; have hv:0 ≤ perk m x y:=by unfold perk; positivity
       refine (mul_le_mul_of_nonneg_left (norm_sum_le ..) hv).trans ?_; rw [mul_sum]; apply sum_le_sum; intro i _; refine (mul_le_mul_of_nonneg_left (norm_sum_le ..) hv).trans ?_; rw [mul_sum]; apply sum_le_sum; intro j _; rw [norm_mul,norm_mul,Matrix.conjTranspose_apply,norm_star]; refine (mul_le_mul_of_nonneg_right (fuel_p m G x y i j) (mul_nonneg (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _)))).trans_eq ?_; unfold S Y X q t a; ring
    _ ≤ _:=by
       refine (sum_le_sum (g:=fun i:Single f=> X i*(t*(K*R))) (fun i _=> mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ?_ ht) (hx i))).trans ?_
       · refine (sum_le_sum (fun j (_:j∈(univ:Finset _))=>mul_le_mul_of_nonneg_left (hB j) (hy i j))).trans ?_; rw [←sum_mul]; exact mul_le_mul_of_nonneg_right (g i) v
       rw [←Finset.sum_mul]; exact mul_le_mul_of_nonneg_right (hA x) (mul_nonneg ht (mul_nonneg h v))
variable {l k n':ℕ}(X: ∀ i:TailB,Support (More f)→Toll (Iota G))(p:∀ i D, Suite (badge _) (pinH G t true) (pinH G t false) D (X i D) (W i D))(V':∀ i, incline (hall G t) n' R (fun _=> C) b (X i)) (u':0 ≤ R)
variable (hb:3*a≤b)(hp:0<a)(he:a ≤ 1)(hx:0 ≤ K)(hk:0 ≤ C)
abbrev mintY(l:ℕ):= frost m (a:=a) l * lurch a*C
abbrev cops(j:Finset (Support (More f)))(t:Bool):Matrix (Single f) (Single c) ℂ:= ∑ i∈ j,openQ G Y W i t
abbrev saltW(i j:Finset (Support (More f))): Op (Single c):= (cops G Y W i true)ᴴ * F * cops G Y W j false
include ho g p V' u' hb hp he hx hk
lemma prowl (i j:Finset (Support (More f)))(hi:∀ a∈ i,l ≤ a.card)(hj:∀ a∈ j,k ≤ a.card)(x:Single c): paidX (perk m x) (fun y=> saltW G Y W F i j x y)≤ mintY m (a:=a) (C:=C) l * ((2:ℝ)^m*(K*mintY m (a:=a) (C:=C) k)):=by
 apply leaven m G F g _ _ _ _ x _ hx
 · intro x; apply (sum_le_sum (fun y (_: y∈(univ:Finset (Single f)))=> reachV m G ho Y W X p V' u' hb hp he i true y x l hi)).trans; unfold mintY; rw [←sum_mul,← Finset.mul_sum]; exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (coin_r G hp x) (by unfold frost polV; positivity)) hk
 · intro y; apply (sum_le_sum (fun z (_:z∈(univ:Finset (Single c)))=> reachV m G ho Y W X p V' u' hb hp he j false y z k hj)).trans; unfold mintY; rw [←sum_mul,←Finset.mul_sum]; exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (coin_l G hp y) (by unfold frost polV; positivity)) hk
 unfold mintY frost lurch polV; have h':=Push.Uniform.count_pos hp; positivity
lemma windy (J:Finset (Support (More f)))(h:∀ a:Support (More f), a∉J → l ≤ a.card)(x:Single c): paidX (perk m x) (fun y=> pulled G Y W F J x y-pulled G Y W F univ x y) ≤ 2*mintY m (a:=a) (C:=C) l*((2:ℝ)^m*(K*mintY m (a:=a) (C:=C) 0)):=by
 let U:= univ \ J; have hz (A:Finset (Support (More f))) :pulled G Y W F A= saltW G Y W F A A:=by unfold saltW cops pulled; simp only [Matrix.conjTranspose_sum,Matrix.mul_sum, Matrix.sum_mul]; rw [sum_comm]
 have hv(z):cops G Y W univ z= cops G Y W U z + cops G Y W J z:= by unfold cops; rw [Finset.sum_sdiff (subset_univ _)]
 let X':=saltW G Y W F U J; let Y':=saltW G Y W F univ U
 have hp':pulled G Y W F J-pulled G Y W F univ= - (X'+Y'):=by simp_rw [hz]; unfold X' Y' saltW; simp_rw [hv, Matrix.conjTranspose_add, Matrix.add_mul,Matrix.mul_add]; abel
 let K₀(y):=X' x y; let L(y):=Y' x y
 rw [show (fun y:Single c=> pulled G Y W F J x y-pulled G Y W F univ x y)=-(K₀+L) from funext fun y=> Matrix.ext_iff.mpr hp' x y,Tap.p_negative]
 have hv'(i)(g:i∈ U):l ≤ i.card:= h i (mem_sdiff.mp g).2
 refine le_trans ((p_sum (H:=perk m x) (fun i=>by unfold perk; positivity) _ _).trans (add_le_add (prowl m G ho Y W F g X p V' u' hb hp he hx hk U J hv' (fun _ _=> Nat.zero_le _) x) (prowl m G ho Y W F g X p V' u' hb hp he hx hk univ U (fun _ _=> Nat.zero_le _) hv' x))) ?_; exact le_of_eq (by ring)
end YM.CF.Haro
