import YM.CF.Font.Sale
set_option autoImplicit false
noncomputable section
namespace YM.CF.Font
open Function Filter Metric Lattice Wilson Laurent RG Precision Tree Finset Exterior Extra Extra.Iteration Bloch
open scoped Topology ContDiff BigOperators InnerProductSpace
variable {L f n c:Side}{g:Ratio c f}{A a b:ℝ}
def circle(x:Site n)(u v: Ps n):ℝ:= ↑(separation x u.1)+ ↑(separation x v.1)
def checkV(b:ℝ)(x:Site n)(K:Ps n→Ps n→ℝ):ℝ :=∑ u,∑ v, nick b (circle x u v)*‖K u v‖
lemma rot0(x:Site n)(u v: Ps n):0≤circle x u v:=by unfold circle; positivity
lemma flowing {A B:Ps n→Ps n→ℝ}(b:ℝ)(x:Site n):checkV b x (fun i j=>A i j+B i j)≤ checkV b x A+checkV b x B:=by unfold checkV; rw [← sum_add_distrib]; refine sum_le_sum ?_; intro i _; rw [← sum_add_distrib]; exact sum_le_sum fun j _=> (mul_le_mul_of_nonneg_left (norm_add_le ..) (nick_pos b (rot0 ..)|>.le)).trans_eq (mul_add ..)
lemma leaving {A B: Ps n→Ps n→ℝ}(b:ℝ)(x:Site n):checkV b x (fun i j=>A i j-B i j)≤ checkV b x A+checkV b x B:=by simpa only [checkV,norm_neg,sub_eq_add_neg] using flowing (A:=A) (B:=fun i j=>-(B i j)) b x
lemma survey(x y z:Site c)(X Y: Ps c → ℝ){V R s:ℝ}(hs:0≤s)(h:0<a)(p:0≤b)(hb:b≤a/2)(he: ↑(separation x y)+↑(separation x z)≤s)(v:∑ i:Ps c,Faro a y i.1 * ‖X i‖ ≤ V)(e:∑ i:Ps c,Faro a z i.1 * ‖Y i‖≤ R): checkV b x (fun i j=> X i*Y j) ≤ nick b s *taxH a*(V*R):=by
 let f(i:Ps c):=Faro a y i.1*‖X i‖; let k(i:Ps c):= Faro a z i.1*‖Y i‖; have h1(i):0≤f i:=mul_nonneg (Real.exp_pos _|>.le) (norm_nonneg _); have h2(i):0≤k i:=mul_nonneg (Real.exp_pos _|>.le) (norm_nonneg _)
 let D:=nick b s*taxH a
 have ht:∑ i:Ps c,f i ≤V:=v; have hK:∑ i:Ps c,k i ≤R:=e
 apply le_trans _ (mul_le_mul_of_nonneg_left (mul_le_mul ht hK (sum_nonneg fun i _=> h2 i) (le_trans (sum_nonneg fun i _=> h1 i) v)) (show 0≤D from mul_nonneg (nick_pos b hs).le (momentPrice_pos _ (half_pos h)|>.le)))
 change checkV b x _ ≤ D*_; rw [sum_mul, mul_sum]
 refine sum_le_sum fun i _=>?_ ; simp_rw [mul_sum]
 refine sum_le_sum fun j _=>?_ ; let t:ℝ:= ↑(separation y i.1)+↑(separation z j.1); have hw:0≤t:=by unfold t; positivity
 have hl: circle x i j ≤ s+t:=calc
    _ ≤ (↑(separation x y + separation y i.1):ℝ)+(↑(separation x z+separation z j.1):ℝ):= add_le_add (by exact_mod_cast separation_triangle ..) (by exact_mod_cast separation_triangle ..)
    _ ≤ _:=by push_cast; unfold t; linarith
 have hp:= (nick_inc p (rot0 ..) hl).trans (nick_add hs hw)
 have h': Real.exp (a*t)= Faro a y i.1* Faro a z j.1:=by unfold t Faro; rw [mul_add,Real.exp_add]
 rw [norm_mul]
 refine (mul_le_mul_of_nonneg_right (hp.trans (mul_le_mul_of_nonneg_left (dentH h hb hw) (nick_pos b hs|>.le))) (mul_nonneg (norm_nonneg _) (norm_nonneg _))).trans_eq ?_
 unfold f k D; rw [h']; ring
lemma t_all {z r:ℝ}(h:0≤z)(p:1≤r)(k:0≤b)(e:b≤a): nick b (z/r+2)≤nick a 2 * nick b z:=by
 apply (nick_add (show 0≤z/r from div_nonneg h (by linarith)) (by norm_num : (0:ℝ)≤2)).trans
 rw [mul_comm (nick b (z/r))]; exact mul_le_mul (nick_rate e (by norm_num)) (nick_inc k (div_nonneg h (by linarith)) (div_le_self h p)) (nick_pos _ (div_nonneg h (by linarith))|>.le) (nick_pos _ (by norm_num)|>.le)
lemma t_hard {z r:ℝ}(h:Real.sqrt r ≤ z)(p:1≤r)(k:0≤b)(e:b≤a):nick b (z/r+2)≤ nick a 2 * (2/Real.sqrt r*nick b z):=by
 have hr:1 ≤ Real.sqrt r:= Real.one_le_sqrt.mpr p; let m:= Real.sqrt r; have he:m^2=r:= Real.sq_sqrt (by linarith); have ht:0≤z:=by linarith
 have hv: 0 < r:=by linarith
 have hp:0<m:=zero_lt_one.trans_le hr; have hm:0≤z/r:=div_nonneg ht hv.le
 refine (nick_add hm (by norm_num : (0:ℝ)≤2)).trans ?_
 rw [mul_comm (nick b (z/r))]; refine mul_le_mul (nick_rate e (by norm_num)) ?_ (nick_pos b hm|>.le) (nick_pos a (by norm_num)|>.le)
 unfold nick; rw [←mul_assoc]; apply mul_le_mul ?_ (Real.exp_monotone (mul_le_mul_of_nonneg_left (div_le_self ht p) k)) (Real.exp_pos _|>.le) (by positivity); change 1+z/r ≤ (2/m)*(1+z)
 have hl:m≤ r:=by nlinarith only [hr, he, hp]
 apply le_of_mul_le_mul_left _ hp
 rw [mul_add,← mul_assoc m (2/m), show m*(2/m)=2 by field_simp,mul_one]; apply le_trans (b:=z+z) (add_le_add h (by rw [← mul_div_assoc,div_le_iff₀ hv, mul_comm m]; exact mul_le_mul_of_nonneg_left hl ht)); linarith
namespace Rails
variable {Λ : Ps f→Ps c→ℝ}(P:Rails g A a Λ)(h:0<a)(v:0<A)(e:0≤b)(hb:b≤a/2)
private def shack(A a:ℝ):= 4*nick a 2*taxH a*A^2
include P h v e hb
lemma camp_big(x:Site f)(u w: Ps f)(p: Real.sqrt (spanV g) ≤ circle x u w):
 checkV b (g.parent x) (fun i j=> Λ u i*Λ w j-Λ (x,u.2) i*Λ (x,w.2) j) ≤ nick b (circle x u w) * (shack A a)/(Real.sqrt (spanV g)*spanV g^4):=by
 let y:= g.parent x; let L:=spanV g; have hp:1≤L:=period_one; have hl:0<L:=span_pos; let t:= circle x u w; have ht:0≤t:=rot0 ..; let R:= t/L+2; have hR:0≤R:=by unfold R; positivity
 apply le_trans (leaving ..); have he: ↑(separation y (g.parent u.1))+↑(separation y (g.parent w.1))≤R:=(add_le_add (hleft (g:=g) x u.1) (hleft (g:=g) x w.1)).trans_eq (by unfold R t circle L; ring)
 have hx:= survey y _ _ _ _ hR h e hb he (P.rate u) (P.rate w)
 have hz:= survey y y y _ _ hR h e hb (by simpa using hR) (P.rate (x,u.2)) (P.rate (x,w.2))
 refine (add_le_add hx hz).trans ?_
 have hy : nick b R≤ nick a 2 * (2/Real.sqrt L*nick b t):= t_hard p hp e (by linarith)
 let V:= taxH a*(A/L^2*(A/L^2)); have hv:0≤ V:=mul_nonneg (momentPrice_pos _ (half_pos h)|>.le) (by positivity)
 change nick b R*taxH a*_+nick b R*taxH a*_≤ _
 have hh:nick b R*taxH a*(A/L^2*(A/L^2)) ≤ nick a 2 * (2/Real.sqrt L*nick b t)*V:=by rw [mul_assoc]; exact mul_le_mul_of_nonneg_right hy hv
 exact (add_le_add hh hh).trans_eq (by unfold t V L shack; ring)
private def lunch(A a:ℝ):=8*taxH a * (Real.exp (a*5)*A)*(Real.exp (a*2)*A)
lemma camp_tiny(x:Site f)(u w:Ps f)(p:circle x u w ≤ Real.sqrt (spanV g)):
 checkV b (g.parent x) (fun i j=> Λ u i*Λ w j - Λ (x,u.2) i*Λ (x,w.2) j) ≤ nick b (circle x u w) * (lunch A a)/(Real.sqrt (spanV g)*spanV g^4):=by
 let z:=g.parent x; let L:=spanV g; let r:=Real.sqrt L; have hr:1≤r:= Real.one_le_sqrt.mpr period_one; have hl:0<L:=span_pos; have hg:r^2=L:=Real.sq_sqrt hl.le; have hs:0<r:=zero_lt_one.trans_le hr; have hL:r≤L:=by nlinarith only [hr, hs, hg]
 have he : (separation x u.1:ℝ)≤ r:=le_trans (le_add_of_nonneg_right (Nat.cast_nonneg _)) p; have ht : (separation x w.1:ℝ)≤r:=le_trans (le_add_of_nonneg_left (Nat.cast_nonneg _)) p
 let V:=Real.exp (a*2)* (A/L^2); let F:=Real.exp (a*5)*(A/L^3)
 have hU(q:Ps f)(h': (separation x q.1:ℝ)≤ r): ∑ i: Ps c,Faro a z i.1*‖Λ q i‖ ≤ V:=P.shift h z q (p:=by apply (hleft ..).trans; have ht':separation x q.1/spanV g≤(1:ℝ):=(div_le_one span_pos).2 (h'.trans hL); linarith) -- tune
 have hk(q:Ps f)(ht': (separation x q.1:ℝ)≤r): ∑ i: Ps c,Faro a z i.1 * ‖Λ q i-Λ (x,q.2) i‖≤ 4*r*F:=by
    let w:=shiftH x q.1; have he : (w.length:ℝ) ≤ 4*r:=(le_trans (by exact_mod_cast short x q.1 : (w.length:ℝ)≤ 4*(separation x q.1:ℕ)) (by gcongr)) -- tune
    have hw:=P.sprint h x x w q.2 (4*r) (by simpa using he); rw [show stop x w=q.1 from stopH ..] at hw; apply hw.trans; unfold F; apply mul_le_mul he _ (by unfold spanV; positivity) (by positivity)
    have ht:(4*r)/L ≤4:=(div_le_iff₀ hl).2 (by gcongr); gcongr
    exact (by change _/L+1 ≤ (5:ℝ); linarith) -- tune
 let t:= checkV b z (fun i j=> (Λ u i-Λ (x,u.2) i)*Λ w j)
 let r0:= checkV b z (fun i j=> Λ (x,u.2) i*(Λ w j-Λ (x,w.2) j))
 have ht' : checkV b z (fun i j=> Λ u i*Λ w j-Λ (x,u.2) i*Λ (x,w.2) j)≤t+r0:=by
   apply le_trans ?_ (flowing (A:=fun i j=>_) (B:=fun i j=>_) b z) -- tune
   rotate_left -- skip
   apply le_of_eq; congr 1; ext; ring
 have hv : nick b 0=1:=by simp [nick]
 have hp(p:Ps c→ℝ)(q:Ps c→ℝ)(R S)(h1: ∑ i:Ps c,Faro a z i.1*‖p i‖≤R)(h2:∑ i:Ps c,Faro a z i.1*‖q i‖≤S):checkV b z (fun i j=>p i*q j) ≤ taxH a*(R*S):=by simpa only [hv,one_mul] using survey z z z p q (s:=0) le_rfl h e hb (by simp) h1 h2
 have hx:t + r0 ≤ lunch A a/(r*L^4):=by
   have hy: (separation x ((x,u.2) : Ps f).1:ℝ)≤r:=by simpa using hs.le
   refine (add_le_add (hp _ _ _ _ (hk u he) (hU w ht)) (hp _ _ _ _ (hU _ hy) (hk w ht))).trans_eq ?_; unfold lunch V F; field_simp; linear_combination 8*taxH a*hg -- tune
 apply ht'.trans (hx.trans ?_); have hy:nick b (circle x u w) ≥1:=nick_cheap (rot0 ..) e; have H:0≤lunch A a:=by have he:0<taxH a:=momentPrice_pos _ (half_pos h); unfold lunch; positivity
 rw [mul_div_assoc]; exact le_mul_of_one_le_left (by positivity) hy
def fareH(A a:ℝ):=max (shack A a) (lunch A a)
lemma camp_full(x:Site f)(u w:Ps f)(y:Site c){r:ℝ}(hy:(separation y (g.parent x):ℝ)≤ r) :checkV b y (fun i j=>Λ u i*Λ w j-Λ (x,u.2) i*Λ (x,w.2) j)≤ nick a (2*r)* (nick b (circle x u w)*fareH A a/(Real.sqrt (spanV g)*spanV g^4)):=by
 let z:=g.parent x; let T:=circle x u w; let D i j:= Λ u i*Λ w j-Λ (x,u.2) i*Λ (x,w.2) j
 have hp : checkV b z D ≤ nick b T*fareH A a/(Real.sqrt (spanV g)*spanV g^4):=by
    by_cases he: T≤ Real.sqrt (spanV g); · apply (camp_tiny P h v e hb x u w he).trans; gcongr; exact (nick_pos b (rot0 ..)).le; exact le_max_right .. -- tune
    apply (camp_big P h v e hb x u w (le_of_lt (not_le.mp he))).trans; gcongr; exact (nick_pos b (rot0 ..)).le; exact le_max_left .. -- tune
 have ht:0≤r:=(Nat.cast_nonneg _).trans hy; refine le_trans ?_ (mul_le_mul_of_nonneg_left hp (nick_pos a (by positivity : 0≤ 2*r)|>.le)); simp_rw [checkV,mul_sum]; refine sum_le_sum fun i _=> sum_le_sum fun j _=>?_ ; unfold D; rw [←mul_assoc]; apply mul_le_mul_of_nonneg_right _ (norm_nonneg _); have he : circle y i j≤ 2*r+circle z i j:=by
    unfold circle; have hv(u:Site c) : (separation y u:ℝ)≤ r +↑(separation z u):=(le_trans (by exact_mod_cast separation_triangle y z u : (separation y u:ℝ)≤ (separation y z:ℕ) + (separation z u:ℝ)) (add_le_add_left hy _)); linarith [hv i.1, hv j.1]
 apply (nick_inc e (rot0 ..) he).trans; refine (nick_add (by positivity : 0≤ 2*r) (rot0 ..)).trans (mul_le_mul_of_nonneg_right (nick_rate (by linarith) (by positivity)) (nick_pos _ (rot0 ..)|>.le))
end Rails
end YM.CF.Font
