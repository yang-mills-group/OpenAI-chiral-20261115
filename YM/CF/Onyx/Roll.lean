import YM.CF.Onyx.Veal
set_option autoImplicit false
noncomputable section
namespace YM.CF.Onyx
open Function Filter Metric Fir Lattice Laurent Next.Free Bloch Finset Lat Ember Jill Flare
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix Matrix.Norms.L2Operator Kronecker
attribute [local instance] opCStarAlgebra
variable {N:Side}{j:ℕ}{r R C w:ℝ}{M:Male}{a:Axis}
-- ignore
variable {A:Site N→Peb}{s:Offset N}
def debt (i:ℕ):ℂ:=bead 8 (-1) i
def odds (F:Site N→Peb)(a:Axis)(d:ℤ)(k:Site N):= F (k+march N a (-d))-∑ i∈range 8,debt i • F (k+march N a (i*d))
lemma debt_bound:∃ C:ℝ,0<C ∧ ∑ i∈range 8,‖debt i‖ ≤ C:=by obtain ⟨c,h,p⟩:=bead_bound 8; refine ⟨c,h,?_⟩; simp only [debt,Complex.norm_real,Real.norm_eq_abs]; exact p _ (by norm_num)
lemma rod_j(i:ℤ)(g:|(i:ℝ)| ≤8)(t:ℤ)(m:ℝ)(h:|extent N t|≤m):|extent N (i*t)|≤8*m:=by rw [march_t,abs_mul]; exact mul_le_mul g h (abs_nonneg _) (by norm_num)
lemma below8 {n:ℕ}(h:n∈range 8): |(↑(n:ℤ):ℝ)| ≤ 8:=by rw [Int.cast_natCast,abs_of_nonneg (by positivity : 0≤ (n:ℝ))]; exact le_of_lt (by exact_mod_cast mem_range.mp h)
lemma gleam(H:1≤j)(p:0<r)(u:0<C)(a:Axis)(l b:ℝ)(hy:0<l)(v:0<b):∃ G:ℝ,0<G∧∀ {N: Side}{A:Site N→Peb}{M:Male}{s:Offset N}{R y:ℝ}, Even N.val→FormU s j M r C A→0<R→R*pinch N≤1→0<y→∀ d:ℤ,|extent N d| ≤ b/R→∀ k:Site N,R*‖glen s k‖≤ l→ ‖odds (flow s j M y A) a d k‖≤ G/R*(1/(1+R*‖glen s k‖)^7):=by
 obtain ⟨c,T,h,hT,P⟩:=soul _ H; obtain ⟨K,hK,Y⟩:=debt_bound
 let V:=l+8*b; let L:=max (c*V) (2*r*C); have hz:0<V:=by unfold V; positivity
 have hh:0<L:= lt_max_of_lt_left (mul_pos h hz)
 refine ⟨(1+l)^7*(1+K)*L,by positivity,fun {N} {A} {M} {s} {R y} g f w t x d he k hu=>?_⟩
 let F:=flow s j M y A; let W:=L/R
 have he(q:ℤ)(hq:|(q:ℝ)|≤8): ‖F (k+march N a (q*d))‖≤ W:=by
    have hh:=abs_le.mp ((within_d (s:=s) g k a (q*d) (8*(b/R)) (rod_j q hq d (b/R) he))); apply flow_b f H p u g V hz y x (k+march N a (q*d)) w t (c:=c)
    · rw [mul_comm, ← le_div_iff₀ w]; unfold V; change _≤_; rw [mul_comm R, ← le_div_iff₀ w] at hu; obtain ⟨hx,_⟩:=hh; rw [add_div,mul_div_assoc]; linarith only [hu,hx]
    exact fun p h=> (P M p h y x).1
    exact h
 have hv: ‖odds F a d k‖≤ W+K*W:=by
    unfold odds; refine (norm_sub_le ..).trans (add_le_add ?_ ((norm_sum_le ..).trans ?_))
    · simpa using he (-1) (by norm_num)
    exact (sum_le_sum (g:=fun i=>‖debt i‖*W) fun i hi=>by rw [norm_smul]; exact mul_le_mul_of_nonneg_left (he i (below8 hi)) (norm_nonneg _)).trans (by rw [←sum_mul]; gcongr)
 exact hv.trans (by
    unfold W; rw [one_div,←div_eq_mul_inv,le_div_iff₀ (by positivity : 0 < (1+R*‖glen s k‖)^7)]; refine (mul_le_mul_of_nonneg_left (show (1+R*‖glen s k‖)^7 ≤ (1+l)^7 by gcongr) (by positivity : 0≤ L/R+K*(L/R))).trans_eq ?_; ring)
lemma ringing (u b R v H:ℝ)(hu:1≤u)(hv:0<v)(hb:0<b)(hr:0<R)(ht:1 ≤ R*b)(g:|H| ≤ u/R): (v*b)* (|H|/b)^8 ≤ (v*u^8*2^7)/R*(1/(1+R*b)^7):=by
 rw [one_div,←div_eq_mul_inv,le_div_iff₀ (by positivity : 0<(1+R*b)^7)]
 refine (mul_le_mul (show v*b*(|H|/b)^8≤v*b*(u/R/b)^8 by gcongr) (show (1+R*b)^7≤ (2*R*b)^7 by gcongr; linarith) (by positivity) (by positivity)).trans_eq ?_; field_simp <;> ring
set_option maxHeartbeats 500000 in
lemma serene(H:1≤j)(p:0<r)(u:1≤w)(a:Axis):∃ V G:ℝ,0<V∧0<G∧∀ {N: Side}{A:Site N→Peb}{M:Male}{s:Offset N}{C R y:ℝ}, Even N.val→FormU s j M r C A→0<R→R*pinch N≤1→0<y→8*w/R<zone→∀ d:ℤ,|extent N d| ≤ w/R→∀ k:Site N,V ≤ R*‖glen s k‖→ ‖odds (flow s j M y A) a d k‖≤ G/R*(1/(1+R*‖glen s k‖)^7):=by
 obtain ⟨b,h,ht,hv,B⟩:=Jill.plunge (limbo _ a H) 8 (by decide); obtain ⟨c,C,hc,U,X⟩:=stern H p; let V:= 1+c+8*w+w/b; have hz:0<V:=by unfold V; positivity
 refine ⟨V,h*w^8*2^7,hz,by positivity,fun {N} {A} {M} {s} {C R y} g f q t e v d l k u'=>?_⟩
 let x:=glen s k; let r':= ‖x‖; have hx:V ≤ R*r':=u'; have hi:0<r':=(by nlinarith only [q,hz,hx]); have he:w/b<R*r':=(by unfold V at hx; linarith only [hx,hc,u]); have htR:1 ≤ R*r':= by unfold V at hx; linarith only [hx,hc, u,show 0<w/b by positivity]
 let i:WarmRay:=(⟨M,x,orb _ _ g,hi⟩,⟨y,e⟩); let D:=extent N d; let Y:=D/r'; let L(z:ℂ):=tail j y M (aura i a z); let F:=flow s j M y A; change |D|≤_ at l
 have hm(z:ℤ)(ho:|(z:ℝ)|≤ 8):L ((z:ℂ)*(Y:ℂ))=F (k+march N a (z*d)):=by
    let x':=k+march N a (z*d); let x'' := glen s x'; let Q:= x+beam a (extent N (z*d)); have h': peers Q x'':= march_a (z*d) s k a; have he:=abs_le.mp (within_d (s:=s) g k a (z*d) (8*w/R) (by simpa [mul_div_assoc] using rod_j z ho d _ l)); have hu: c*pinch N≤‖x''‖:=by
      have ha:V/R≤ r':= by rw [div_le_iff₀ q]; linarith
      unfold V at ha; obtain ⟨_,hg⟩:=he; change r'-‖x''‖≤_ at hg; have hy:pinch N ≤1/R:=by rw [le_div_iff₀ q]; linarith
      refine (mul_le_mul_of_nonneg_left hy hc.le).trans ?_; -- field order
      have hy: 0< w/b/R:=by positivity
      simp_rw [add_div] at ha; rw [← mul_div_assoc,mul_one]; linarith only [ha,hy,hg,show 0<1/R by positivity]
    have hp:= (X N M s x' g).1 hu; have hz:=ice_h g x' j M s; have hi': Bound Real.pi x'':= orb _ s g
    have hy':aura i a ((z:ℂ)*(Y:ℂ)) = tmap Q:=by unfold aura; rw [←Complex.ofReal_intCast z,snap]; congr 2; rw [march_t]; apply congrArg; change (z:ℝ)*(r'*Y)=(z:ℝ)*D; unfold Y; field_simp -- tune
    have hq:tmap Q∈realCube zone:=by
      refine ⟨tmap_physical _,fun j=> ?_⟩; have ht:= ((norm_add_le x (beam a (extent N (z*d)))).trans (add_le_add (show ‖x‖≤Real.pi from i.1.cap) ((beam_cost ..).trans (rod_j z ho d _ l)))); have hy:|Q j|≤ ‖Q‖:=b_abs Q j
      change |((_ : ℝ):ℂ).re|<_; rw [Complex.ofReal_re]; change ‖Q‖≤_ at ht; rw [mul_div_assoc] at v; linarith only [hy,ht,v]
    have hk:tmap x''∈realCube zone:= base_subset_realCube zone_pos (b_base hi'); unfold L tail; rw [hy',seep j M h' hq hk, ← h'.map_shell hq hk M.val j]; unfold F flow; rw [f.far x' hp]; rw [show shell j M.val (tmap x'')= _ from hz]
 have hy: ‖(Y:ℂ)‖= |D|/r':=by simp [Y,abs_div,abs_of_pos hi]
 have hY: ‖(Y:ℂ)‖<b:=by rw [hy,div_lt_iff₀ hi]; apply l.trans_lt; rw [div_lt_iff₀ q]; rw [div_lt_iff₀ ht] at he; linarith
 have hv':= B i (-1) (by norm_num) (Y:ℂ) hY; rw [zpow_one] at hv'; change ‖L (_*(Y:ℂ))-∑ l∈ range 8,debt l • L ((l:ℂ)*(Y:ℂ))‖≤ h*r'*‖(Y:ℂ)‖^8 at hv'; rw [show (↑(-1:ℝ):ℂ)=((-1:ℤ):ℂ) by norm_num, hm (-1) (by norm_num),neg_one_mul,hy,sum_congr (g:=fun l=> debt l • F (k+march N a (l*d))) rfl (fun l hl=>show debt l • L _=debt l • F _ from by rw [← Int.cast_natCast (R:=ℂ) l,hm l (below8 hl)])] at hv'
 exact hv'.trans (ringing w r' R h D u hv hi q htR l)
end YM.CF.Onyx
