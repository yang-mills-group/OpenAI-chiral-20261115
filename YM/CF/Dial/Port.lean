import YM.CF.Dial.Stick
set_option autoImplicit false
set_option synthInstance.maxSize 8000
noncomputable section
namespace YM.CF.Dial
open Function Filter Lattice Laurent Bloch Next.Free Metric Lat Finset Branch Cube Tenant SU Rush Drapes Fir Tulip Fock Peaks
open scoped Topology Matrix MatrixOrder BigOperators Matrix.Norms.L2Operator Kronecker InnerProductSpace
attribute [local instance] opCStarAlgebra
variable {N P:Side}(G:Ratio N P)
variable {ι:Type*}{L:Side}{u v:AxisT}{A B:Chop ι}{a r e s c:ℝ}{k:ℕ}
omit G
lemma rosary (a r c K t:ℝ)(ha:0<a)(hr:0<r)(hc:0<c)(h:c<1)(g:0<K)(ht:0<t): ∃ (m n:ℕ)(d w:ℝ), 0<n∧0<w∧w<1∧0<d∧d≤a/2 ∧
      let x:=Real.exp a*(2*r)^n; let y:=Real.exp (-a/2*m)*x; let V:=K* (((m+m:ℕ):ℝ)+1)^4; V*Real.exp (d*V)*(c^n+y+x*(w+w))+y ≤ t:=by
  obtain ⟨L,hp,hq⟩:=breakp ha hr; let Q:= Real.exp (-a/2*L)*(2*r); have hQ: 0<Q:=by unfold Q; positivity
  let x(n:ℕ):=Real.exp a*(2*r)^n; let y(n:ℕ):=Real.exp (-a/2*(((L*n):ℕ):ℝ))*x n; let V(n:ℕ):= K*(((L*n+L*n:ℕ):ℝ)+1)^4
  have hs(n:ℕ):y n= Real.exp a* Q^n :=by unfold Q y x; rw [mul_pow (Real.exp _),←Real.exp_nat_mul]; push_cast; ring_nf
  have he := fun i:ℕ=> summable_pow_mul_geometric_of_norm_lt_one i (by rwa [Real.norm_of_nonneg hc.le] : ‖c‖<1)
  have hb := fun i:ℕ=> summable_pow_mul_geometric_of_norm_lt_one i (by rwa [Real.norm_of_nonneg hQ.le] : ‖Q‖<1)
  let B:= K*(2*(L:ℝ)+1)^4; have hx(n:ℕ)(p:0<n): V n≤ B*n^4:=by
    have hp:(1:ℝ)≤n :=by exact_mod_cast p
    unfold V B; rw [mul_assoc,←mul_pow]; push_cast; gcongr; linarith
  let F(n:ℕ):= V n*(c^n+y n)+y n
  let f(n:ℕ):= B*n^4*(c^n+y n)+y n
  have hF: Summable f:=by
    apply ((( (he 4).mul_left B).add ((hb 4).mul_left (B*Real.exp a))).add ((hb 0).mul_left (Real.exp a))).congr
    intro i; unfold f; rw [hs]; ring
  obtain ⟨n,hn,H⟩:= ((eventually_gt_atTop (0:ℕ)).and (hF.tendsto_atTop_zero.eventually (gt_mem_nhds ht))).exists
  have hy : F n<t := lt_of_le_of_lt (add_le_add_left (mul_le_mul_of_nonneg_right (hx n hn) (add_nonneg (pow_nonneg hc.le _) (show 0≤y n by unfold y x; positivity))) (y n)) (show f n<t from H)
  let W(d:ℝ):= V n*Real.exp (d*V n)*(c^n+y n+x n*(d+d))+y n
  have ht: Continuous W:=by unfold W; fun_prop
  have hW : ∀ᶠ i in 𝓝[>] (0:ℝ), W i<t:= ht.continuousAt.continuousWithinAt (gt_mem_nhds (show W 0<t by simpa [W,F] using hy))
  obtain ⟨d,p,g,q⟩ : ∃ i:ℝ,i∈Set.Ioi 0 ∧ W i<t ∧ i<min 1 (a/2):= by
    have he: ∀ᶠ i in 𝓝[>] (0:ℝ), i< min 1 (a/2):= nhdsWithin_le_nhds (gt_mem_nhds (lt_min (by norm_num) (half_pos ha)))
    exact ((show ∀ᶠ i in 𝓝[>] (0:ℝ), i∈Set.Ioi 0 from self_mem_nhdsWithin).and (hW.and he)).exists
  exact ⟨L*n,n,d,d,hn,p,q.trans_le (min_le_left ..),p,q.le.trans (min_le_right ..),g.le⟩
lemma quota_p : 0<quota:= lt_of_lt_of_le (by norm_num:(0:ℝ)<16) quota_bound
lemma invert_stencil (p:IndexB L u u A a r e k)(ha:0<a)(hr:0<r)(hk:0<e)(hc:0<c)(hq:c<1) (H:∀ i {N P:Side}(G: Ratio N P),G.count=L→ k≤N.val→ ‖A i G (vacancyY N P)‖ ≤ c)(q:ℝ)(hp:0<q): ∃ m d:ℝ,0<m∧0<d∧m≤e∧d≤a ∧∃ n b:ℕ,0<n∧ IndexB L u u (fun i _ _ G x=>A i G x^n) d q m b:=by
  obtain ⟨m,n,d,w,h,hw,g,Hd,H',hy⟩:=rosary a r c quota q ha hr hc hq quota_p hp
  have hB: IndexB L u u (fun i _ _ G x=>A i G x^n) a (Real.exp a*(2*r)^n) e k:=fun i _ _ G he hv=> (p i G he hv).powers ha.le n -- check
  obtain ⟨t,Z,hz,W,F⟩:=anchor_dusk (A:=fun i _ _ G x=> A i G x^n) hB (c^n) (by positivity) (fun i _ _ G hc hg=> (norm_pow_le ..).trans (pow_le_pow_left₀ (norm_nonneg _) (H i G hc hg) n)) hk m d w hw g.le Hd H'
  exact ⟨t,d,Z,Hd,hz,H'.trans (half_le_self ha.le),n,W,h,fun i _ _ G q p=> (F i G q p).books hy⟩
-- frequent semiring
abbrev Interest(L:Side)(A:Chop ι):=∃ e:ℝ,0<e∧∃ k:ℕ,∀ i {N P:Side}(G: Ratio N P),G.count=L→ k≤N.val→∀ x ∈zoneP G e, IsUnit (A i G x)
lemma awaken (h:IndexB L u u A a r e k)(ha:0<a)(hr:0<r)(p:0<e)(hc:0<c)(hq:c<1)(H:∀ i {N P:Side}(G: Ratio N P),G.count=L→ k≤N.val→ ‖A i G (vacancyY N P)‖ ≤ c):∃ d m K C:ℝ,0<d∧0<m∧m≤e∧0<K∧0<C∧C<1∧∃ t:ℕ,∀ n:ℕ,IndexB L u u (fun i _ _ G x=> A i G x^n) d (K*C^n) m t:=by
  obtain ⟨m,d,hp,hd,he,hf,n,t,hn,hx⟩:= invert_stencil h ha hr p hc hq H (1/4) (by norm_num)
  obtain ⟨K,l,hm,B⟩:=drift_name hn (show 0<(1:ℝ)/2 by norm_num) (by norm_num)
  refine ⟨d,m,(2 * (Real.exp d * (K^n)⁻¹ * (Real.exp d*(max 1 (2*r))^n))), K, hd,hp,he,by positivity,l,hm, max k t, fun n i N P G hc hv=>?_⟩
  exact Crown.craft hn ((neck hp he h) i G hc ((le_max_left ..).trans hv)) (hx i G hc ((le_max_right ..).trans hv)) hf hd l B _
end YM.CF.Dial
