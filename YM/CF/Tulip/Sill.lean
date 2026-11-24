import YM.CF.Tulip.Tag
/-! Uniform library over arbitrarily small caps and all sufficiently large periods. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.Tulip
open Function Filter Lattice Laurent Bloch Next.Free Metric Lat Finset Branch Cube Tenant SU Rush Drapes
open scoped Topology Matrix BigOperators Matrix.Norms.L2Operator Kronecker
attribute [local instance] opCStarAlgebra
variable {ι:Type*}
abbrev WG (ι:Type*) := ι→ (N:Side) → Chin N → Op (Single N)
abbrev shelf (f:WG ι)(a c : ℝ)(v:ℕ)(e:ℝ) := ∀ i N, v≤ N.val → Solo a c (f i N) e
def Lively (f:WG ι):= ∃ (a r e:ℝ),0<a ∧ 0<r ∧ 0<e ∧ ∃ v:ℕ, shelf f a r v e
variable {f g : WG ι}
lemma certify {a r e:ℝ}(ha:0<a)(he:0<e){v:ℕ}(hp:shelf f a r v e): Lively f:= ⟨a,max 1 r,e,ha,lt_max_of_lt_left one_pos,he,v,fun i N h=> (hp i N h).books (le_max_right ..)⟩
namespace Lively
lemma link (p:Lively f)(q:Lively g): ∃ a r e:ℝ, 0<a ∧ 0<r∧ 0<e∧ ∃ v:ℕ,shelf f a r v e ∧ shelf g a r v e:=by
  obtain ⟨a,K,e,h₀,h₁,h₂,v,H⟩:=p; obtain ⟨b,S,d,p₀,p₁,p₂,w,J⟩:=q; let h:=lt_min h₂ p₂
  refine ⟨min a b,K+S,min e d,lt_min h₀ p₀,add_pos h₁ p₁,h,max v w,fun i N hx=>?_,fun i N hx=>?_⟩
  · exact ((axis_down _ _ (H i N ((le_max_left ..).trans hx)) _ h (min_le_left ..)).drop (min_le_left ..)).books (by linarith)
  exact ((axis_down _ _ (J i N ((le_max_right ..).trans hx)) _ h (min_le_right ..)).drop (min_le_right ..)).books (by linarith)
lemma prod (p:Lively f)(q:Lively g): Lively (fun i N z=> f i N z*g i N z):=by
  obtain ⟨a,r,e,ha,hr,hp,v,A,B⟩:=link p q; exact certify ha hp (v:=v) fun i N h=>(A i N h).product (B i N h) ha.le
lemma add (p:Lively f)(q:Lively g): Lively (fun i N z=> f i N z+g i N z):=by
  obtain ⟨a,r,e,ha,hr,hp,v,A,B⟩:=link p q; exact certify ha hp (v:=v) fun i N h=>(A i N h).plus (B i N h)
lemma weighted (p:Lively f)(k:ℂ): Lively (fun i N z=> k • f i N z):=by
  obtain ⟨a,r,e,h,hb,he,v,H⟩:=p; exact certify h he (v:=v) fun i N h=>(H i N h).scale k
lemma scaleR(p:Lively f)(k:ℝ): Lively (fun i N z=> k • f i N z):=by
  convert p.weighted (k:ℂ) using 2; funext N z; exact RCLike.real_smul_eq_coe_smul ..
lemma sub(p:Lively f)(q:Lively g): Lively (fun i N z=> f i N z-g i N z):=by simpa [sub_eq_add_neg] using (p.add (q.weighted (-1))) -- may simp too much
lemma reverseL(p:Lively f): Lively (fun i N=> pale (f i N)):=by
  obtain ⟨a,r,e,h,hb,he,v,H⟩:=p; exact certify h he (v:=v) fun i N h=>solo_opp (H i N h)
lemma one : Lively (fun (_:ι) _ _=>1):=certify (show 0<(1:ℝ) by norm_num) (show 0<(1:ℝ) by norm_num) (v:=0) fun _ _ _=> Crown.ident ..
lemma zero : Lively (fun (_:ι) _ _=>0):=certify (show 0<(1:ℝ) by norm_num) (show 0<(1:ℝ) by norm_num) (v:=0) fun _ _ _=> Crown.free -- inspect

lemma estate {a r e v} (p:shelf f a r v e)(q:0<a)(h:0<e)(hr:0<r)(l:ℝ)(g:0<l)(H:∀ i N,v≤ N.val→ f i N 1=0): ∃ (d m:ℝ), 0<d∧0<m∧ m≤e∧ d≤a/2∧∃ w:ℕ,shelf f d l w m:=by
  have hc:0≤quota:=le_trans (by norm_num : (0:ℝ)≤16) quota_bound
  obtain ⟨w,y,d,hy,hs,hd,h',hw⟩:= Drapes.clips hr.le q hc g
  let Z:= 64*((((w+w:ℕ):ℝ))+1)^4*(1+priceF (w+w) 1)
  have hz:1≤ Z :=by
    have hm: 1≤ ((((w+w:ℕ):ℝ))+1)^4:=one_le_pow₀ (by simp)
    have hx:0≤priceF (w+w) 1:=by unfold priceF; positivity
    unfold Z; nlinarith
  let m:= e*y/Z; have hx:0<m:=div_pos (mul_pos h hy) (zero_lt_one.trans_le hz)
  have hk:m/e≤y :=by unfold m; calc
    _ = y/Z:=by field_simp
    _ ≤ _:=div_le_self hy.le hz
  refine ⟨d,m,hd,hx, by simpa using ((div_le_iff₀ h).mp (hk.trans hs.le)),h',2*(w+w)+3+v,fun i N hp=>?_⟩ -- fix
  have hh:v≤N.val:=by omega
  let b:=bail N e; let ρ(x:Openc (More N) m):↑(Openc (More N) e):=⟨x.val,filt' _ _ _ x.property (by nlinarith [(div_le_iff₀ h).mp hk])⟩
  have T:Towards (forum N e) (badge _) (forum N m) (badge _) ρ y:=by
    refine ⟨Continuous.subtype_mk continuous_subtype_val _,rfl,rfl,fun _ _=>rfl,fun S x x'=>?_,fun f h V hs γ p=>?_⟩
    · change fare S x.val x'.val / |e|≤ y*(fare S x.val x'.val/|m|)
      let z:= fare S x.val x'.val; rw [abs_of_pos hx,abs_of_pos h]; apply (div_le_iff₀ h).mpr
      have hg : m ≤ y * e :=(div_le_iff₀ h).mp hk
      calc
        _ = z/m*m:=by unfold z; field_simp
        _ ≤ z/m*(y*e):=mul_le_mul_of_nonneg_left hg (div_nonneg (fare_t ..) hx.le)
        _ = _:=by unfold z; ring
    exact h V hs (ρ ∘ γ) p
  let X:Openc (More N) e:=⟨1,vacancy0 _ h⟩
  refine T.smaller (s':=bail N m) (t':=bail N m) (A:=fun z : Openc (More N) e=>f i N z.val) (p i N hh) w hs.le hd h' (meterQ ..) hc rfl rfl X (H i N hh) hy.le ?_ ?_
  · intro z i
    let S:= bay (terr (More N)) ((forum N e).home i) (w+w)
    obtain ⟨g,hF⟩:=branch_cost z.val m (w+w) (by simp [More]; omega) z.property ((forum N e).home i)
    use g
    change fare S (relayg g z.val) 1/|e|≤y
    rw [abs_of_pos h]; refine (div_le_iff₀ h).mpr (hF.trans ?_)
    have hb:64*((((w+w:ℕ):ℝ))+1)^4*(m+priceF (w+w) m)=Z*m:=by unfold Z priceF; ring
    rw [hb]; unfold m; field_simp; simp
  · simpa only [abs_of_pos hy,two_mul] using hw

lemma rotor (p:Lively f)(r:ℝ)(g:0<r)(hp:r<1){v e}(he:0<e)(h:∀ i N,v≤ N.val→∀ x∈Openc (More N) e, ‖f i N x‖ ≤ r) : ∃ a b M δ:ℝ, 0<a ∧ 0<b∧ b<1∧ 0<M∧ 0<δ∧ ∃ k:ℕ, ∀ n:ℕ,shelf (fun i N x=> f i N x^n) a (M*b^n) k δ :=by
  obtain ⟨a,c,d,ha,hc,hd,w,J⟩:=p
  let q:=lt_min he hd
  have hm: shelf f a c (max v w) (min e d):=fun i N hx=> axis_down _ _ (J i N ((le_max_right ..).trans hx)) _ q (min_le_right ..)
  have hh:0≤quota:=le_trans (by norm_num : (0:ℝ)≤16) quota_bound
  obtain ⟨t,gt,p₁⟩:=exists_between hp
  obtain ⟨n,hn,ℓ,y,hy,hY,hB,H⟩:=grouping hh ha hc gt (g.trans gt) p₁ (show 0<(1:ℝ)/4 by norm_num)
  obtain ⟨u,p,q₀,e₀⟩:=drift_name hn (show 0<(1:ℝ)/2 by norm_num) (by norm_num)
  refine ⟨y,u, (2 * (Real.exp y * (u^n)⁻¹ * (Real.exp y*(max 1 (2*c))^n))),min e d,hy,p,q₀,?_,q,max v w,fun k i N hv=>?_⟩; swap
  · exact Crown.craft hn (hm i N hv) (Crown.natural _ _ _ _ _ _ _ _ _ hh ha.le (g.trans gt).le hy.le hY hB H (meterQ ..) (hm i N hv) (fun x=> h i N ((le_max_left ..).trans hv) _ (filt' x.val _ _ x.property (min_le_left ..)))) (hY.trans (half_le_self ha.le)) hy p e₀ _
  positivity
end Lively
end YM.CF.Tulip
