import YM.CF.Exa.Proud
set_option autoImplicit false
set_option maxHeartbeats 450000
set_option synthInstance.maxSize 18000
noncomputable section
namespace YM.CF.Exa
open Function Filter Metric Lattice Wilson Laurent Lat Stationary Rush Cube Scroll SU Drapes Fir Peaks Dial Paige Brace Vault Fock Tulip Font Spire Nacre Ember Pec Branch NormedSpace Finset
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate Matrix Matrix.Norms.L2Operator Kronecker
attribute [local instance] opCStarAlgebra
open Tap Thera Haro -- tune
open Tap Tenant Proa
lemma estate_m (n:ℕ){ι:Type*}{f:WG ι}{a r e v} (p:shelf f a r v e)(q:0<a)(h:0<e)(hr:0<r)(l:ℝ)(g:0<l)(H:∀ i N,v≤ N.val→ f i N 1=0): ∃ (d m c:ℝ), 0<d∧0 < m∧ m≤e∧ d≤a/2∧ d ≤ 1 ∧ 0 ≤ c ∧ ((d/(n+1:ℝ))⁻¹)^n * c ≤ l ∧∃ w:ℕ,shelf f d c w m:=by
  have hc:0<Tenant.quota:=lt_of_lt_of_le (by norm_num : (0:ℝ)<16) quota_bound
  obtain ⟨w,y,d,hy,hs,hd,h1,h',hw⟩:= Drapes.gain hr.le q hc g n
  let Z:= 64*((((w+w:ℕ):ℝ))+1)^4*(1+priceF (w+w) 1)
  have hz:1≤ Z :=by
    have hm: 1≤ ((((w+w:ℕ):ℝ))+1)^4:=one_le_pow₀ (by simp)
    have hx:0≤priceF (w+w) 1:=by unfold priceF; positivity
    unfold Z; nlinarith
  let m:= e*y/Z; have hx:0 < m:=div_pos (mul_pos h hy) (zero_lt_one.trans_le hz)
  have hk:m/e≤y :=by unfold m; calc
    _ = y/Z:=by field_simp
    _ ≤ _:=div_le_self hy.le hz
  let B:= Real.exp (-a/2*w)*r; let V:= Tenant.quota*(((((w+w):ℕ):ℝ)+1)^4); let c:= V*Real.exp (2*d*V)*(B+r*(2*y))+B; have hB:0≤c:=by unfold c B V; positivity
  refine ⟨d,m,c,hd,hx, by simpa using ((div_le_iff₀ h).mp (hk.trans hs.le)), (show d≤a/2 by linarith),h1,hB,hw,2*(w+w)+3+v,fun i N hp=>?_⟩ -- fix
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
  refine T.smaller (s':=bail N m) (t':=bail N m) (A:=fun z : Openc (More N) e=>f i N z.val) (p i N hh) w hs.le hd (by linarith: d ≤ a/2) (meterQ ..) hc.le rfl rfl X (H i N hh) hy.le ?_ ?_
  · intro z i
    let S:= bay (terr (More N)) ((forum N e).home i) (w+w)
    obtain ⟨g,hF⟩:=branch_cost z.val m (w+w) (by simp [More]; omega) z.property ((forum N e).home i)
    use g
    change fare S (relayg g z.val) 1/|e|≤y
    rw [abs_of_pos h]; refine (div_le_iff₀ h).mpr (hF.trans ?_)
    have hb:64*((((w+w:ℕ):ℝ))+1)^4*(m+priceF (w+w) m)=Z*m:=by unfold Z priceF; ring
    rw [hb]; unfold m; field_simp; simp
  · intro A C; rw [abs_of_pos hy, ←two_mul]; unfold c; change V*Real.exp (d*V)*(B+r*(2*y))+B≤_; have hp:0 ≤ V:=by unfold V; positivity
    have hb: 0 ≤ B:=by unfold B; positivity
    gcongr; linarith


end YM.CF.Exa
