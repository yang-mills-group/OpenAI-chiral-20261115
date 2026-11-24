import YM.CF.Peaks.Shape
set_option autoImplicit false
noncomputable section
namespace YM.CF.Peaks
open Function Filter Lattice Laurent Bloch Next.Free Metric Lat Finset Branch Cube Tenant SU Rush Drapes Fir Tulip
open scoped Topology Matrix BigOperators Matrix.Norms.L2Operator Kronecker
attribute [local instance] opCStarAlgebra
variable {N P:Side} (G:Ratio N P) (u v:Bool)
-- equality use ∥ residual ∥ ≤ limit. Neumann 
variable {L:Side}{ι:Type*}{A B:Script ι}
def Slope (L:Side)(f:Script ι)(r:ℝ):=∃ e:ℝ,0<e∧∃ k:ℕ,∀ i {N P:Side}(G:Ratio N P),G.count=L→ k≤N.val → ∀ x∈legal G e,‖f i G x‖≤r
def Always (L:Side)(P:∀ {N F:Side}(G:Ratio N F), Coil N F →Prop):=∃ e:ℝ,0<e∧∃ k:ℕ,∀ {N F}(G:Ratio N F),G.count=L→ k≤N.val →∀ x ∈ legal G e, P G x
def UnitAlways (L:Side)(f:Script ι):= Always L fun {N F} G x=> ∀ i,IsUnit (f i G x)
lemma series (p:Save L u u @A){r e k}(h:0<r)(g:r<1)(he:0<e) (H:∀ i {N P:Side}(G:Ratio N P),G.count=L→ k≤N.val →∀ x∈legal G e, ‖A i G x‖≤r): ∃ b c M δ:ℝ,0<b∧0<c∧c<1∧0<M∧0<δ∧∃ v:ℕ,∀ n:ℕ,Tax L (fun i _ _ G x=> A i G x^n) u u b (M*c^n) v δ:=by
  obtain ⟨a,K,m,ha,hK,hm,v,W⟩:=p
  let δ:=min m e; have hx:=lt_min hm he; have hc:0≤quota:=(show 0≤(16:ℝ) by norm_num).trans quota_bound
  obtain ⟨t,hy,hf⟩:= exists_between g
  obtain ⟨n,hn,V,d,hd,hd',hp,hw⟩:=grouping hc ha hK hy (h.trans hy) hf (show 0<(1:ℝ)/4 by norm_num)
  obtain ⟨c,s,C,F⟩:=drift_name hn (show 0<(1:ℝ)/2 by norm_num) (by norm_num)
  refine ⟨d,c,(2 * (Real.exp d * (c^n)⁻¹ * (Real.exp d*(max 1 (2*K))^n))),δ,hd,s,C,by positivity,hx,max k v,fun l i N P G p q=>?_⟩
  have hQ:= decayV W hx (min_le_left ..) i G p ((le_max_right ..).trans q)
  refine Crown.craft hn hQ (Crown.natural _ _ _ _ _ _ _ _ _ hc ha.le (h.trans hy).le hd.le hd' hp hw (temper_cap ..) hQ (fun x=> H i G p ((le_max_left ..).trans q) _ (insideP G x.property (min_le_right ..)))) (hd'.trans (half_le_self ha.le)) hd s F l
lemma valEq (p:Save L u v @A)(P0:Always L (fun {N F} G x=>∀ i,A i G x=B i G x)): Save L u v @B:=by
  obtain ⟨a,c,e,h,m,p,k,H⟩:=p; obtain ⟨d,hb,t,W⟩:=P0; let g:=lt_min p hb
  refine ⟨a,c,min e d,h,m,g,max k t,fun i N P G he hv=>?_⟩
  convert decayV H g (min_le_left ..) i G he ((le_max_left ..).trans hv) using 1; ext1 x; exact (W _ he ((le_max_right ..).trans hv) _ (insideP _ x.property (min_le_right ..)) i).symm
lemma driveway (h: Save L u u @A){r:ℝ}(he:0<r)(hp:r<1)(p:Slope L @A r): Save L u u (fun i _ _ G x=> (1-A i G x)⁻¹) ∧ UnitAlways L (fun i _ _ G x=> 1-A i G x):=by
  obtain ⟨e,ha,k,H⟩:=p; obtain ⟨b,c,M,d,p,hc,hc',hM,g,v,W⟩:= series u h he hp ha H
  constructor
  · let f (n:ℕ):= M*c^n; have hf:Summable f:= (summable_geometric_of_lt_one hc.le hc').mul_left M
    have hq: Save L u u (fun i _ _ G x=>∑' n:ℕ,A i G x^n):= recorded (k:=v) (fun i N P G h ht=> by exact Crown.tsK f (fun l=> W l i G h ht) p.le hf) p g
    exact valEq u u (A:=fun i _ _ G x=> ∑' n:ℕ,A i G x^n) hq ⟨e,ha,k,fun {N P} G he hv x h i=> route_inv ((H i G he hv x h).trans_lt hp)⟩
  exact ⟨e,ha,k,fun {N P} G hk h x he i=> Fock.live_of ((summable_geometric_of_norm_lt_one ((H i G hk h x he).trans_lt hp)).one_sub_mul_tsum_pow)⟩
lemma righted (p:Save L u v @A)(h:Save L v u @B)(H:∀ i {N P:Side}(G:Ratio N P),G.count=L→A i G 1*B i G 1=1): Save L v u (fun i _ _ G x=>(A i G x)⁻¹) ∧ UnitAlways L @A:=by
  let Y:Script ι:=fun i _ _ G x=>1-A i G x* B i G x; have hh:Save L u u @Y:= (Save.one _).sub (p.mul h)
  have hx:Slope L @Y (1/2) := by
    obtain ⟨a,r,e,h₀,hc,hE,k,K⟩:=hh
    have hg (i) {N P:Side}(G:Ratio N P) (h:G.count=L)(_:k≤N.val): Y i G 1=0:=by dsimp only [Y]; rw [H i G h,sub_self] -- edit
    obtain ⟨b,m,p,q,-,w,W⟩:= curve (A:=@Y) K h₀ hc hE (1/2) (by norm_num) @hg
    exact ⟨m,q,w,fun i _ _ G he ht x hp=> (W i G he ht).lib.boundOp p.le ⟨x,hp⟩⟩
  obtain ⟨ht,c⟩:= driveway u (A:=@Y) hh (show 0<(1:ℝ)/2 by norm_num) (by norm_num) hx
  obtain ⟨e,k,v,Hx⟩:=c
  have H' {N P:Side}(G:Ratio N P)(hc:G.count=L)(hv:v≤N.val){x: Coil N P}(he:x∈ legal G e)(i:ι): A i G x*(B i G x*(1-Y i G x)⁻¹)=1:=by
    have hk : IsUnit (1-Y i G x):= Hx G hc hv x he i; rw [←mul_assoc,show A i G x*B i G x=1-Y i G x from (sub_sub_cancel 1 _).symm]; exact (Fock.live hk).1
  exact ⟨valEq _ _ (A:=fun i _ _ G x=>B i G x*(1-Y i G x)⁻¹) (h.mul ht) ⟨e,k,v,fun {N P} G hc hv x he i=>(Matrix.inv_eq_right_inv (H' G hc hv he i)).symm⟩, e,k,v,fun {N P} G hc hv x he i=>Fock.live_of (H' G hc hv he i)⟩
end YM.CF.Peaks
