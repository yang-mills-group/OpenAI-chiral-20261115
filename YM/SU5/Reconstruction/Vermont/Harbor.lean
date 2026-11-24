import YM.SU5.Reconstruction.Vermont.Playlist
import YM.SU5.Reconstruction.Crease.Diagonal
/-!
# RECAP vacuum observations of apertures deep outside the region
-/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Lens
open Function Set Filter MeasureTheory Spectral Analysis OS.Semigroup ConePrice Sail BridgeClub Anvil
open scoped BigOperators Topology NNReal InnerProductSpace ComplexOrder
variable {H:Hilbert}{a:Axis}(S:OS.Semigroup H a)(A B:H.Op)(x:H)
private lemma shore (U:ℂ)(p:0≤U.re) : U∈ closure inside:= by
 let f(u:ℝ):ℂ:= U+u; have he : f 0=U:=by simp [f]
 have h:Continuous f:=continuous_const.add Complex.continuous_ofReal; rw [← he]; exact mem_closure_of_tendsto (s:=inside) ((h.tendsto 0).mono_left (nhdsWithin_le_nhds (s:=Ioi 0))) (by filter_upwards [self_mem_nhdsWithin] with i z; change 0 < (f i).re; simp [f]; linarith [show 0 < i from z]) -- tune
lemma patrol {r:ℝ≥0}(p:0<r)(u:∀ t:ℝ≥0,0<t→t<r→ A (S.E t x)= B (S.E t x))(z:ℂ)(e: 0≤ z.re): A (phase S z x)= B (phase S z x):=by
 let f(z:ℂ):= A (phase S z x); let g(z:ℂ):= B (phase S z x); let χ(z:ℂ):= phase S z x
 have hc: Continuous χ:= phase_cont S (fun i=>i) (fun _=> x) continuous_const continuous_id
 have hv:AnalyticOnNhd ℂ χ inside:= fun z v=> (((ContinuousLinearMap.apply ℂ H.space x).analyticAt _).comp (phase_ana S z v))
 refine EqOn.closure (s:=inside) ?_ (A.continuous.comp hc) (B.continuous.comp hc) (shore z e) -- arg names
 obtain ⟨s,t,w⟩:= exists_between (show 0< (r:ℝ) from p)
 apply pioneer ((convex_halfSpace_gt Complex.reCLM.toLinearMap.isLinear 0).isPreconnected) (show (s:ℂ)∈inside from t) _ _ ⟨t,w⟩ (fun z v=>(A.analyticAt _).comp (hv z v)) (fun z v=>(B.analyticAt _).comp (hv z v)) _
 intro a b; dsimp only [χ,Function.comp]; rw [width_real]; exact u _ (Real.toNNReal_pos.mpr b.1) ((NNReal.coe_lt_coe).mp (by rw [Real.coe_toNNReal a b.1.le]; exact b.2))
open Picket
variable {b:Axis}(l:b≠a)(Z:Set ℝ)(d:Dense Z)(P:Forward S)
include l P d
lemma traverses (c:ℝ)(r:ℝ≥0)(p:0<r)(u:∀ y∈ Z,c<y→∀ t:ℝ≥0,0<t→t<r→ A (S.E t (trans S (y • basis b) x)) = B (S.E t (trans S (y • basis b) x))) (z:E4)(v:∀ i:Axis, i≠a→ i≠b→ z i=0) : A (trans S z x)= B (trans S z x):=by
 let h:= c+1; let u₀:= (z a) • basis a; let z6:= (z b) • basis b; let γ:= Picket.cross a b l; let ℓ:= z a; let t:= z b
 -- avoid ambiguity eject.Reframe
 have V': u₀+z6=z:=by
   ext i; by_cases h:i=a
   · subst i; simp [u₀,z6,l.symm]
   by_cases g:i=b
   · subst i; simp [u₀,z6,h]
   simp [u₀,z6,h,g,v i h g]
 have hX (u:ℝ): S.U (u • γ)=trans S (u • basis b):= (trans_space (h:=l) b u S).symm -- check order
 have hh (s:ℝ≥0)(w:0<s)(e:s<r): A (S.E s (trans S z6 x))=B (S.E s (trans S z6 x)):=by
   have hz : ‖γ‖≤1:=le_of_eq (by change ‖basis b‖=1; simp)
   let W:= Sail.transverse S P γ hz s w; let L(z:ℂ):= W z x;
   have hx(u:ℝ):S.E s (trans S (u • basis b) x)= L u:= by rw [← hX]; unfold L W Sail.transverse; rw [on_strip S P γ hz s w]; exact DFunLike.congr_fun (S.independent s _) x
   have hy:AnalyticOnNhd ℂ L (slit s):= fun i v=>((ContinuousLinearMap.apply ℂ H.space x).analyticAt _).comp (transverse_anal S P γ hz s w i v)
   have hb:Continuous (fun i:ℝ=> L i):= hy.continuousOn.comp_continuous Complex.continuous_ofReal (fun i=> slit_ground _ w i)
   rw [show z6=t • basis b from rfl,hx]; have kk:= Ioo c (c+1); obtain ⟨T,v₁,v₂⟩:= exists_between (show c<c+1 by linarith)
   apply pioneer (slit_connected _) (slit_ground _ w T) _ _ ⟨v₁,v₂⟩ (M₁:=fun i=>A (L i)) (fun z v=>(A.analyticAt _).comp (hy z v)) (fun z v=>(B.analyticAt _).comp (hy z v)) _ (slit_ground _ w t)  -- args syntax
   intro y k; apply EqOn.closure (s:=Ioi c∩ Z) _ (A.continuous.comp hb) (B.continuous.comp hb) (show y∈_ from d.open_subset_closure_inter isOpen_Ioi k.1)
   rintro z ⟨q,p⟩; change A (L z)=B (L z); rw [←hx]; exact u z p q s w e
 rw [←V',trans_sum,show trans S u₀=S.edge ℓ from trans_time ℓ S]; change A (S.edge ℓ _) = B (S.edge ℓ _); rw [← width_imaginary]; exact patrol _ _ _ _ p hh _ (by rw [side]) -- exact by simp
end YM.Lens
