import YM.CF.BProof.Bias.Harp
/-! Time-uniform nogapz obstruction: exhibits bounded-degree approximation failure
 on chosen discrete spectral sector, without replacing B_D with limiting symbol. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BProof.Bias
open Function Filter Fock Finset Branch Tenant Cube SU Tulip Lat Lattice Dial Spin Fig Align Stint
open Fir Laurent Rush Bloch Next.Free BZ Real
open scoped Topology BigOperators Matrix MatrixOrder InnerProductSpace Kronecker Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
variable {j:ℕ}(h:1≤j)(r:ℕ){K s q b v:ℝ}{p: Stint.Pay}
def RentZ (r:ℕ)(K s q:ℝ):Prop:= 2+revCost r*(r*(4*s)*(K/q+1)) < (K*(2*q))⁻¹-1-K/s
private lemma positive_small {f:ℝ→ℝ}{K x:ℝ}(k:0 < x)(h:Continuous f)(v:f 0<K): ∃ s:ℝ, 0<s ∧ s<x∧ f s<K := by
 let l:= 𝓝[>] (0:ℝ); have he:∀ᶠ k in l, f k<K:=(h.continuousWithinAt (s:=Set.Ioi 0) (x:=0)).eventually (gt_mem_nhds v); have g:∀ᶠ t in l, t<x:= nhdsWithin_le_nhds (gt_mem_nhds k); exact (he.and (g.and (show ∀ᶠ t in l, 0<t from self_mem_nhdsWithin))).exists.imp (fun s ⟨p,t,h⟩=>⟨h,t,p⟩)
lemma rentZ (k:0<K): ∃ s q:ℝ,0<q ∧ q<1 ∧ q<s∧ 2*s<π∧RentZ r K s q:=by
 let C:= (K*2)⁻¹; have he:0<C:=by unfold C; positivity
 obtain ⟨s,f,g,l⟩:=positive_small (show 0<π/2 by positivity) (x:=π/2) (K:=C) (f:=fun s:ℝ=>revCost r*(r*(4*s)*K)) (by fun_prop) (by simpa)
 let W:=revCost r*(r*(4*s)); have hx: W*K<C:= by unfold W; rwa [mul_assoc]
 obtain ⟨q,u,y,L⟩:= positive_small (lt_min zero_lt_one f) (x:=min 1 s) (K:=C) (f:=fun q:ℝ=>(2+1+K/s+W)*q+W*K) (by fun_prop) (by simpa)
 refine ⟨s,q,u,(lt_min_iff.mp y).1,(lt_min_iff.mp y).2,by linarith,?_⟩; unfold RentZ; apply lt_of_mul_lt_mul_right (a:=q) -- tune signature
 swap; exact u.le
 rw [show (2+ revCost r*(r*(4*s)*(K/q+1)))*q=2*q+ W*K +W*q from (by unfold W; field_simp; ring),sub_mul,sub_mul,one_mul,show (K*(2*q))⁻¹*q=C from (by unfold C; field_simp)] -- tune
 linarith
include h r -- tune
lemma lacks {N:Side}(S:Scale j K)(H: RentZ r K s q)(W w:Per N)(M:Male)(x:0<q)(X:q<s)(f:q≤ principal w)(z:principal w ≤2*q)(g:s≤principal W)(k:principal W≤2*s): ¬ Near ht r 1 (AngleZ j M w):=by
 let e:Site N:=fun _=>w; let t:Site N:= fun i=> if i=0 then W else w; let A:= AngleZ j M w; let T:=twang (disp e t) (disp_u e t) (N:=N) ht
 have hx:0<s:=x.trans X; have hv:= x.trans_le f; have ht':0<K:= S.p
 have hz: ‖A‖≤K/q:=by unfold A AngleZ haloW wing modality; rw [relic_mul]; apply relic_up (by positivity); intro i; by_cases h':i∈Label 1 w; simp only [Pi.mul_apply,thinK,h',ite_true,mul_one]; refine (S.slice h x M i ?_).2; refine f.trans ?_; have hh:pm i 1=principal w:=(by unfold pm; rw [Function.comp_apply,(labelled ..).1 h']); exact le_trans (le_of_eq (Real.norm_of_nonneg hv.le).symm) (hh ▸ norm_le_pi_norm (pm i) 1); simp [thinK,h']; positivity
 intro u; let U:= ‖wiggle T A‖; have he: U ≤ 2+ revCost r*(r*(4*s)*(K/q+1)):=by apply (near_w (N:=N) _ (disp_pr e t) (disp_u e t) ht u hz).trans; rw [mul_one]; unfold revCost; gcongr; apply (disp_pitch ..).trans; change |(principal W:ℝ)-principal w|≤_; apply abs_le.mpr; constructor <;> linarith
 apply not_lt_of_ge he; apply lt_of_lt_of_le H; apply le_trans _ (disp_l e t M h (fun i k=> (if_neg k).symm) w (show e 1=w from rfl)); have he':‖pm e‖ ≤ 2*q:= (pi_norm_le_iff_of_nonneg (by positivity)).2 fun i=> (Real.norm_of_nonneg hv.le).trans_le z
 refine sub_le_sub (S.flare h (by positivity) M e he') (S.slice h hx M t ?_).2; exact g.trans (le_trans (le_of_eq (Real.norm_of_nonneg (hx.trans_le g).le).symm) (norm_le_pi_norm (pm t) 0)) -- defeq
lemma bankable (p: Stint.Pay):∃ b v:ℝ,∃ k:ℕ,0≤b∧ b<1∧0≤v∧∀ {N:Side}, k≤N.val→∃ w:Per N,∀ (M:Male), (∀ i:ℕ,Near ht i (tailPay p i) (redP j M N))→ Tango ht b v p (AngleZ j M w) ∧ ¬ Near ht r 1 (AngleZ j M w):=by
 obtain ⟨K,ht⟩:= scaleP h; have hp:= ht.p; obtain ⟨s,q,g,e,u,t,H⟩:=rentZ r hp; obtain ⟨k,hk⟩:= sample g (by linarith:2*q<π); obtain ⟨i,hi⟩:=sample (g.trans u) t; let b:=1-(q/K)^2; have hr:0 < q/K:= (by positivity); refine ⟨b,K/q,max k i,?_,by unfold b; nlinarith only [sq_pos_of_pos hr],by positivity,?_⟩; · have hp: q/K ≤1:= (div_le_one hp).mpr (e.le.trans ht.1); unfold b; nlinarith
 intro N x; obtain ⟨w,f,z⟩:=hk N ((le_max_left ..).trans x); obtain ⟨W,f',z'⟩:=hi N ((le_max_right ..).trans x); refine ⟨w,fun M E=> ⟨?_,lacks h r ht H W w M g u f z f' z'⟩⟩; apply bills M h w ?_ (by positivity) ?_ E; · have hp:q/K≤1:=(div_le_one hp).mpr (e.le.trans ht.1); unfold b; nlinarith
 intro i a; have hv:pm i 1= Lat.principal w:=(by unfold pm; rw [Function.comp_apply,(labelled ..).1 a]); have he:= ht.slice h g M i (show q ≤ ‖pm i‖ from f.trans (le_trans (le_of_eq (Real.norm_of_nonneg ((g.trans_le f).le)).symm) (hv ▸ norm_le_pi_norm (pm i) 1))); exact ⟨(by unfold b; rw [sub_sub_cancel]; exact he.1), (zag_norm j M h i).symm.le.trans (pow_le_pow_left₀ (norm_nonneg _) he.2 _)⟩
end YM.CF.BProof.Bias
