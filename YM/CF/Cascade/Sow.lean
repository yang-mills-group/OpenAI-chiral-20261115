import YM.CF.Cascade.Sums
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
set_option autoImplicit false
noncomputable section
namespace YM.CF.Cascade
open Function Filter Metric Finset Lattice Wilson Next.Free Bloch Laurent Scroll Precision Exterior Lat Ember Aroma
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate Matrix MatrixOrder Kronecker
variable {j t:ℕ}{n c f:Side}{k a b:ℝ}
open Tree SU Font Cube Extra.Iteration Nacre
open Thera Fock Dial Peaks Tulip Paige NormedSpace
open Spire Vault Laic Kennel Rush Fir Branch Tenant
open Pec Push.Uniform Planned.JetPort Drapes
section
open scoped Matrix.Norms.Frobenius
lemma woods(t:ℕ):∃ a:ℝ,0≤a∧∀ n:Side,EnvM t (represent (G:=group) (n:=More n)) 0 a:=by
 let U(x:CoreX):= group.mat (group.lieExp x)
 obtain ⟨a,h,H⟩:= exists_allows (f:=U) (isCompact_singleton (x:=(0:CoreX))) (fun x g=> by apply (Gauge.exp_jet group).contDiffAt) t
 refine ⟨composeCost t a 1,by unfold composeCost; positivity,fun n=>⟨fun i=>?_⟩⟩
 let V : Cloud n→L[ℝ] CoreX:= ContinuousLinearMap.proj (Channel.bondBody _ i); have hp: Allows t V 0 1:= allows_linear (V.opNorm_le_bound zero_le_one fun x=>by rw [one_mul]; exact norm_le_pi_norm x _) (by rw [map_zero,norm_zero]; norm_num)
 simp_rw [Work.F03.represent_link]; exact (H (V 0) (by rw [map_zero]; rfl)).comp hp
lemma hotCost(t:ℕ):∃ a:ℝ,0≤a∧∀ n:Side,∀ u:CoreX,‖u‖=1→ EnvM t (represent ∘ pour n u) 0 a:=by
 obtain ⟨a,h,Q⟩:= woods t; refine ⟨composeCost t a 1,by unfold composeCost; positivity,fun n u x=>⟨fun i=>?_⟩⟩; let V:= pour n u; have he(x':Air n):‖V x'‖≤‖x'‖:=by apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr; intro i; change ‖pill n x' i • u‖ ≤ _; rw [norm_smul,x,mul_one]; unfold pill; split; exact norm_le_pi_norm _ _; rw [norm_zero]; exact norm_nonneg _
 have ht:= allows_linear (n:=t) (V.opNorm_le_bound zero_le_one fun x=> by rw [one_mul]; exact he _) (by rw [map_zero,norm_zero]; norm_num); exact ((map_zero V).symm ▸ (Q n).ink i: Allows t (fun y: Cloud n=>group.mat (represent y i)) (V 0) a).comp ht
end
open scoped Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
lemma begC {N: Side}(r:ℝ)(p:0<r): ball (1:Chin N) r⊆ Openc (More N) r:=by intro x hx; refine ⟨1,guard0 p.le,?_⟩; rw [profile_trivial]; rw [mem_ball, dist_eq_norm] at hx; exact hx
lemma hol_proj(j:ℕ)(p:1≤j):∃ i:ℕ,∀ N:Side, i ≤N.val→ ∀ M: Male,ContDiffAt ℝ ω (spar j M ∘ represent (n:=More N)) 0:=by
 obtain ⟨h,c,W⟩:=woods 1; obtain ⟨C,v,V⟩:=plex 1 c; obtain ⟨a,b,r,ha,hb,hp,i,Q⟩:=funde_s j p
 refine ⟨i,fun N e M=>?_⟩; let B:= profile ∘ represent (n:=More N) (G:=group); let P:= funde j M N; have ht:= V (W N) link_one; have hm:Openc (More N) r ∈𝓝 (B 0):=by unfold B; rw [Function.comp_apply, link_one,profile_trivial]; exact Filter.mem_of_superset (Metric.ball_mem_nhds _ hp) (begC _ hp)
 have hx:=Q M N e; have hc:ContDiffAt ℝ ω P (B 0):=by
    refine tort.mpr ?_; intro i j; let f(x: Openc (More N) r):= P x.val i j; have he: Looks (Openc (More N) r) f:=hx.air i j; obtain ⟨R,M,h,k,V⟩:=hx; have hv:Continuous f:=by unfold f; simp_rw [show ∀ x : Openc (More N) r,P x.val i j=∑ S,R S x i j from fun x=>by rw [show P x.val=_ from V x,Matrix.sum_apply]]; exact continuous_finsetSum _ fun S _=>(h S).toTicket.cont.matrix_elem i j
    apply ((Jet.interiorC he hv (B 0) hm).restrictScalars (𝕜:=ℝ)).contDiffAt.congr_of_eventuallyEq; filter_upwards [hm] with i h; exact Eq.symm (dif_pos h)
 exact hc.comp (f:=B) _ ht.analytic
lemma sewn (n:Side)(u:CoreX)(x:Air n)(i:Edge (Site (More n)))(y:Air n)(h:x i.1=y i.1): represent (pour n u x) i=represent (pour n u y) i:=by simp_rw [Work.F03.represent_link]; apply congrArg group.lieExp; change pill n x _ • u= pill n y _ • u; unfold pill; rw [show x i.1=y i.1 from h] -- tune
lemma yokeL(n:Side)(u:CoreX):Yoke id (represent ∘ pour n u) id 1 :=by constructor; intro i j; simp; rintro x y i h; exact sewn n u x i y (h i.1 (by simp)) -- tune de
lemma certU(k j:ℕ)(p:1≤j):∃ a b:ℝ,0<a ∧ 0<b∧∃ i:ℕ,∀ N:Side,i≤N.val→∀ M:Male,∀ u:CoreX,‖u‖=1→HoldX id place_x (spar j M ∘represent ∘ pour N u) a b k:=by
 obtain ⟨C,v,H⟩:=hotCost k
 obtain ⟨B,h,D⟩:=plex k v; obtain ⟨a,b,r,ha,hb,hp,i,Q⟩:=funde_s j p; let s:= a/(k+1:ℝ); let W:=(1+(2:ℝ)^k/r)^k; let A:= composeCost k W B; have hs:0<s:=by unfold s; positivity
 have hA: 0<A:=by unfold A W composeCost; positivity
 obtain ⟨l,P⟩:=hol_proj j p; refine ⟨s,A*b,hs,mul_pos hA hb,max i l,fun N x M u w=>?_⟩
 let g:=profile (N:=More N) ∘represent ∘ pour N u; let T:= Openc (More N) r; have hF:g 0=1:=by unfold g; rw [Function.comp_apply,Function.comp_apply,map_zero,link_one,profile_trivial]
 let X:=spar j M ∘ represent ∘ pour N u; have hu:ContDiffAt ℝ ω X 0:= ((map_zero (pour N u)).symm ▸ P N ((le_max_right ..).trans x) M:ContDiffAt ℝ ω (spar j M ∘ represent) ((pour N u) 0)).comp _ (pour N u).contDiff.contDiffAt
 have hk: Allows k g 0 B:= D (H N u w) ((by unfold Function.comp; rw [map_zero,link_one]))
 refine ⟨hu, ledger (tort.mp hu) ?_,mul_pos hA hb⟩
 intro i' b'; let v:=place_x i'
 obtain ⟨R,U,H,C,E⟩:= Q M N ((le_max_left ..).trans x); let X'(S)(i:T):= R S i i' b'; let Z(S):= Jet.equalizer (X' S) ∘ g; let F(S):= U S i' b'; have hW:T∈𝓝 (g 0):=by rw [hF]; exact Filter.mem_of_superset (Metric.ball_mem_nhds _ hp) (begC r hp)
 let G:= g ⁻¹' T; have hx:G∈𝓝 0:= hk.analytic.continuousAt.preimage_mem_nhds hW
 have ht(S:Seal (Site (More N))): Allows k (Z S) 0 (A*F S):=by
    have hi: Looks T (X' S):=(H S).fuel i' b'; have hh:Continuous (X' S):=(H S).toTicket.cont.matrix_elem i' b'
    have he:Allows k (Jet.equalizer (X' S)) (g 0) (F S *W):=⟨(Jet.interiorC hi hh _ hW).restrictScalars.contDiffAt,(Jet.allows_looks hi hh (S:=T) (show ball (g 0) r⊆ T by rw [hF]; exact begC r hp) hp k ((H S).expo i' b').bounded).norm_le⟩; exact (he.comp hk).mono (le_of_eq (by unfold A composeCost; ring))
 let V(y: Single N):=Decay s (place_x i') (place_x y); have he(S):0≤ F S:=(H S).nonn _ _; have hg(S):Beacon id s k (Z S) (place_x i') 0 (A*(Branch.rent a S*F S)* V b'):=by
    by_cases h:F S=0; · intro t p i; exact (le_trans (entry_bound i) ((ht S).norm_le t p)).trans (by rw [h]; simp)
    obtain ⟨t,f,z⟩:= (H S).expo i' b'|>.triggered h; let v:=place_x i'; have hi:separation v (place_x b')≤ S.card:= (t.lim _ f _ z).le
    apply Beacon.mono (Allows.beacon (ht S) (r:=S.card) (s:=G) ?_ hx hs.le)
    · unfold Branch.rent V Decay; rw [show A * (Real.exp (a*S.card) *F S)* _= A*F S*(Real.exp (a*S.card)*Real.exp (-s*separation v (place_x b'))) by unfold v; ring]; rw [←Real.exp_add]; apply mul_le_mul_of_nonneg_left _ (mul_nonneg hA.le (he S)); apply Real.exp_monotone; have hk:s*(k+1:ℝ)=a:=by unfold s; field_simp
      push_cast; change _≤ a * _ + -s*_ ; have hq: (separation v (place_x b'):ℝ) ≤ S.card:=by exact_mod_cast hi
      nlinarith only [hk,congrArg (· * (S.card:ℝ)) hk,mul_le_mul_of_nonneg_left hq hs.le]
    intro x y u' hU hu; let x' : T:= ⟨_, (show g x ∈ T from y)⟩; let v':T:=⟨g u',hU⟩; change Jet.equalizer (X' S) (g x) = Jet.equalizer (X' S) (g u'); rw [show Jet.equalizer (X' S) (g x) = (X' S x') from dif_pos (show g x ∈ T from y),show Jet.equalizer (X' S) (g u') = X' S v' from dif_pos (show g u'∈ T from hU)]; apply sub_eq_zero.mp; apply norm_le_zero_iff.mp; apply ((H S).expo i' b'|>.variation x' v').trans; change _*(Tulip.fare S (g x) (g u') / _ )≤ _; unfold Tulip.fare; rw [sum_eq_zero]; simp; intro i l; have hL : x i.1=u' i.1:=hu i.1 (t.lim _ f _ (mem_filter.mp l).2.1).le; change ‖profile _ i-profile _ i‖=_; unfold profile; simp only [Function.comp_apply]; rw [sewn N _ _ i _ hL,sub_self,norm_zero]
 have hE : (fun i=>X i i' b')=ᶠ[𝓝 0] fun i=>∑ S,Z S i:=by
    filter_upwards [hx] with i h; let f:T:= ⟨g i,h⟩; change funde j M N f.val i' b'= _; rw [show funde j M N f.val=_ from E f,Matrix.sum_apply]; apply sum_congr rfl; intro S _; exact Eq.symm (dif_pos h)
 intro t p v'; unfold Push.Uniform.entry; rw [(hE.iteratedFDeriv ℝ t).eq_of_nhds]; apply (beacon_S (fun S _=>hg S) (fun S _=>((ht S).analytic.of_le le_top)) t p v').trans; apply mul_le_mul_of_nonneg_right _ (by positivity); simp_rw [← Finset.sum_mul,←Finset.mul_sum]; apply mul_le_mul_of_nonneg_right _ (by unfold V; exact (Push.Uniform.decay_pos ..).le); apply mul_le_mul_of_nonneg_left _ hA.le; exact (single_le_sum (fun j _=>sale_nn (fun S=>(H S).nonn) a i' j) (mem_univ b')).trans (C.rows _)
end YM.CF.Cascade
