import YM.CF.Laic.Tan
set_option autoImplicit false
noncomputable section
namespace YM.CF.Laic
open Function Filter Metric Lattice Wilson Laurent Precision Tree Finset Exterior Extra Bloch Lat Rush Cube Scroll SU Peaks Dial Fock Thera Nacre Branch Drapes Tulip Paige Spire Vault Font Kennel Planned.JetPort Push.Uniform
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix MatrixOrder Kronecker Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
variable {n N:Side}{k:ℕ}{T:RG.StepData (More n) (More N)}(F: Forest T.ratio)(G:Ratio n N){a b d:ℝ}
abbrev lookM (G:Ratio n N):Iota G→Site (More N):= place_x ∘ switchG G
lemma hatScore(k:ℕ):∃ A:ℝ,0≤A∧∀ {m n:Side}{T:RG.StepData (More m) (More n)}(F: Forest T.ratio), Allows k (unionP ∘ hats F) 0 A:=by
 obtain ⟨B,hb,H⟩:=hatch k; obtain ⟨C,hc,U⟩:=plex k hb; refine ⟨C,hc,fun F=>?_⟩; exact (U (H F).1 (congrArg Prod.fst hats0)).pair (U (H F).2 (congrArg Prod.snd hats0))
abbrev clothH (T:RG.StepData (More n) (More N)) (F:Forest T.ratio):Push.Uniform.Joint F SU.group→ Site (More N):=Push.Uniform.address F group
lemma rock (h:T.ratio= ratio G)(u v:Snap F)(S:Seal (Site (More N)))(x:Iota G)(p:(tempo G a).home x ∈S)(g:Grove (Tenant.terr _) S)(w:together (clothH T F) (lookM G x) (S.card+G.count.val) u v): deal G S (unionP (hats F u)) (unionP (hats F v))=0:=by
 let A:=ratio G
 unfold deal
 have hx : Tulip.fare S (profile (fine group F u)) (profile (fine group F v))=0:=by unfold Tulip.fare; refine Finset.sum_eq_zero fun i hv=>?_ ; rw [sub_eq_zero.mpr (show profile (fine group F u) i=profile (fine group F v) i by unfold profile; rw [fine_read F w i ?_]; exact le_trans (Nat.add_le_add_right (show separation (lookM G x) i.1 ≤ _ from (g.lim _ p _ (mem_filter.mp hv).2.1).le) T.ratio.count.val) (le_of_eq (by rw [h]; rfl))), norm_zero]
 simp only [unionP,hats,hx,zero_add]; unfold Tulip.fare; refine Finset.sum_eq_zero fun i hv=>?_ ; rw [sub_eq_zero.mpr (show profile (outer group F u) i=profile (outer group F v) i from ?_), norm_zero]; unfold profile; rw [co_read F w i ?_] -- tune
 rw [h]; exact le_trans (show separation (lookM G x) _≤ S.card from (g.lim _ p _ (mem_filter.mp (mem_filter.mp hv).2.1).2).le) (Nat.le_add_right ..)
-- coordinate extraction each paid analytic term
lemma sphere_cost(k:ℕ)(C:ℝ){d:ℝ}(p:0<d)(g:0≤C):∃ A:ℝ,0<A∧∀ {n M:Side}{T:RG.StepData (More n) (More M)}(F:Forest T.ratio)(G:Ratio n M)(x: legal G d→ℂ), Continuous x → Looks (legal G d) x→ ∀ a:ℝ,(∀ f,‖x f‖≤a)→ Allows k (fun y=> Jet.equalizer x (unionP (hats F y))) 0 (A*a):=by
 obtain ⟨u,h,H⟩:= hatScore k; let W:= (1+(2:ℝ)^k/d)^k; refine ⟨composeCost k W u,by unfold W composeCost; positivity,fun {n M T} F G x v w a y=>?_⟩
 let f(v:Snap F):= unionP (hats F v); have he:=H F; have hf: f 0=1:=by simp only [f,hats0,unionP, Prod.fst_one,Prod.snd_one]; change (profile (1:Bkg _),profile (1:Bkg _))= _; simp [profile_trivial]
 have ht:Metric.ball (f 0) d ⊆ legal G d:=by
    intro i hi; have hz:= (near_j G d p).self_of_nhds; rw [Metric.mem_ball,dist_eq_norm] at hi; exact ⟨1,hz,by rwa [← hats0 (F:=F)]⟩ -- fold f
 have hh: Allows k (Jet.equalizer x) (f 0) (a*W):= ⟨(Jet.interiorC w v _ (mem_of_superset (Metric.ball_mem_nhds _ p) ht)).restrictScalars.contDiffAt,(Jet.allows_looks w v ht p k y).norm_le⟩
 exact (hh.comp (f:=f) he).mono (le_of_eq (by unfold composeCost; ring))
lemma creed(k:ℕ)(p:0<a)(v:0<b)(t:0<d)(L:Side):∃ c e:ℝ,0<c∧0<e ∧∀ {n M:Side}{T:RG.StepData (More n) (More M)}(F:Forest T.ratio)(G:Ratio n M), T.ratio=ratio G→ G.count=L→ ∀ U:Coil n M→ Op (Iota G),∀ r s:Bool, Crown (badge (legal G d)) (Peaks.parcel G r d) (Peaks.parcel G s d) a b (fun x=> U x.val)→ ContDiffAt ℝ ω (U∘ unionP ∘ hats F) 0∧ CableM (clothH T F) (lookM G) (lookM G) c k (U ∘ unionP ∘ hats F) 0 e:=by
 obtain ⟨C,hc,H⟩:= sphere_cost k b t v.le; let c:=a/(k+1:ℝ); have hz:0<c:=by unfold c; positivity
 let A:= C*Real.exp (c*(k*L.val:ℕ)); have hA:0<A:=mul_pos hc (by positivity); refine ⟨c,A*b,hz,mul_pos hA v,fun {n N T} F G he hv U r s p'=>?_⟩
 obtain ⟨B,hb,X⟩:=hatScore k; let f:Snap F→ Coil n N:= unionP ∘ hats F; have hh:legal G d∈𝓝 (f 0):=by apply (Peaks.cabin ..).mem_nhds; rw [show f 0=unionP (hats F 0) from rfl,hats0]; exact ambient _ _ t le_rfl (near_j G d t).self_of_nhds
 have hp:= (crown_air G p' (f 0) hh).comp (f:=f) 0 (X F).analytic; refine ⟨hp, ledger (Nacre.tort.mp hp) ?_⟩
 intro i j; obtain ⟨P,Q,Ht,hq,hE⟩:=p'
 let C'(S):= A*Branch.rent a S*Q S i j; let T'(S:Seal (Site (More N)))(x: legal G d):= P S x i j; let Z(S):=Jet.equalizer (T' S) ∘ f; let Y:=lookM G i; let u:= Decay c Y (lookM G j)
 have hw(S:Seal (Site (More N))): Allows k (Z S) 0 (C*Q S i j):= H F G (T' S) ((Ht S).expo i j).connected ((Ht S).fuel i j) _ ((Ht S).expo i j).bounded
 have hy(S): Beacon (clothH T F) c k (Z S) Y 0 (C' S*u):=by
    let B:=Q S i j; have hm:= (Ht S).expo i j; by_cases h:B=0; · intro t p v; refine ((entry_bound v).trans ((hw S).norm_le t p)).trans (le_of_eq ?_); change C*B=A*_ * B*_ * _; rw [h]; ring
    obtain ⟨ha,he',hq⟩:=hm.triggered h; have hu:=ha.lim _ he' _ hq; apply Beacon.mono (Allows.beacon (r:=S.card+G.count.val) (s:= f ⁻¹' legal G d) (hw S) ?_ ((X F).analytic.continuousAt.preimage_mem_nhds hh) hz.le)
    · unfold C' A u Push.Uniform.Decay Branch.rent; let v:= separation Y (lookM G j); change _≤ _*_*Real.exp (-c*v)
      have hx:(v:ℝ)≤ S.card:=by exact_mod_cast (show v ≤ S.card from hu.le)
      have hk:c*((k:ℝ)+1)=a:=by unfold c; field_simp
      have hh: c*(k*(S.card+G.count.val):ℕ)≤ c*(k*L.val:ℕ)+a*S.card+(-c*v):=by push_cast; rw [hv]; nlinarith only [hx,hz,hk, mul_le_mul_of_nonneg_left hx hz.le, congrArg (· * (S.card:ℝ)) hk]
      apply (mul_le_mul_of_nonneg_left (Real.exp_monotone hh) (show 0≤C*Q S i j from mul_nonneg hc.le hm.positive)).trans_eq; simp only [Real.exp_add]; ring
    intro i hi j hj hx; change (Z S i)=Z S j; unfold Z Function.comp; rw [show Jet.equalizer (T' S) _ =_ from dif_pos (show f i∈_ from hi), show Jet.equalizer (T' S) (f j)= _ from dif_pos (show f j∈_ from hj)]; apply sub_eq_zero.mp; apply norm_le_zero_iff.mp; apply (hm.variation _ _).trans; rw [show (tempo G d).eval _ _ _=0 from ?_]; simp; change deal G S (unionP (hats F i)) (unionP (hats F j)) / _=0; rw [rock _ _ he i j S _ he' ha hx,zero_div] -- tune shadow
 intro k' hk v; have hR : (fun x:Snap F=>U (f x) i j) =ᶠ[𝓝 0] (fun x=>∑ S,Z S x):=by
    filter_upwards [(X F).analytic.continuousAt.preimage_mem_nhds hh] with x hx; change f x∈legal G d at hx; rw [show U (f x)=_ from hE ⟨_,hx⟩,Matrix.sum_apply]; exact sum_congr rfl fun i _=> (by change T' i ⟨_,hx⟩ = Jet.equalizer (T' i) (f x); exact Eq.symm (dif_pos hx))
 have hg(i j):0 ≤ ∑ S,Branch.rent a S*Q S i j:= sum_nonneg fun i _=> mul_nonneg (Real.exp_pos _|>.le) ((Ht _).nonn _ _); have hh : Beacon _ c k (fun x=>∑ S,Z S x) Y 0 ((∑ S,C' S*u)):=beacon_sum (fun S _=>hy S) (fun S _=>(hw S).analytic)
 change ‖iteratedFDeriv ℝ k' (fun x=> U (f x) i j) _ _‖≤ _; rw [(hR.iteratedFDeriv ℝ k').eq_of_nhds]; refine ((hh _ hk v).trans ?_); apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _|>.le); unfold C'; rw [←Finset.sum_mul]; simp_rw [mul_assoc A,←Finset.mul_sum]; rw [←mul_assoc A b]; apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _|>.le); apply mul_le_mul_of_nonneg_left _ hA.le; exact (single_le_sum (fun j _=>hg i j) (mem_univ j)).trans (hq.rows i)
end YM.CF.Laic
