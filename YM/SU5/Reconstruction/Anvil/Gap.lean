import YM.SU5.Reconstruction.Anvil.Lens
/-! # Margins and horizontal strip economy. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Anvil
open Function Set Filter Metric InnerProductSpace OS Semigroup Finset ConePrice
open scoped Topology InnerProductSpace NNReal ENNReal BigOperators Classical
variable {a: Axis} {K: Finset Axis} (x:Meter) (b:ℝ)
namespace Terrain
variable (P:Terrain a K)
section eager
local notation "C" i:max=> (P.P i)
local notation "c" i:max=> (P.first i)
variable (V : Festum (P.gap x) b)
local notation "F"=> raiseLens x b P V
lemma swept : ∀ᶠ T:ℝ in atTop,∀ z∈ Rim,∃ i:K, ((P.P i).extend T).permeates i.val (P.first i) (F z):= by
 let g (r:ℝ × ℂ) := ∃ i:K,((P.P i).extend r.1).permeates i.val (P.first i) (F r.2)
 have h:∀ᶠ r in ((atTop:Filter ℝ) ×ˢ 𝓝ˢ Rim),g r:= by
    apply (isCompact_sphere (0:ℂ) 1).mem_prod_nhdsSet_of_forall
    intro z hz; obtain ⟨i,h⟩:=P.arcScan x b V z hz; obtain ⟨T,v⟩:= (Price.entry_cost i.val (P.P i) (P.first i) (F z) h).exists
    let X:=((P.P i).extend T); have E:ContinuousAt F z:= continuousAt_pi.mpr (fun y=> P.expense x b V y z (sphere_subset_closedBall hz)); have M: ∀ᶠ ζ in 𝓝 z,X.permeates i.val (P.first i) (F ζ):= E.tendsto.eventually ((X.permeates_open ..).mem_nhds v)
    refine Eventually.mono ( (show ∀ᶠ r:ℝ × ℂ in (atTop:Filter ℝ) ×ˢ 𝓝 z,r.1 ≥ T ∧ X.permeates i.val (P.first i) (F r.2) from prod_mem_prod (eventually_ge_atTop T) M)) fun r p=> ⟨i,Price.charge_upwards _ (P.P i) T r.1 p.1 _ _ p.2⟩ -- tune
 exact h.curry.mono fun _ h=> h.self_of_nhdsSet
-- horizontal shift on boundary. strip with argument Clock s real carrier.
-- omit V
lemma still (a0 b:Axis)(x y:ℂ)(p:a0≠b)(e:x.im=y.im)(u:Wage)(Q:Price)(w:Bool)(q:Q.permeates a0 w (LedgerRide b u x)): Q.permeates a0 w (LedgerRide b u y):= by
 cases w <;> (first | (rw [(Price.window_syntax a0 Q _).2] at q ⊢) | (rw [(Price.window_syntax a0 Q _).1] at q ⊢)) <;> simpa only [LedgerRide,deeper_add,only_agree, Pi.add_apply,onlyTime,e, Pi.single_eq_of_ne p,add_zero] using q
lemma stratum : ∀ᶠ T:ℝ in atTop,∃ e>(0:ℝ),∀ z∈ Rim,∀ t∈ Sail.slit e,∃ i:K, ((P.P i).extend T).permeates i.val (P.first i) (LedgerRide a (F z) t):= by
 filter_upwards [P.swept x b V] with T h
 let G (t:ℝ)(z:ℂ) := ∃ i:K,((P.P i).extend T).permeates i.val (P.first i) (LedgerRide a (F z) ((t:ℂ)*Complex.I))
 have A(z:ℂ)(v:z∈ Rim):∀ᶠ p:ℝ × ℂ in 𝓝 ((0:ℝ),z), G p.1 p.2:= by
    obtain ⟨i,d⟩:= h _ v; let k(p:ℝ × ℂ):= LedgerRide a (F p.2) ((p.1:ℂ)*Complex.I)
    have D:ContinuousAt F z:= continuousAt_pi.mpr (fun i=>P.expense x b V i z (sphere_subset_closedBall v)); have E:k ( (0:ℝ),z)= F z:= by simp [k,LedgerRide,onlyTime]
    have e:Continuous (fun x:ℝ=> onlyTime a ((x:ℂ)*Complex.I)):= continuous_pi (fun j=>by by_cases q:j=a<;> simp [onlyTime,q]<;> fun_prop)
    have W:ContinuousAt k ((0:ℝ),z):= (ContinuousAt.comp (g:=F) D (continuous_snd.continuousAt (x:=((0:ℝ),z)))).add (e.continuousAt.comp continuousAt_fst)
    refine ( (show ∀ᶠ p in 𝓝 ((0:ℝ),z),((P.P i).extend T).permeates i.val (P.first i) (k p) from W.tendsto.eventually ((((P.P i).extend T).permeates_open ..).mem_nhds ?_))).mono fun _ h=>⟨i,h⟩
    rw [E]; exact d
 obtain ⟨e,v,h⟩:= Metric.eventually_nhds_iff.mp ((isCompact_sphere _ _).eventually_forall_of_forall_eventually A)
 refine ⟨e,v,fun i t p q=>?_⟩; obtain ⟨z,g⟩:= h (show dist p.im 0 < e from (by simpa [Real.dist_eq] using (show |p.im|<e from q))) i t
 exact ⟨z, still z.val a _ _ (P.enough z) (by simp) _ _ _ g⟩
end eager
end Terrain
-- j budgets always with positive time vs left regardless IM of the s argument
abbrev vertical (T u v:ℝ): Price:= ⟨T,0,u,0,v⟩
lemma up_test (T u v:ℝ) (z : Wage) (s:ℂ) :
    ((vertical T u v).permeates a true (LedgerRide a z s) ↔ 0<T ∧ ‖rimPay a (Deeper z)‖ < (z a).re + s.re -u ∧ ‖rimPay a (Deeper z)‖ < T-v-((z a).re+s.re)) ∧
    ((vertical T u v).permeates a false (LedgerRide a z s) ↔ ‖rimPay a (Deeper z)‖ < (z a).re+s.re+T ∧ ‖rimPay a (Deeper z)‖< -v-((z a).re+s.re) ∧ 0< T-u) := by rw [(Price.window_syntax a _ _).1,(Price.window_syntax ..).2]; simp [Price.compares,LedgerRide,only_agree,onlyTime]
-- reserve plot. Includes vertical budgets for all active candidates up to widths θ.
structure Umbrella (a:Axis) (x:Meter)(b T V m e: ℝ)(P:Terrain a K) extends Outlook a x b where
   pos: 0<V
   enough : V+1<T
   costly: 0<e
   overlay (z:ℂ)(hz:z∈Rim)(s:ℂ)(p:s∈ Sail.slit e): ∃ i:K, ((P.P i).extend T).permeates i.val (P.first i) (LedgerRide a (X z) s)
   horizon (z:ℂ)(h:z∈Pane)(s:ℂ)(u v:ℝ)(hu:u ≤ m)(hv:v≤m) :
       (s.re ∈ Set.Icc V (V+1) → (vertical T u v).permeates a true (LedgerRide a (X z) s)) ∧
       ( -s.re∈ Set.Icc V (V+1) → (vertical T u v).permeates a false (LedgerRide a (X z) s))
variable (P:Terrain a K)
lemma envelope (e:x a=0)(T:b^2< ∑ i:K,P.gap x i^2)(p:∀ i,0< P.gap x i) (m:ℝ)(hm:0≤m) : ∀ᶠ t:ℝ in atTop,∃ (U e:ℝ),Nonempty (Umbrella a x b t U m e P) := by
 obtain ⟨B⟩ := put_in_place (P.gap x) b T p
 let F:=P.raiseLens x b B; have hv(z:ℂ)(p:z∈Pane):ContinuousAt F z:= continuousAt_pi.mpr (fun i=>P.expense x b B i z p); let H(z:ℂ):ℝ:= |(F z a).re| + ‖rimPay a (Deeper (F z))‖
 obtain ⟨u,uB,Bv⟩:= (isCompact_closedBall (0:ℂ) 1).exists_isMaxOn (s:=Pane) (nonempty_closedBall.mpr zero_le_one) (f:=H) (fun z b=> ContinuousAt.continuousWithinAt ((Complex.continuous_re.continuousAt.comp ((continuousAt_pi.mp (hv z b)) a)).abs.add (((c_r a).continuousAt.comp (c_y.continuousAt.comp (hv z b))).norm))) -- tune
 have M(z:ℂ)(p:z∈Pane): H z ≤ H u:= Bv p; let R:=H u + m + 2; have v:0<R:= by unfold R H; positivity
 filter_upwards [P.stratum x b B,eventually_gt_atTop (2*R+1)] with t h ht
 obtain ⟨k,e',w⟩:=h; refine ⟨R,k,⟨{ X:=F, atSpot:=P.makesLens x b B e, life:=hv,pulse:= P.totals x b B, pos:=v, enough:= by linarith, costly:=e', overlay:= w, horizon:= ?_ }⟩⟩ -- struct expects Nonempty
 intro z zP s u v hU hV -- shadow
 obtain ⟨X,Y⟩:= up_test t u v (F z) s (a:=a); let p0:=M z zP; unfold R H at *
 refine ⟨fun i=> X.mpr ⟨by linarith,by linarith [i.1,neg_le_abs (F z a).re,le_abs_self (F z a).re],by linarith [i.2,neg_le_abs (F z a).re,le_abs_self (F z a).re]⟩,fun i=> Y.mpr ⟨by linarith [i.2,neg_le_abs (F z a).re,le_abs_self (F z a).re],by linarith [i.1, le_abs_self (F z a).re],by linarith [p0,abs_nonneg (F z a).re, norm_nonneg (rimPay a (Deeper (F z)))]⟩⟩
end YM.Anvil
