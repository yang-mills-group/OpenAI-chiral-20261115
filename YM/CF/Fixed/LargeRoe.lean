import YM.CF.Fixed.LargeClock
import YM.CF.Mint.Dace
/-!
Larger **finite-window** estimates. Generalization of the actual Roe.echo &
Roe.costR etc proofs to the needed volume hypothesis. Keep API near verbatim
at many steps (cf Mint/{Nove,Boom,Rate,Locket,Cash,Dace}). All entries in
both normalized denominator and matter readings use this same state. Size
hypothesis NOT in terms of log x allocations internal to budgets! Rates still
paid in its schedules; do not change T.p. Foresee/Later derives in fixed-x
window after changing the weak x→∞ path estimates, and tests there. Still
missing genuinely fixed-x thermodynamic control.
-/
set_option autoImplicit false
noncomputable section
namespace YM.CF.Mint
open Function NormedSpace Filter Finset Graph Lattice Laurent Wilson Analysis Pressure Tulip Lat Cube SU Emu Rush Scree Graph RG Scroll Peaks Drapes Cascade Vault Sods Spire Paige Nova Girt Skye Kea Ember
set_option synthInstance.maxSize 24000
set_option maxHeartbeats 500000
open scoped Topology ContDiff InnerProductSpace BigOperators Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
variable {x y A:ℕ→ℝ}{c b w η r a e K b' v C' l s' γ μ τ H m L':ℝ}{S T:ℕ→Side}{β θ V L1 δ L:ℕ→ℝ}{J B:Side}{O:Odd J.val}{j k:ℕ}{Y:Pricing j J O (Thread j)}{P:Grasp Y B e}{hP:Pearl P}
-- nonuniform sequences. loop exponent update tracks budget. 
namespace RoeWL
open Roe Fixed.Extensive
variable {N:ℕ→Side} (D:Pic.Span hP K b' v C' l s' k) {I:∀ i,GramM (mid (N i) B)} {C Q h:ℝ}
local notation "NP"=> (fun i=> mid (N i) B)

open MeasureTheory Gall Pastry Fock
structure WidthK {P:Grasp Y B e} (w C L T R γ h:ℝ)(H H':ℝ) : Prop where -- H is factor in front of vast, H' is charge (`T` is Haar price, `R` is angelLower; last h is rope mass). Keep both milestones.
  posZ:0<w
  bound : H ≤ penaltyK w (borderK C L R T (saltBudget w) γ H')
  heat : 0<H
  unitC:0 ≤ C
  bill:1 ≤ T
  salt (x:ℝ)(v:0<x) : ∫ U:SU.E,saltWeight group x (saltBudget w) U∂group.probHaar ≤ T*shellMass group x
  plant (m:Side)(S:Kea.Pad j (mid m B))(p:P.roundZ≤ (mid m B).val)(M:Jill.Male): Real.exp (-(↑(mid m B).val:ℝ)^4*R) ≤ Kea.angel m P M
  rope:1 ≤ h
-- reduce dependencies structural
lemma issue (P:Grasp Y B e) (he:0<e) (hZ:1≤j) (w C L' γ h:ℝ)(F':ℝ)(p:0<w)(u:0≤C)(t:1≤h):∃ T R H:ℝ,WidthK (P:=P) w C L' T R γ h H F' := by
  obtain ⟨C',pA,A⟩:= pay_angel P he hZ; obtain ⟨D,hD,G⟩:= salt_pay group (saltBudget w) (div_pos p (by norm_num)); exact ⟨D,C',_,p,le_rfl,penalty_pos p _,u,hD,G,fun _ q g M=> A _ g q M,t⟩
variable {Lr T' R F_A:ℝ}
structure Wide (Z:WidthK (P:=P) w C L' T' R γ h H F_A) (Lr μ r:ℝ)(V θ x:ℕ→ℝ)(I:∀ i,GramM (mid (N i) B)): Prop where
  path:Mint.RangeH x (fun i=>(I i).beta) (1/2) 2
  vol: ∀ᶠ i in atTop, (eur (fun i=>mid (N i) B) i)^4 ≤ H*vast x i
  tend:Tendsto (eur (fun i=>mid (N i) B)) atTop atTop
  loc:Aqua (eur (fun i=>mid (N i) B)) V
  dark:∀ᶠ i in atTop,V i≤ F_A ∧ θ i≤ F_A
  wind:0<r
  row:0≤L'
  support: ∀ᶠ i in atTop, let W:=I i; let T:= W.p
                    T.threshold=tame x i ∧ Ledger h (V i) (θ i) r C W ∧ W.path.Bounds W.funds μ L' Lr ∧ w≤ W.funds.linear ∧W.funds.direct ≤γ ∧ 0≤V i
variable (X':WidthK (P:=P) w C L' T' R γ h H F_A) (Z: Wide X' Lr μ r V θ x I)
include Z

lemma stageGrants : Gray (vast x) (eur NP) := by
  refine ⟨H,X'.heat,1,Z.vol.mono fun i p=>?_⟩; rw [Real.norm_eq_abs,abs_of_pos (show 0<eur NP i from nPos (NP i)),pow_one]; have he: 1≤eur NP i:= by unfold eur; exact_mod_cast (NP i).property
  exact le_trans (by simpa using pow_le_pow_right₀ he (by decide : 1 ≤ 4)) p
lemma stageMore : Gray (vast x) (eur (fun i=>More (NP i))) := by
  apply Gray.eqK ((stageGrants X' Z).mul (Gray.coef (vital Z.path.rank) 2)); exact Eventually.of_forall fun i=>by change eur NP i* 2= _; unfold eur; simp [More]
include D
lemma caesar:∃ T:ℕ→ℝ,Aqua (eur NP) T∧∀ᶠ i in atTop,CoolR D (N i) (T i) (I i).p.threshold:=by
 obtain ⟨u,b,t,p,Q'⟩:= manyK (B:=B)
 let S:= tame x; let E:=eur NP; let M:= fun i=>More (NP i); let y(i):=eur M i^2 * (tame x i) * b⁻¹
 have hV := Z.vol; let W:= Z.path; have hx : Aqua E y:=by
    have he:= vital W.rank; exact (((Aqua.fed (vast_temp W.rank) ((stageMore X' Z).powG he 2) he).pays (Gray.coef he b⁻¹) he).through he (stageGrants X' Z))
 have hz:∀ᶠ i in atTop,0<y i:= W.infl.mono fun i h=>by unfold y; have hp:=h.2.2.1; have hv:0<eur M i:=nPos (M i); positivity
 obtain ⟨e,A⟩:= rootA Z.tend hx hz t; let T :=fun i=> y i ^ ((u:ℝ)⁻¹)
 have hp:=A 10; let B1:= b'/(2 * poseX); have hC:=D.pos; have hX:0<B1:=by unfold B1; have he:=pose_p; positivity
 refine ⟨T,A,?_⟩; filter_upwards [Z.tend.eventually_ge_atTop k,e,A.shrinks.eventually (ge_mem_nhds one_pos), hp.eventually (ge_mem_nhds (lt_min D.xP one_pos)), (hp.const_mul C').eventually (ge_mem_nhds (by simpa using hX : C'*0< B1)),Z.support,W.infl] with i hi ⟨v,e⟩ t x a w u'; refine ⟨v,t,Nat.cast_le.mp hi,x,?_,fun U g=>?_⟩; -- tune shadow
 · unfold duty; rw [zero_mul,add_zero,mul_assoc]; exact a
 apply Q' _ U (I i).p.threshold (T i) ((I i).p.threshold_pos) g v t; rw [show T i^_ = _ from e,w.1]; unfold y eur M; rw [mul_comm b, inv_mul_cancel_right₀ p.ne']
omit D
lemma teal:Aqua (eur NP) (bloom NP r x):=by
 let A:=eur NP; have hx:= vast_temp Z.path.rank; have h:= hx.through (vital Z.path.rank) (stageGrants X' Z); have he:=Z.wind; let f(i):= Real.exp (-(r*eur (More∘NP) i)); refine Aqua.panel h (Aqua.fed (F:=f) ?_ (Gray.coef Z.tend 2) Z.tend); exact (Aqua.exp_neg Z.tend r he).clip Z.tend (Eventually.of_forall fun i=> by refine ⟨(Real.exp_pos _).le,Real.exp_le_exp.mpr ?_⟩; rw [neg_mul]; apply neg_le_neg; gcongr; unfold eur; exact_mod_cast (show (NP i).val ≤ ((More∘NP) i).val from Nat.le_mul_of_pos_right _ (by change (0:ℕ)<2; decide))) -- tune
lemma surge (k:ℝ): let M:=NP; let G:=bloom M r x; Aqua (eur M) (fun i=> baton (M i) (V i) (G i) C k)∧ (∀ᶠ i in atTop, pittance (M i) (G i) C ≤1∧ 0 ≤ G i):=by
 intro M G; let F:=Aqua (eur M); have h:Aqua (eur M) G:= teal X' Z; have he:= Z.tend; let H:= fun k=>Gray.coef he k; have hx:=vast_temp Z.path.rank
 have hb :∀ᶠ i in atTop,0 ≤ G i:= Z.path.infl.mono fun i v=> (v.2.2.1.trans_le (le_add_of_nonneg_right (by positivity))).le
 have hp : Gray (eur M) (eur M):=Gray.arg he; have hu:Aqua (eur M) (fun i=> G i ^2) := by simpa [sq] using (h.pays (Gray.thin he h.shrinks) he)
 let L(i):= pittance (M i) (G i) C; have ht:Aqua (eur M) L:= ((hu.pays (H C) he).pays (hp.powG he 4) he)
 have hw:Gray (eur M) (fun i=> lark (M i)):= (H 180).mul (hp.powG he 4)
 let X(i):= doorF (M i) (G i) C; have hg:Aqua (eur M) X:= Aqua.fed (Aqua.fed ((by
   show Aqua (eur M) (fun i=> (G i + G i^2)*C); exact ((h.panel hu).pays (H C) he))) (H 45) he) hw he
 let U(i):=axle (M i) (V i)+X i*lark (M i)^2*k^2; have hl:Aqua (eur M) U:=by
    have hy : Gray (eur M) (eur (More ∘ M)):=by apply Gray.eqK (hp.mul (H 2)); exact Eventually.of_forall fun i=>by change eur M i*2=eur (More ∘ M) i; unfold eur; norm_num [More]
    exact Aqua.panel ((Z.loc.panel Z.loc).pays (hy.powG he 4) he) ((hg.pays (hw.powG he 2) he).pays (H _) he)
 have hL:Tendsto (fun i=>Real.exp (L i)) atTop (𝓝 (Real.exp 0)):= (Real.continuous_exp.continuousAt.tendsto.comp ((show Aqua (eur M) L from ht).shrinks)); have hz: ∀ᶠ i in atTop,0≤U i:=by
    filter_upwards [Z.support,hb] with i ℓ p; have hg:=ℓ.2.2.2.2.2; have hx:=X'.unitC; unfold U axle X doorF lark; positivity
 exact ⟨Aqua.panel ((show Aqua (eur M) L from ht).fed (H 2) he) (Aqua.fed (Aqua.rise hl he hz) (Gray.thin he hL) he),(ht.shrinks.eventually (ge_mem_nhds one_pos)).and hb⟩ -- infer ht issue

include D
-- minTitle grants for state.
-- abbrev dowN (i:ℕ) : ℝ := lowerBook (NP i) (hemp x i) (stoutY (More (NP i)) (I i).beta (4*hemp x i) γ (tame x i) L' Lr) R  -- omit/ include? Q
local notation "ζ_" => saltBudget w
set_option quotPrecheck false
local notation "X_" i:max => stoutY (More (NP i)) (I i).beta (4*hemp x i) γ (tame x i) L' Lr
local notation "Y_" i:max => (chargeE (NP i) (V i) (θ i) C+flagTitle (More (NP i)) ζ_ (I i).p.threshold (I i).beta w L' Lr)
-- Exact estimate of leftover expenses
lemma lower_support : ∀ᶠ i in atTop, lowerBook (NP i) (hemp x i) (X_ i) R ≤ drip (I i) P∧ 0< Graph.angle (I i) ∧ 0<drip (I i) P:=by
  filter_upwards [Z.path.helm,Z.support,Z.path.infl,Z.tend.eventually_ge_atTop k] with i ⟨z,p,h⟩ ⟨e,T,U,u,w,_⟩ ⟨g,v,hζ,d⟩ l; let n:=NP i; let G:=drip (I i) P; rw [←e]; rw [←e] at h; obtain ⟨A,B'⟩:=D.plan _ (Nat.cast_le.mp l); have hp:=X'.plant (N i) B' A (I i).J.M; obtain ⟨ht,hv⟩:= drip_title (I i) U z h p w Z.row v.le (bonB T U) hp; refine ⟨ht,?_,hv⟩; have he:=shell_angle (bonB T U) U z.le h w v.le Z.row; have hz:=shellMass_pos group z p; exact lt_of_lt_of_le (by positivity) he
lemma touch : ∀ᶠ i in atTop,0<Graph.angle (I i) ∧0<drip (I i) P:=(lower_support D X' Z).mono fun _ p=>p.2
lemma guardedRatio : Aqua (eur NP) fun i=> upperBook (NP i) (hemp x i) T' (Y_ i)/drip (I i) P:=by
  have hX' := X'.posZ; have hg:0<T':=zero_lt_one.trans_le X'.bill
  have hY:0≤γ:=by obtain ⟨i,p⟩:= Z.support.exists; exact (I i).funds.quadratic_pos.le.trans p.2.2.2.2.1
  refine ((Aqua.exp_neg (vital Z.path.rank) (w/8) (by positivity)).through (vital Z.path.rank) (stageGrants X' Z)).clip Z.tend ?_
  filter_upwards [Z.path.helm, Z.path.infl, lower_support D X' Z,Z.support, barred Z.path X'.posZ V θ F_A Z.dark γ L' ζ_ T' R Lr C hY,Z.vol] with i ⟨p,h,u⟩ v ⟨w,hp,hv⟩ ⟨κ,A,hB,B,r,t⟩ he hu; let N:=NP i; have hz:= upperBook_pos (Y_ i) T' hg p h N; have hl:= lowerBook_pos (X_ i) R p h N -- h shadow
  refine ⟨div_nonneg hz.le hv.le,?_⟩; apply le_trans (div_le_div_of_nonneg_left hz.le hl w); apply le_trans (comparison T' R _ _ _ p h X'.bill N); apply Real.exp_le_exp.mpr; rw [κ]; exact he N (hu.trans (mul_le_mul_of_nonneg_right X'.bound v.2.2.2.le))

section marks
variable {d vA r₀ C₀ E':ℝ}{n₀:ℕ} (F:Port D d E' C₀ vA r₀ n₀)(g:C₀ ≤h)
lemma flagK (F:Port D d E' C₀ vA r₀ n₀):∀ᶠ i in atTop,(I i).p.threshold≤ r₀:= (Z.support.and ((damp Z.path.rank).shrinks.eventually (ge_mem_nhds F.pit))).mono fun _ h=>le_trans h.1.1.le h.2
include F g
lemma shot {α:Type*}(T:∀ i,Opt (α:=α) (NP i))(X:∀ i,Loom (NP i))(U:∀ᶠ i in atTop,SkinT (I i) (X i) e)(H:Charge α NP T) : Aqua (eur NP) fun i=> phM (I i) (T i) P (X i) /drip (I i) P:=by
 let S:=NP; let R:=eur S; let V'(i):= bloom S r x i; let W(i):= baton (S i) (V i) (V' i) C d; let B'(i):= lite (T i); let R'(i):= upperBook (S i) (hemp x i) T' (Y_ i)
 have he:= Z.tend; obtain ⟨Wk,Wb⟩:= RoeWL.surge X' Z d; obtain ⟨n,p⟩:=H.art; have hp:Gray R R:= Gray.arg he
 have hv:Gray R B':= (((hp.powG he 2).powG he n)).eqK (p.mono fun i t=>by change (R i^2)^n=B' i; rw [←t])
 have hu:Gray R (fun i=>feeP (T i) d):= ((((Gray.coef he (d*180)).mul (hp.powG he 6)).powG he n).eqK (p.mono fun i t=>by change (d*180*R i^6)^n=_; rw [←t]; rfl))
 have hl: Aqua R (fun i=> W i * E' * feeP (T i) d):=(Wk.pays (Gray.coef he E') he).pays hu he
 have hL:Aqua R (fun i=> B' i * (R' i/drip (I i) P)):= (Aqua.fed (guardedRatio D X' Z) hv he) -- tune explicit
 refine (hl.panel hL).clip he ?_; obtain ⟨Q,A,QF⟩:= RoeWL.caesar D X' Z
 filter_upwards [RoeWL.touch D X' Z,Z.support,QF,RoeWL.flagK D X' Z F,U,Wb,H.paid,Z.tend.eventually_ge_atTop (n₀:ℝ), Z.path.infl, ((A 10).eventually (ge_mem_nhds F.knot)),Z.path.helm, weather Z.path X'.posZ (fun i=>(I i).funds) (Z.support.mono fun i p=>p.2.2.2.1)] with i ⟨u,p⟩ ⟨X'_,J,gx,hQ,w',v⟩ q fU Xh ⟨a,v'⟩ hO hn ht hi ⟨hS,pT,ph⟩ ⟨f,he_,hW⟩
 let n:= S i; have ht':n₀≤ n.val:=(Nat.cast_le.mp hn); have hm(T: Orbit (S i))(p:T∈ Lace (I i)): flags ((I i).p.threshold) T.1=∅:= p
 let F':= phM (I i) (T i) P (X i); have hf: 0 ≤ F':= integral_nonneg fun x=>norm_nonneg _; have hg:= F.sap
 refine ⟨div_nonneg hf p.le,?_⟩; apply (div_le_iff₀ p).2
 have ha:T i=T i:=rfl
 refine le_trans (dampened_book (I i) (X i) D Xh J gx Z.wind.le X'.rope hS he_ (X'_.symm ▸ hW) (div_pos X'.posZ (by norm_num)) ht.2.1.le X'.posZ.le hQ _ (X'.salt _ hS) (F.site.trans ht') F.sap.le v' X'.unitC F.lark.le ?_ ?_ ?_ a (T i) hO) ?_
 · intro w t; obtain ⟨f,d,gT,h⟩:=q.roll w.1 t; exact F.wear (N i) ht' w.1 _ _ _ (Q i) (spiral _ gT) q.pose q.data hi h
 · intro w t j; have he: flags r₀ w.1=∅:=by
      apply Finset.eq_empty_iff_forall_notMem.mpr; intro i p; obtain ⟨x,u,v⟩:= (flags_spec ..).mp p; have hp:= t; change flags _ w.1=∅ at hp; exact notMem_empty _ (hp ▸ (flags_spec ..).mpr ⟨x,u,fU.trans_lt v⟩) -- tune
   exact (F.draw n ht' w.1 he _ _).weigh g F.sap.le
 · intro w t; have hx:=tile_p w.1 (show 0 ≤ tame x i from ht.2.2.1.le) Z.wind.le (show _ from (by rw [← X'_]; exact t)); exact hx
 apply le_of_eq; change _= (W i*E'*feeP _ d + B' i *(R' i/drip (I i) P))*drip (I i) P; unfold W V'; rw [add_mul, mul_assoc (B' i),div_mul_cancel₀ _ p.ne']; ring -- tune More


end marks
variable (F:∀ i,Loom (mid (N i) B)) (W:∀ᶠ i in atTop,SkinT (I i) (F i) e) {d vA r₀ C₀ E':ℝ}{n₀:ℕ} (U:Port D d E' C₀ vA r₀ n₀)(g:C₀ ≤h)

include W U g
lemma wageK: Aqua (eur NP) fun i=> ‖denQ (P:=P) (I:=I) F i -Graph.start (I i) P (F i)‖/drip (I i) P:=by
 let O(i):= tOpt (NP i); have hh: Charge Empty NP O:=⟨⟨0,Eventually.of_forall fun i=>rfl⟩,Eventually.of_forall fun i=>by simp [O,tOpt,Emu.gain]⟩
 refine (shot D X' Z U g O F W hh).clip Z.tend ?_
 filter_upwards [W,Z.support,touch D X' Z,Z.tend.eventually_ge_atTop k] with i p ⟨x,y,h,t⟩ ⟨u,q⟩ v; refine ⟨by positivity,?_⟩
 obtain ⟨A,B⟩:=Graph.integrable_s (I i) _ D p (bonB y h) (O i) (Nat.cast_le.mp v); obtain ⟨X,Y⟩:=porx (P:=P) (I:=I) F i; refine div_le_div_of_nonneg_right ?_ q.le; rw [←X,← Y,← integral_sub A B]; exact norm_integral_le_integral_norm _
lemma costR: let c:=b'/(2*Nova.poseX); let t(i):= facing (I i) P (F i)
 (∀ᶠ i in atTop, Integrable (denZ (I i) P (F i)) (city _) ∧ 0 <Graph.angle (I i) ∧0<drip (I i) P∧ drip (I i) P * (c/2) ≤ (t i).re ∧ (t i)≠0∧ (t i).re >0 ∧ ‖denQ (P:=P) (I:=I) F i‖≥(drip (I i) P)*(c/2) ∧partitionZ (I i) P (F i) ≠0)∧ Aqua (eur NP) fun i=> |(t i).im| / drip (I i) P:=by
 intro c t; obtain ⟨T,V,v⟩:= caesar D X' Z; let R(i):= gleam (N i) P (I i).J.M; let a(i):=drip (I i) P; let G(i):=Graph.start (I i) P (F i); let D'(i):= R i*G i; let S:= denQ (P:=P) (I:=I) F
 have hc:0<c:=by unfold c; have ht:=D.pos; have he:= pose_p; positivity
 let Q(i):= ‖S i-G i‖/a i; have hA:Aqua (eur NP) Q:= wageK D X' Z F W U g; let Y(i):= duty (eur NP i) (T i) C' 0; have ht:Aqua (eur NP) Y:=by unfold Y duty; simp only [zero_mul,add_zero]; exact V.fed ((Gray.coef Z.tend C').mul ((Gray.arg Z.tend).powG Z.tend 10)) Z.tend
 have hx:∀ᶠ i in atTop, a i*c≤(D' i).re ∧ |(D' i).im| ≤ Y i*a i ∧ ‖R i‖=1:=by
    filter_upwards [Z.support,W,touch D X' Z,v] with i ⟨_,J,h,_⟩ w ⟨u,p⟩ e; have hu:= stoutC D (I i) (F i) (bonB J h) w e u.le; exact ⟨hu.1,hu.2.1,(gleams D e.frame _).1⟩
 have hp(i)(h:0<a i)(p:‖R i‖=1): ‖t i-D' i‖=Q i*a i:=by change ‖R i*S i-R i*G i‖ =_; unfold Q; rw [←mul_sub, norm_mul,p,one_mul,div_mul_cancel₀ _ h.ne']
 constructor
 · filter_upwards [hx,W,Z.support,v,touch D X' Z,hA.shrinks.eventually (ge_mem_nhds (by positivity :0<c/2))] with i ⟨p,y,h⟩ w ⟨_,J,u,_⟩ l ⟨pv,f⟩ k; have hq:Q i≤c/2:=k; have hf:0<a i:=f; have he:= Complex.abs_re_le_norm (t i-D' i); rw [hp i f h, Complex.sub_re] at he; have hg:a i*(c/2) ≤ (t i).re:=by nlinarith [abs_le.mp he]
   have hY:0<(t i).re:= (mul_pos hf (by positivity)).trans_le hg; have hz:t i≠0:=fun v=>by rw [v] at hY; exact (lt_irrefl _ hY); -- tune
   obtain ⟨x,l',m⟩:=w.wave; have hv:= sailW (I i) (bonB J u) hP D.stmt D.eP D.p l' (F i) m (D.plan _ l.frame).1
   exact ⟨Integrable.of_bound hv.meas.aestronglyMeasurable _ (Eventually.of_forall hv.cost.choose_spec),pv,f,hg,hz,hY,(hg.trans (Complex.re_le_norm _)).trans_eq (by change ‖R i*S i‖=_; rw [norm_mul,h,one_mul]),fun e=>hz (by unfold t facing; rw [e,mul_zero,mul_zero])⟩
 refine (ht.panel hA).clip Z.tend ?_; filter_upwards [hx,touch D X' Z] with i ⟨p,x,h⟩ ⟨u,l⟩; refine ⟨by positivity,?_⟩; apply (div_le_iff₀ l).mpr; have he:= Complex.abs_im_le_norm (t i-D' i); rw [hp i l h,Complex.sub_im] at he; change _ ≤ (Y i+Q i)*a i; rw [add_mul]; have hv:= abs_le.mp x; have hz:= abs_le.mp he; apply abs_le.mpr; constructor<;> linarith

variable {α:Type*} (FX:ℕ→ℝ)
include U g
lemma echo (u:Onyx.Yard NP FX)(p:∀ i,Site (NP i))(T:Emu.Plot α FX)(J:List α): let Y(i):= optV FX i _ (p i) T J
  (∀ᶠ i in atTop,Integrable (getF (Y i) (I i) P (F i)) (city _))∧ Tendsto (fun i=>(∫ z,getF (Y i) (I i) P (F i) z∂city _)/partitionZ (I i) P (F i)) atTop (𝓝 (Emu.runes T.rho J)) :=by
 intro t; let M(i):=Graph.start (I i) P (F i); let S:= NP; let C:=eur S; let cityP i:=city (NP i); let G:=denQ (P:=P) (I:=I) F; let X(i):= ∫ z,baseW (t i) P (I i) (F i) z∂cityP i; let Y(i):=∫ z,recW (t i) P (I i) (F i) z∂cityP i; let L(i):=drip (I i) P
 have ht: ∀ᶠ i in atTop, Integrable (recW (t i) P (I i) (F i)) (city _) ∧ Integrable (baseW (t i) P (I i) (F i)) (city _) ∧ Integrable (getF (t i) (I i) P (F i)) (city _):=by
    filter_upwards [Z.support,W,Z.tend.eventually_ge_atTop k] with i ⟨_,a,w,p⟩ t' v; have hv:k≤(S i).val:=Nat.cast_le.mp v; have hp:= bonB a w; obtain ⟨u,b⟩:=integrable_s _ _ D t' hp (t i) hv; obtain ⟨s,k',m⟩:=t'.wave; have hx:=earned (t i) _ (sailW _ hp hP D.stmt D.eP D.p _ _ m (D.plan _ hv).1); exact ⟨u,b,Integrable.of_bound hx.meas.aestronglyMeasurable _ (Eventually.of_forall hx.cost.choose_spec)⟩
 refine ⟨ht.mono fun i p=>p.2.2,?_⟩
 obtain ⟨δ,hδ,v⟩:= caesar D X' Z; let D':= b'/(2*Nova.poseX); have hD:0<D'/2:= by unfold D'; have he:= D.pos; have hp:=pose_p; positivity
 have hv: BeamG D N δ 0 (3*J.length):= skybed D (W:=fun i=> (I i).p.threshold) v _ (hδ _)
 obtain ⟨hX,hY⟩:= elfin (a:=1) D (I:=fun i=>Orbit (S i)) (fun i=>dim (I i)) T J u hv p (fun i=> (I i).J.M) (fun _=>Prod.fst) (fun i=> cab (I i) P (F i)) cityP (by norm_num) (by
     filter_upwards [Z.support,W,v] with i ⟨_,a,w,t⟩ l b; exact handout D (I i) (F i) (bonB a w) l b) ((touch D X' Z).mono fun i e=> e.1) (ht.mono fun i p=>p.2.1)
 have he:∀ᶠ i in atTop, 0<L i∧ M i≠0∧ L i*(D'/2)≤ ‖G i‖:=by filter_upwards [(touch D X' Z),hX,(costR D X' Z F W U g).1] with i f p g; exact ⟨f.2,p,g.2.2.2.2.2.2.1⟩
 have hh:Charge α S t:=⟨⟨_,Eventually.of_forall fun i=> (show (t i).dial=J.length from rfl)⟩,(growG u).mono fun i p=> by exact lungG _ _ p.2 p.1⟩ -- tune pair
 have hx : ∀ᶠ i in atTop, ‖(M i-G i)/(L i:ℂ)‖= ‖G i-M i‖/L i := he.mono fun i h=>by rw [norm_div,Complex.norm_real,Real.norm_of_nonneg h.1.le,norm_sub_rev]
 have hK : Tendsto (fun i=>(Y i-X i)/(L i:ℂ)) atTop (𝓝 0):=by
    rw [tendsto_zero_iff_norm_tendsto_zero]; refine squeeze_zero' (Eventually.of_forall fun i=>norm_nonneg _) ?_ (shot D X' Z U g t F W hh).shrinks; filter_upwards [ht,he] with i ⟨p,b,h⟩ v; rw [norm_div, Complex.norm_real,Real.norm_of_nonneg v.1.le]; unfold Y X cityP; rw [←integral_sub p b]; exact div_le_div_of_nonneg_right (norm_integral_le_integral_norm _) v.1.le
 have hp:= power_v (Z:=Y) (X:=X) he hK (tendsto_zero_iff_norm_tendsto_zero.mpr ((wageK D X' Z F W U g).shrinks.congr' ((show _=ᶠ[atTop] _ from (show (fun i=> ‖(M i-G i)/(L i:ℂ)‖)=ᶠ[atTop] (fun i=> ‖G i-M i‖/L i) from hx)).symm))) hD _ hY; refine hp.congr' (Eventually.of_forall fun i=>?_); unfold Y; let f(i'):ℂ:=getF (t i) (I i) P (F i) i'; let c:= Complex.exp (-(I i).v); have he: c ≠0:=Complex.exp_ne_zero _; simp_rw [show ∀ j,recW (t i) P (I i) (F i) j=c*f j from fun j=>(by unfold recW feel valA recX; rw [map_smul,inner_smul_right]; rfl),MeasureTheory.integral_const_mul]; change (c*_)/(c*_)=(∫ z,f z ∂cityP i)/_; rw [mul_div_mul_left _ _ he]
end RoeWL
end YM.CF.Mint
