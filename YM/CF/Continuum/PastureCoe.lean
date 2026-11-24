import YM.CF.Continuum.Pastures
/-!
# Emu estimates with wide small-box option. Reworks Proof `Mint/Roe`
# except for growth (see Pastures) where sharper estimates needed
(permits families much larger than any fixed polylog bound, but not
one expanding at fixed coupling). Comparison includes growing-pivot
restriction independently of any later volume-agnostic claim.
-/
set_option autoImplicit false
noncomputable section
namespace YM.CF.Window
open Function Filter NormedSpace Finset Lattice Laurent Wilson Analysis Pressure MeasureTheory Mint Mint.Roe Graph Tulip Lat Cube SU Emu Rush Scree RG Scroll Peaks Drapes Cascade Vault Sods Spire Paige Nova Girt Skye Kea Ember
open scoped Topology ContDiff InnerProductSpace BigOperators Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
set_option maxHeartbeats 500000
set_option synthInstance.maxSize 8192
variable {N : ℕ→Side} {a b c w η r e K b' v C' l s' L' μ y h C L0 γ:ℝ}{J B m:Side}{O:Odd J.val}{j k:ℕ}{Y:Pricing j J O (Thread j)}{P:Grasp Y B e}{hP:Pearl P} {x L L1 : ℕ→ℝ}
namespace Pastures
local notation "NP" => (fun i=> mid (N i) B)
variable {I : ∀ i,GramM (mid (N i) B)} (D:Pic.Span hP K b' v C' l s' k)
    (Z: Pastures B N x h C r μ L' w γ L0 L I)
include D
lemma angleLower (PitY:Pastures B N x h C r μ L' w γ L0 L I) :∀ᶠ i in atTop, Graph.gainS (More (mid (N i) B)) (hemp x i)* Real.exp (-stoutY (More (mid (N i) B)) (I i).beta (4*hemp x i) γ (tame x i) L' L0)*horn (mid (N i) B) s' ≤drip (I i) P ∧0< Graph.angle (I i):=by
 filter_upwards [PitY.path.helm,PitY.path.infl,PitY.support0,PitY.tend.eventually_ge_atTop k] with i ⟨p,t,v⟩ ⟨xP,bP,T,h⟩ wK kA; obtain ⟨W,T',fℓ,g,a,hb⟩:=wK; let R:=I i; let N':= mid (N i) B; have hr:k≤N'.val:=(Nat.cast_le.mp kA); have hu:0 <gainS (More N') (hemp x i):=by unfold gainS; positivity
 have ht:= glow (bonB T' fℓ) fℓ p t (by rw [W]; exact v) a PitY.row bP.le; rw [W] at ht; have he:0<Graph.angle R:=(mul_pos hu (Real.exp_pos _)).trans_le ht; have hp:D.p=D.p:=rfl
 refine ⟨mul_le_mul ht ?_ (by unfold horn; have he:=D.rP; have hp:=Ember.pinch_pos (mid (N i) B); positivity) he.le,he⟩; exact (cupP _ (too (mid (N i) B)) (R.J.M) D.rP).trans_eq (D.fits _ hr _)
include Z
lemma caesar:∃ T:ℕ→ℝ,Aqua (eur NP) T∧∀ᶠ i in atTop,CoolR D (N i) (T i) (I i).p.threshold:=by
 obtain ⟨u,b,t,p,Q'⟩:= manyK (B:=B)
 let S:= tame x; let E:=eur NP; let M:= fun i=>More (NP i); let y(i):=eur M i^2 * (tame x i) * b⁻¹
 let W:=Z.path; have hx:Aqua E y:=by
    have hp: Gray E (eur M):=by
       apply (Gray.mul (Gray.arg Z.tend) (Gray.coef Z.tend 2)).eqK; apply Eventually.of_forall; intro i; norm_num [E, M, eur, More]
    exact ((Aqua.fed (show Aqua E (tame x) from Z.large.tame_bills) (hp.powG Z.tend 2) Z.tend).pays (Gray.coef Z.tend b⁻¹) Z.tend)
 have hz:∀ᶠ i in atTop,0<y i:= W.infl.mono fun i h=>by unfold y; have hp:=h.2.2.1; have hv:0<eur M i:=nPos (M i); positivity
 obtain ⟨e,A⟩:= rootA Z.tend hx hz t; let T :=fun i=> y i ^ ((u:ℝ)⁻¹)
 have hp:=A 10; let B1:= b'/(2 * poseX); have hC:=D.pos; have hX:0<B1:=by unfold B1; have he:=pose_p; positivity
 refine ⟨T,A,?_⟩; filter_upwards [Z.tend.eventually_ge_atTop k,e,A.shrinks.eventually (ge_mem_nhds one_pos), hp.eventually (ge_mem_nhds (lt_min D.xP one_pos)), (hp.const_mul C').eventually (ge_mem_nhds (by simpa using hX : C'*0< B1)),Z.support0,W.infl] with i hi ⟨v,e⟩ t x a w u'; refine ⟨v,t,Nat.cast_le.mp hi,x,?_,fun U g=>?_⟩; -- tune shadow
 · unfold duty; rw [zero_mul,add_zero,mul_assoc]; exact a
 apply Q' _ U (I i).p.threshold (T i) ((I i).p.threshold_pos) g v t; rw [show T i^_ = _ from e,w.1]; unfold y eur M; rw [mul_comm b, inv_mul_cancel_right₀ p.ne']
lemma alive : ∀ᶠ i in atTop,0<Graph.angle (I i) ∧0<drip (I i) P:=by filter_upwards [Z.angleLower D,Z.path.helm] with i ⟨p,h⟩ ⟨e,v,y⟩; refine ⟨h,lt_of_lt_of_le ?_ p⟩; unfold gainS horn; have he:=D.rP; have hx:= pinch_pos (NP i); positivity
omit D
lemma teal:Aqua (eur NP) (bloom NP r x):=by
 let A:=eur NP; have h : Aqua A (tame x):=Z.large.tame_bills; have he:=Z.wind; let f(i):= Real.exp (-(r*eur (More∘NP) i)); refine Aqua.panel h (Aqua.fed (F:=f) ?_ (Gray.coef Z.tend 2) Z.tend); exact (Aqua.exp_neg Z.tend r he).clip Z.tend (Eventually.of_forall fun i=> by change 0≤f i ∧ f i ≤ _; refine ⟨(Real.exp_pos _).le,Real.exp_le_exp.mpr ?_⟩; rw [neg_mul]; apply neg_le_neg; gcongr; unfold eur; exact_mod_cast (show (NP i).val ≤ ((More∘NP) i).val from Nat.le_mul_of_pos_right _ (by change (0:ℕ)<2; decide))) -- tune
lemma surge (k:ℝ): let M:=NP; let G:=bloom M r x; Aqua (eur M) (fun i=> baton (M i) (L i) (G i) C k)∧ (∀ᶠ i in atTop, pittance (M i) (G i) C ≤1∧ 0 ≤ G i):=by
 intro M G; let F:=Aqua (eur M); have h:Aqua (eur M) G:= Pastures.teal Z; have he:= Z.tend; let H:= fun k=>Gray.coef he k; have hx:=damp Z.path.rank
 have hb :∀ᶠ i in atTop,0 ≤ G i:= Z.path.infl.mono fun i v=> (v.2.2.1.trans_le (le_add_of_nonneg_right (by positivity))).le
 have hp : Gray (eur M) (eur M):=Gray.arg he; have hu:Aqua (eur M) (fun i=> G i ^2) := by simpa [sq] using (h.pays (Gray.thin he h.shrinks) he)
 let LK(i):= pittance (M i) (G i) C; have ht:Aqua (eur M) LK:= ((hu.pays (H C) he).pays (hp.powG he 4) he)
 have hw:Gray (eur M) (fun i=> lark (M i)):= (H 180).mul (hp.powG he 4)
 let X(i):= doorF (M i) (G i) C; have hg:Aqua (eur M) X:= Aqua.fed (Aqua.fed ((by
   show Aqua (eur M) (fun i=> (G i + G i^2)*C); exact ((h.panel hu).pays (H C) he))) (H 45) he) hw he
 let U(i):=axle (M i) (L i)+X i*lark (M i)^2*k^2; have hl:Aqua (eur M) U:=by
    have hy : Gray (eur M) (eur (More ∘ M)):=by apply Gray.eqK (hp.mul (H 2)); exact Eventually.of_forall fun i=>by change eur M i*2=eur (More ∘ M) i; unfold eur; norm_num [More]; done
    exact Aqua.panel ((Z.loc.panel Z.loc).pays (hy.powG he 4) he) ((hg.pays (hw.powG he 2) he).pays (H _) he)
 have hL:Tendsto (fun i=>Real.exp (LK i)) atTop (𝓝 (Real.exp 0)):= (Real.continuous_exp.continuousAt.tendsto.comp ((show Aqua (eur M) LK from ht).shrinks)); have hz: ∀ᶠ i in atTop,0≤U i:=by
    filter_upwards [Z.support0,hb] with i ℓ p; have hg:=ℓ.2.2.2.2.2; have hx:=Z.size; unfold U axle X doorF lark; positivity
 exact ⟨Aqua.panel ((show Aqua (eur M) LK from ht).fed (H 2) he) (Aqua.fed (Aqua.rise hl he hz) (Gray.thin he hL) he),(ht.shrinks.eventually (ge_mem_nhds one_pos)).and hb⟩ -- infer ht issue
open Fock Pastry Dial Gall
include D
section first
variable {d vA r₀ C₀ E':ℝ}{n₀:ℕ} (F:Port D d E' C₀ vA r₀ n₀)(g:C₀ ≤h)
lemma flagK (F:Port D d E' C₀ vA r₀ n₀):∀ᶠ i in atTop,(I i).p.threshold≤ r₀:= (Z.support0.and ((damp Z.path.rank).shrinks.eventually (ge_mem_nhds F.pit))).mono fun i h=>le_trans h.1.1.le h.2
include F g
lemma shot {α:Type*}(T:∀ i,Opt (α:=α) (NP i))(X:∀ i,Loom (NP i))(U:∀ᶠ i in atTop,SkinT (I i) (X i) e)(H:Charge α NP T) : Aqua (eur NP) fun i=> phM (I i) (T i) P (X i) /drip (I i) P:=by
 let S:=NP; let R:=eur S; let V'(i):= bloom S r x i; let W(i):= baton (S i) (L i) (V' i) C d; let B'(i):= lite (T i); let R'(i):= Real.exp (flagBill (S i) (L i) (L i) C - kinetic (More (S i)) (I i).p L' L0 (I i).beta w)
 have he:= Z.tend; obtain ⟨Wk,Wb⟩:= Pastures.surge Z d; obtain ⟨n,p⟩:=H.art; have hp:Gray R R:= Gray.arg he
 have hv:Gray R B':= (((hp.powG he 2).powG he n)).eqK (p.mono fun i t=>by change (R i^2)^n=B' i; rw [←t])
 have hu:Gray R (fun i=>feeP (T i) d):= ((((Gray.coef he (d*180)).mul (hp.powG he 6)).powG he n).eqK (p.mono fun i t=>by change (d*180*R i^6)^n=_; rw [←t]; rfl))
 have hl: Aqua R (fun i=> W i * E' * feeP (T i) d):=(Wk.pays (Gray.coef he E') he).pays hu he
 have hL:Aqua R (fun i=> B' i * (R' i/drip (I i) P)):= (Aqua.fed (Pastures.wear D Z) hv he) -- tune explicit
 refine (hl.panel hL).clip he ?_; obtain ⟨Q,A,QF⟩:= Pastures.caesar D Z
 filter_upwards [Pastures.alive D Z,Z.support0,QF,Pastures.flagK D Z F,U,Wb,H.paid,Z.tend.eventually_ge_atTop (n₀:ℝ), Z.path.infl, ((A 10).eventually (ge_mem_nhds F.knot))] with i ⟨u,p⟩ ⟨X',J,gx,hQ,w',v⟩ q fU Xh ⟨a,v'⟩ hO hn ht hi
 let n:= S i; have ht':n₀≤ n.val:=(Nat.cast_le.mp hn); have hm(T: Orbit (S i))(p:T∈ Lace (I i)): flags ((I i).p.threshold) T.1=∅:= p
 let F':= phM (I i) (T i) P (X i); have hf: 0 ≤ F':= integral_nonneg fun x=>norm_nonneg _; have hg:= F.sap
 refine ⟨div_nonneg hf p.le,?_⟩; apply (div_le_iff₀ p).2
 have ha:T i=T i:=rfl
 refine le_trans (Window.together_ledger (I i) (X i) D Xh J Z.wind v' F.sap.le Z.bold gx ht.2.1.le Z.clip.le hQ (F.site.trans ht') Z.size F.lark.le ?_ ?_ ?_ a (T i) hO) ?_
 · intro w t; obtain ⟨f,d,gT,h⟩:=q.roll w.1 t; exact F.wear (N i) ht' w.1 _ _ _ (Q i) (spiral _ gT) q.pose q.data hi h
 · intro w t j; have he: flags r₀ w.1=∅:=by
      apply Finset.eq_empty_iff_forall_notMem.mpr; intro i p; obtain ⟨x,u,v⟩:= (flags_spec ..).mp p; have hp:= t; change flags _ w.1=∅ at hp; exact notMem_empty _ (hp ▸ (flags_spec ..).mpr ⟨x,u,fU.trans_lt v⟩) -- tune
   exact (F.draw n ht' w.1 he _ _).weigh g F.sap.le
 · intro w t; have hx:=tile_p w.1 (show 0 ≤ tame x i from ht.2.2.1.le) Z.wind.le (show _ from (by rw [← X']; exact t)); exact hx
 apply le_of_eq; change _= (W i*E'*feeP _ d + B' i *(R' i/drip (I i) P))*drip (I i) P; unfold W V'; rw [add_mul, mul_assoc (B' i),div_mul_cancel₀ _ p.ne']; ring -- tune More
end first
section
variable (F_:∀ i,Loom (mid (N i) B)) (W:∀ᶠ i in atTop,SkinT (I i) (F_ i) e) {d vA r₀ C₀ E':ℝ}{n₀:ℕ} (U:Port D d E' C₀ vA r₀ n₀)(g:C₀ ≤h)
include W U g
lemma wageK: Aqua (eur NP) fun i=> ‖denQ (P:=P) (I:=I) F_ i -Graph.start (I i) P (F_ i)‖/drip (I i) P:=by
 let O(i):= tOpt (NP i); have hh: Charge Empty NP O:=⟨⟨0,Eventually.of_forall fun i=>rfl⟩,Eventually.of_forall fun i=>by simp [O,tOpt,Emu.gain]⟩
 refine (Pastures.shot D Z U g O F_ W hh).clip Z.tend ?_
 filter_upwards [W,Z.support0,Pastures.alive D Z,Z.tend.eventually_ge_atTop k] with i p ⟨x,y,h,t⟩ ⟨u,q⟩ v; refine ⟨by positivity,?_⟩
 obtain ⟨A,B⟩:=Graph.integrable_s (I i) _ D p (bonB y h) (O i) (Nat.cast_le.mp v); obtain ⟨X,Y⟩:=porx (P:=P) (I:=I) F_ i; refine div_le_div_of_nonneg_right ?_ q.le; rw [←X,← Y,← integral_sub A B]; exact norm_integral_le_integral_norm _
lemma costR: let c:=b'/(2*Nova.poseX); let t(i):= facing (I i) P (F_ i)
 (∀ᶠ i in atTop, Integrable (denZ (I i) P (F_ i)) (city _) ∧ 0 <Graph.angle (I i) ∧0<drip (I i) P∧ drip (I i) P * (c/2) ≤ (t i).re ∧ (t i)≠0∧ (t i).re >0 ∧ ‖denQ (P:=P) (I:=I) F_ i‖≥(drip (I i) P)*(c/2) ∧partitionZ (I i) P (F_ i) ≠0)∧ Aqua (eur NP) fun i=> |(t i).im| / drip (I i) P:=by
 intro c t; obtain ⟨T,V,v⟩:= Pastures.caesar D Z; let R(i):= gleam (N i) P (I i).J.M; let a(i):=drip (I i) P; let G(i):=Graph.start (I i) P (F_ i); let D'(i):= R i*G i; let S:= denQ (P:=P) (I:=I) F_
 have hc:0<c:=by unfold c; have ht:=D.pos; have he:= pose_p; positivity
 let Q(i):= ‖S i-G i‖/a i; have hA:Aqua (eur NP) Q:= Pastures.wageK D Z F_ W U g; let Y(i):= duty (eur NP i) (T i) C' 0; have ht:Aqua (eur NP) Y:=by unfold Y duty; simp only [zero_mul,add_zero]; exact V.fed ((Gray.coef Z.tend C').mul ((Gray.arg Z.tend).powG Z.tend 10)) Z.tend
 have hx:∀ᶠ i in atTop, a i*c≤(D' i).re ∧ |(D' i).im| ≤ Y i*a i ∧ ‖R i‖=1:=by
    filter_upwards [Z.support0,W,Pastures.alive D Z,v] with i ⟨_,J,h,_⟩ w ⟨u,p⟩ e; have hu:= stoutC D (I i) (F_ i) (bonB J h) w e u.le; exact ⟨hu.1,hu.2.1,(gleams D e.frame _).1⟩
 have hp(i)(h:0<a i)(p:‖R i‖=1): ‖t i-D' i‖=Q i*a i:=by change ‖R i*S i-R i*G i‖ =_; unfold Q; rw [←mul_sub, norm_mul,p,one_mul,div_mul_cancel₀ _ h.ne']
 constructor
 · filter_upwards [hx,W,Z.support0,v,Pastures.alive D Z,hA.shrinks.eventually (ge_mem_nhds (by positivity :0<c/2))] with i ⟨p,y,h⟩ w ⟨_,J,u,_⟩ l ⟨pv,f⟩ k; have hq:Q i≤c/2:=k; have hf:0<a i:=f; have he:= Complex.abs_re_le_norm (t i-D' i); rw [hp i f h, Complex.sub_re] at he; have hg:a i*(c/2) ≤ (t i).re:=by nlinarith [abs_le.mp he]
   have hY:0<(t i).re:= (mul_pos hf (by positivity)).trans_le hg; have hz:t i≠0:=fun v=>by rw [v] at hY; exact (lt_irrefl _ hY); -- tune
   obtain ⟨x,l',m⟩:=w.wave; have hv:= sailW (I i) (bonB J u) hP D.stmt D.eP D.p l' (F_ i) m (D.plan _ l.frame).1
   exact ⟨Integrable.of_bound hv.meas.aestronglyMeasurable _ (Eventually.of_forall hv.cost.choose_spec),pv,f,hg,hz,hY,(hg.trans (Complex.re_le_norm _)).trans_eq (by change ‖R i*S i‖=_; rw [norm_mul,h,one_mul]),fun e=>hz (by unfold t facing; rw [e,mul_zero,mul_zero])⟩
 refine (ht.panel hA).clip Z.tend ?_; filter_upwards [hx,Pastures.alive D Z] with i ⟨p,x,h⟩ ⟨u,l⟩; refine ⟨by positivity,?_⟩; apply (div_le_iff₀ l).mpr; have he:= Complex.abs_im_le_norm (t i-D' i); rw [hp i l h,Complex.sub_im] at he; change _ ≤ (Y i+Q i)*a i; rw [add_mul]; have hv:= abs_le.mp x; have hz:= abs_le.mp he; apply abs_le.mpr; constructor<;> linarith
variable {α:Type*} (R:ℕ→ℝ)
lemma echo (u:Onyx.Yard NP R)(p:∀ i,Site (NP i))(T:Emu.Plot α R)(J:List α): let Y(i):= optV R i _ (p i) T J
  (∀ᶠ i in atTop,Integrable (getF (Y i) (I i) P (F_ i)) (city _))∧ Tendsto (fun i=>(∫ z,getF (Y i) (I i) P (F_ i) z∂city _)/partitionZ (I i) P (F_ i)) atTop (𝓝 (Emu.runes T.rho J)) :=by
 intro t; let M(i):=Graph.start (I i) P (F_ i); let S:= NP; let C:=eur S; let cityP i:=city (NP i); let G:=denQ (P:=P) (I:=I) F_; let X(i):= ∫ z,baseW (t i) P (I i) (F_ i) z∂cityP i; let Y(i):=∫ z,recW (t i) P (I i) (F_ i) z∂cityP i; let L(i):=drip (I i) P
 have ht: ∀ᶠ i in atTop, Integrable (recW (t i) P (I i) (F_ i)) (city _) ∧ Integrable (baseW (t i) P (I i) (F_ i)) (city _) ∧ Integrable (getF (t i) (I i) P (F_ i)) (city _):=by
    filter_upwards [Z.support0,W,Z.tend.eventually_ge_atTop k] with i ⟨_,a,w,p⟩ t' v; have hv:k≤(S i).val:=Nat.cast_le.mp v; have hp:= bonB a w; obtain ⟨u,b⟩:=integrable_s _ _ D t' hp (t i) hv; obtain ⟨s,k',m⟩:=t'.wave; have hx:=earned (t i) _ (sailW _ hp hP D.stmt D.eP D.p _ _ m (D.plan _ hv).1); exact ⟨u,b,Integrable.of_bound hx.meas.aestronglyMeasurable _ (Eventually.of_forall hx.cost.choose_spec)⟩
 refine ⟨ht.mono fun i p=>p.2.2,?_⟩
 obtain ⟨δ,hδ,v⟩:= Pastures.caesar D Z; let D':= b'/(2*Nova.poseX); have hD:0<D'/2:= by unfold D'; have he:= D.pos; have hp:=pose_p; positivity
 have hv: BeamG D N δ 0 (3*J.length):= skybed D (W:=fun i=> (I i).p.threshold) v _ (hδ _)
 obtain ⟨hX,hY⟩:= elfin (a:=1) D (I:=fun i=>Orbit (S i)) (fun i=>dim (I i)) T J u hv p (fun i=> (I i).J.M) (fun _=>Prod.fst) (fun i=> cab (I i) P (F_ i)) cityP (by norm_num) (by
     filter_upwards [Z.support0,W,v] with i ⟨_,a,w,t⟩ l b; exact handout D (I i) (F_ i) (bonB a w) l b) ((Pastures.alive D Z).mono fun i e=> e.1) (ht.mono fun i p=>p.2.1)
 have he:∀ᶠ i in atTop, 0<L i∧ M i≠0∧ L i*(D'/2)≤ ‖G i‖:=by filter_upwards [(Pastures.alive D Z),hX,(Pastures.costR D Z F_ W U g).1] with i f p g; exact ⟨f.2,p,g.2.2.2.2.2.2.1⟩
 have hh:Charge α S t:=⟨⟨_,Eventually.of_forall fun i=> (show (t i).dial=J.length from rfl)⟩,(growG u).mono fun i p=> by exact lungG _ _ p.2 p.1⟩ -- tune pair
 have hx : ∀ᶠ i in atTop, ‖(M i-G i)/(L i:ℂ)‖= ‖G i-M i‖/L i := he.mono fun i h=>by rw [norm_div,Complex.norm_real,Real.norm_of_nonneg h.1.le,norm_sub_rev]
 have hK : Tendsto (fun i=>(Y i-X i)/(L i:ℂ)) atTop (𝓝 0):=by
    rw [tendsto_zero_iff_norm_tendsto_zero]; refine squeeze_zero' (Eventually.of_forall fun i=>norm_nonneg _) ?_ (Pastures.shot D Z U g t F_ W hh).shrinks; filter_upwards [ht,he] with i ⟨p,b,h⟩ v; rw [norm_div, Complex.norm_real,Real.norm_of_nonneg v.1.le]; unfold Y X cityP; rw [←integral_sub p b]; exact div_le_div_of_nonneg_right (norm_integral_le_integral_norm _) v.1.le
 have hp:= power_v (Z:=Y) (X:=X) he hK (tendsto_zero_iff_norm_tendsto_zero.mpr ((Pastures.wageK D Z F_ W U g).shrinks.congr' ((show _=ᶠ[atTop] _ from (show (fun i=> ‖(M i-G i)/(L i:ℂ)‖)=ᶠ[atTop] (fun i=> ‖G i-M i‖/L i) from hx)).symm))) hD _ hY; refine hp.congr' (Eventually.of_forall fun i=>?_); unfold Y; let f(i'):ℂ:=getF (t i) (I i) P (F_ i) i'; let c:= Complex.exp (-(I i).v); have he: c ≠0:=Complex.exp_ne_zero _; simp_rw [show ∀ j,recW (t i) P (I i) (F_ i) j=c*f j from fun j=>(by unfold recW feel valA recX; rw [map_smul,inner_smul_right]; rfl),MeasureTheory.integral_const_mul]; change (c*_)/(c*_)=(∫ z,f z ∂cityP i)/_; rw [mul_div_mul_left _ _ he]
end
end Pastures
end YM.CF.Window
