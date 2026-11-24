import SatinFixedContrastNovember4

import SatinThinSymphony

/-! # CP12 Nuclear rank -/
set_option autoImplicit false
set_option maxHeartbeats 350000
set_option synthInstance.maxSize 28000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common Ballad Cordial
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
open Germ Alliance Lamour.Bridge.Celeste Designs Twah Prototype
open Lamour.Bridge.Celeste.Morn
namespace Spine
open Aria Casting Six OS.Semigroup.Balloon
open MacroGrid Aria Casting Six OS.Semigroup.Balloon
open MacroGrid SatinNucleus
lemma rank_inject {L:Hilbert}(j:Axis)(V:OS.Semigroup L j)(t:ℝ≥0): Function.Injective (V.E t):=by
 suffices w:∀ y:L, V.E t y=0→ y=0 by intro x y q; exact sub_eq_zero.mp (w _ (by rw [map_sub,q,sub_self]))
 intro y q; let f(i:ℕ):ℝ≥0:= t*(1/2:ℝ≥0)^i
 have he(i): V.E (f i) y=0:=by
    induction i with
    | zero=>simpa [f] using q
    | succ i ih=>
      let a:=f (i+1)
      have hx: f i=a+a:=by unfold a f; rw [pow_succ]; ring
      -- inner pos
      refine inner_self_eq_zero.mp (by rw [V.swing, ←ContinuousLinearMap.comp_apply (V.E a),← V.time,← hx,ih,inner_zero_right])
 have hu : Tendsto f atTop (𝓝 0):=by
    have hz:Tendsto (fun i:ℕ=>(1/2:ℝ≥0)^i) atTop (𝓝 0):= tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
    simpa only [f, mul_zero] using hz.const_mul t
 have hv:=tendsto_nhds_unique ((V.continuousE y).continuousAt.tendsto.comp hu) (tendsto_const_nhds.congr fun i=>(he i).symm); rw [V.eZero] at hv; exact hv
private lemma rank_up {H:Hilbert}{κ:Type}(f:H.Op){X:κ→ H}{Y:κ→ H}(h:Function.Injective f)(p:∀ i, f (X i)=Y i): LinearIndependent ℂ Y ↔ LinearIndependent ℂ X:=by
 rw [show Y=f.toLinearMap ∘ X from funext fun i=>(p i).symm]; exact f.toLinearMap.linearIndependent_iff (LinearMap.ker_eq_bot.mpr h)

-- retreat
variable (P:Spine)(x:P.Spectrum0 3)(j:Axis)
local notation "ξ(j)" => P.advocate 3 x j -- unused
local notation "G" j:max=> P.ManyF j (P.advocate 3 x j)
local notation "κ" j:max=> P.wealth j (P.advocate 3 x j)
local notation "U" j:max=> P.cartage j (P.advocate 3 x j)
local notation "H" j:max=> P.seasons j (P.advocate 3 x j)
local notation "E" j:max=> (H j).E
variable (f r n:ℕ) (v:ℕ→ℕ)(u:StrictMono v)(a: ℕ→ (ℕ×ℕ)→ℝ)(Q:ℕ → Coalition) {P₀:ℕ→P.Apron}
local notation "a'" => fun i:ℕ=> a i (f,r)
variable (W:∀ j:Axis,List Axis→ℝ→ P.ColorHil j (P.advocate 3 x j))
local notation "C" k:max=> P.basePlay x f k
local notation "Ψ" k:max=> P.meshPose k (P.runP f k 1 0)
local notation "A!"=> P.invoiceV x f r r 1
local notation "B!" i:max=> P.invoiceV x f r (v i) (( (a') i:ℝ):ℂ)
local notation "Φ"=> P.flightCap f
local notation "Z"=> (fun _:Axis=> P.flightCap f)
lemma invoice_flight {t:ℕ}(s:ℂ)(e:P.reached f t): P.invoiceV x f r t s = (U 3) (Ψ t) ((P.rewardK f r:ℂ) • s • P.beam 3 x (C t) ((Ψ t) 3)):=by
 unfold invoiceV; rw [map_smul,map_smul,←P.capStroll]; obtain ⟨h,p⟩:= P.beam_grid_pose_view 3 x (C t) t (P.runP f t 1 0) (show (C t).realWidth P 3 ≤ (Ψ t) 3 from ( (P.bought_as x e 1 zero_lt_one 3).le.trans ((P.rent_only ..).symm|>.le))) (le_refl t) -- tune args
 obtain ⟨b,r₀⟩:= P.residentH x e (i:=1) zero_lt_one 0; rw [←r₀,show P.viewF 3 _ _ b= _ from p]; unfold beamGridRay; rw [P.commit_move,P.beam_bank]; rfl
lemma height_pass (g:Radiates P x P₀ W)(l:List Axis) {t r:ℝ}(p:0<t)(q:t≤ r): (κ j) (W j l r)=(E j) (r-t).toNNReal ((κ j) (W j l t)):= (congrArg ((κ j)) (g.choir j l p q)).trans (P.bankHeat ..)
-- CP10 provenance compare on moved clock
local notation "r★" i:max => ((P.rewardK f r:ℂ) * ( ((a') i:ℝ):ℂ)) -- syntax needs (a')
local notation "X'" i:max => (U 3) Z ((r★ i) • P.beam 3 x (C (v i)) Φ)
lemma moves_invoice (t:f≤ r) (h:P.reached f r) {i:ℕ}(p:r≤ v i) : X' i=(U 3) (Z-Ψ (v i)) ((E 3) ((Φ)- (Ψ (v i)) 3).toNNReal (B! i)):=by
 let P':=Ψ (v i); let XZ:=Z
 have w:(C (v i)).realWidth P 3≤ P' 3:= ( (P.bought_as x (P.reach_onward h p) 1 zero_lt_one 3).le.trans ((P.rent_only ..).symm|>.le))
 rw [P.invoice_flight x f r _ (P.reach_onward h p), P.warm_drive, P.beam_twice 3 x _ w (P.offer_beneath (t.trans p) 3)] -- order
 simp_rw [map_smul,mul_smul]
 apply congrArg (fun z:(G 3)=> (P.rewardK f r:ℂ) • (( (a') i:ℂ) • z)); rw [←ContinuousLinearMap.comp_apply ((U 3) (Z-Ψ (v i))),←P.cart_paves,sub_add_cancel]
private lemma contractionE (S:Hilbert)(c:S.Op)(p:‖c‖≤ 1)(x y:S): dist (c x) (c y)≤ dist x y:=by rw [dist_eq_norm,← map_sub,dist_eq_norm]; exact (c.le_opNorm _).trans (mul_le_of_le_one_left (norm_nonneg _) p)
local notation "T" q:max=> fun i=>P.pleading x f r i (q i) v a' u
include u
set_option linter.unusedSectionVars false in
private lemma limiting_ball {b:ℝ}(t:f≤ r)(h:P.reached f r)(p:∀ i,r≤ v i)(e:0<b)(R:∀ i, dist (B! i) A! ≤ b/16): ∀ᶠ i:ℕ in atTop, dist (X' i) A! ≤ b:=by
 let Y(i):= Ψ (v i); let Z₀:= Z
 let W:= U 3; let S:= H 3
 let f'(i:ℕ):= ((Φ)-Y i 3).toNNReal; have hu:Tendsto Y atTop (𝓝 Z):=P.offer_approaches f|>.comp u.tendsto_atTop
 have hx:Tendsto (fun i=>Z₀-Y i) atTop (𝓝 0):=by simpa only [Z₀,sub_self] using (tendsto_const_nhds (x:=Z)).sub hu
 let S₁:=fun x:ℝ≥0 × Vantage=> W x.2 (S.E x.1 A!); have hw:Tendsto f' atTop (𝓝 0):=by
    have he:= (tendsto_const_nhds (x:=Φ)).sub ((tendsto_pi_nhds.mp hu) 3)
    have hc:= (continuous_real_toNNReal.tendsto _).comp he
    change Tendsto f' atTop (𝓝 ((Φ)-(Φ)).toNNReal) at hc; simpa only [sub_self,Real.toNNReal_zero] using hc
 have he: Tendsto (fun i=> S₁ (f' i,Z₀-Y i)) atTop (𝓝 A!):=by
    have ht:(S₁) (0,0)= A!:= by unfold S₁ S W; dsimp only; rw [(H 3).eZero,P.cart_zero]; rfl
    have ht':Continuous S₁:= P.caravan 3 (P.advocate 3 x 3) Prod.snd _ continuous_snd ((S.continuousE A!).comp continuous_fst) -- tune
    exact (ht'.tendsto' _ _ ht).comp (hw.prodMk_nhds hx)
 filter_upwards [Metric.tendsto_nhds.mp he _ (show 0<b/2 from half_pos e)] with i t'
 refine le_trans (dist_triangle _ (S₁ (f' i,Z₀-Y i)) _) ?_; have hb: dist (X' i) (S₁ (f' i,Z₀-Y i)) ≤ b/16:= by
    rw [P.moves_invoice x f r v a t h (p i)] -- u not used?
    exact (contractionE (G 3) (W (Z₀-Y i)) (P.cart_pay ..) _ _).trans ((contractionE (G 3) (S.E (f' i)) (S.shrinks _) _ _).trans (R i))
 linarith only [t',hb,e]
-- close and lift. cost at mean
omit u in
private lemma allied {X₁:Hilbert}(G': Coalition)(T': X₁)(Y:ℕ→ X₁) (b:ℝ)(p:∀ i∈G'.voters,dist (Y i) T'≤ b) : dist (∑ i∈ G'.voters,(G'.w i:ℂ) • Y i) T' ≤ b:=by
 letI := InnerProductSpace.rclikeToReal ℂ X₁
 exact (convex_closedBall T' b).sum_mem G'.signed G'.pledges p -- instance order
lemma combined_ball {P₁ C₁ b:ℝ}(X:ScoutAnthem P x P₁ C₁ f r b v a)(t:f≤ r)(h:P.reached f r)(e:0<b)(g:Radiates P x (T Q) W) : dist ((U 3) Z ((κ 3) (W 3 [] Φ))) A!≤ b:=by
 obtain ⟨p,w⟩:=X.station
 have hu:= limiting_ball P x f r v u a t h w.up e w.main
 let Y(i:ℕ):= P.beam 3 x (((T Q) i).pivot P []) (Φ)
 let QX:= (U 3) Z; have ht:Tendsto (fun i=>QX (Y i)) atTop (𝓝 (QX ((κ 3) (W 3 [] Φ)))):= (QX.continuous.tendsto _).comp (g.port 3 [] (P.flight_pos f) tendsto_const_nhds)
 refine le_of_tendsto (ht.dist tendsto_const_nhds) ?_; obtain ⟨b',hp⟩:= eventually_atTop.mp hu; filter_upwards [(g.slender 3).eventually (gt_mem_nhds (P.flight_pos f)),eventually_ge_atTop b'] with i v0 p'
 have hw:QX (Y i)= ∑ k∈ (Q i).voters,((Q i).w k:ℂ) • X' (i+k):=by
    unfold Y; rw [P.beam_bank, P.pleading_p x 3 f r i _ v u _ _ _ ((P.pleading_w ..).symm.le.trans (le_of_lt v0)),map_sum,map_sum]; refine sum_congr rfl fun k _=>?_ -- args
    rw [Apron.pivot_nil]; unfold QX; simp only [P.beam_bank,map_smul,Complex.ofReal_mul,mul_smul]
 change dist (QX (Y i)) _ ≤ b; rw [hw]; exact allied (X₁:= G 3) (Q i) _ (fun k=>X' (i+k)) b fun k _=> hp (i+k) (by omega)
omit u
local notation "E!" i:max t:max=> (E 3) (P.launchTick f r (SatinJets.stride i)) ((κ 3) (W 3 [] t))
private lemma freedom (w:Vantage) (y:G 3)(g:LinearIndependent ℂ (fun i:SatinJets.Seven=> P.epochW x f r i ((U 3) w y))): LinearIndependent ℂ (fun i:SatinJets.Seven=> P.epochW x f r i y):=by
 let U':= (U 3) w; refine (rank_up U' ?_ (fun i:SatinJets.Seven=>?_)).mp g
 · refine fun i j q=> sub_eq_zero.mp (norm_eq_zero.mp ((P.cart_norm 3 (P.advocate 3 x 3) w (i-j)).symm.trans (show ‖U' (i-j)‖=0 from by rw [map_sub,q,sub_self,norm_zero])))
 exact (P.warm_drive ..).symm
private lemma neighbors (g:Radiates P x P₀ W)(w:SatinJets.Seven){t t':ℝ}(p:0<t)(f':t ≤ t'): (E 3) (t'-t).toNNReal (E! w t)=(E! w t'):=by
 rw [P.height_pass x 3 W g [] p f', ← ContinuousLinearMap.comp_apply ((E 3) (t'-t).toNNReal),← (H 3).time,add_comm, (H 3).time]; rfl
include u
lemma freemen {P₁ C₁ b:ℝ}(X:ScoutAnthem P x P₁ C₁ f r b v a)(t:f≤ r)(h:P.reached f r)(e:0<b)(g:Radiates P x (T Q) W)(R:P.reliableP x f r b) (p:ℝ)(q:0<p): LinearIndependent ℂ (fun i:SatinJets.Seven=> P.epochW x f r i ((κ 3) (W 3 [] p))):=by
 have ht:= freedom P x f r Z ((κ 3) (W 3 [] Φ)) (R _ (P.combined_ball x f r v u a Q W X t h e g))
 by_cases v:(Φ) ≤ p
 · exact (rank_up (X:=fun i:SatinJets.Seven=> (E! i Φ)) ((E 3) (p-(Φ)).toNNReal) (rank_inject ..) (fun i:SatinJets.Seven=> P.neighbors x f r W g i (P.flight_pos f) v)).mpr ht -- rank_inject .. elaborated takes implicits x, y, eq
 exact (rank_up (X:=fun i:SatinJets.Seven=> (E! i p)) ((E 3) ((Φ)-p).toNNReal) (rank_inject ..) (fun i:SatinJets.Seven=> P.neighbors x f r W g i q (le_of_lt (lt_of_not_ge v)))).mp ht
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
#print axioms YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine.freemen
