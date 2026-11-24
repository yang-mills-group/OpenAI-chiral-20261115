import GaugeFieldConstruction.Bantry
import YM.CF.Chaff.Sky
set_option autoImplicit false
set_option synthInstance.maxSize 24000
set_option maxHeartbeats 200000
set_option quotPrecheck false
noncomputable section
namespace YM.CF
namespace XGarden
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Classical Matrix.Norms.L2Operator
open Cube Lat Tulip Fock Rush Scroll Paige Vault Phase Spire
attribute [local instance] opCStarAlgebra
open Broc Jet Drapes
variable {K b c d r v e:ℝ}{N m B:Side}{n:ℕ}{E:Type}[NormedAddCommGroup E][NormedSpace ℝ E]
open Chaff
section
variable {W W': Type}[NormedAddCommGroup W][NormedSpace ℝ W][NormedAddCommGroup W'][NormedSpace ℝ W']
lemma comps {f:E→W}{x:W'}(L:W'→L[ℝ] E)(h:Allows n f (L x) c)(p:‖L‖ ≤1) :Allows n (fun i=>f (L i)) x c:=by
 refine ⟨h.1.comp x L.contDiff.contDiffAt,fun j g=>?_⟩; change ‖iteratedFDeriv ℝ j (f ∘ L) x‖ ≤ c; rw [Push.Uniform.iter_lin_at (L:=L) (h.smooth.of_le (by exact_mod_cast g))]; exact (ContinuousMultilinearMap.norm_compContinuousLinearMap_le ..).trans ((mul_le_of_le_one_right (norm_nonneg _) (Finset.prod_le_one (fun i _=>norm_nonneg _) (fun _ _=>p))).trans (h.norm_le j g))
end
abbrev V8(N:Side):= Edge (Seat N)
def bud(T:tangD N)(x:Pane N)(u:ℝ): Pane N:=increment x (u • T)
lemma bud_x(T:tangD N)(x:Pane N): bud T x 0=x:=by unfold bud; simp
abbrev hud_T(k:ℕ)(C:ℝ):Prop:= ∀ N:Side,∀ (x:Pane N) (i:tangD N),‖i‖≤1→ TransK k (increment x) i C
section
variable (T:tangD N)(hp:‖T‖ ≤1)
include hp
lemma bud_T (p:hud_T 7 c)(x:Pane N)(i:ℝ)(h:i∈ Metric.ball (0:ℝ) 1):TransK 7 (bud T x) i c:=by
 let L:ℝ→L[ℝ] tangD N:= (ContinuousLinearMap.id ℝ ℝ).smulRight T
 have he:‖L‖≤1:=by
    refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun v=>?_ ; change ‖v • T‖ ≤_; rw [norm_smul,one_mul]; exact mul_le_of_le_one_right (norm_nonneg _) hp
 have ht:‖L i‖ ≤1:=le_trans (L.le_opNorm _) ((mul_le_mul he (ball_subset_closedBall h|> mem_closedBall_zero_iff.mp) (norm_nonneg i) zero_le_one).trans (one_mul _).le)
 exact fun g=> comps L (p N x _ ht g) he
abbrev lin_T (k:ℕ):ℝ:=2^k* ‖ContinuousLinearMap.mul ℝ (Op SU.F)‖
-- product T pulse with chart uses same U. Norm price independent x.E
lemma weld_T(p:hud_T 7 c)(U:E→Pane N)(x:E)(hq:TransK 7 U x b):TransK 7 (fun y:E×ℝ=> bud T (U y.1) y.2) (x,0) (lin_T 7*c*b):=by
 have he:= bud_T T hp p (1:Pane N) 0 (mem_ball_self zero_lt_one)
 intro i; refine (Allows.germ ?_ (Eventually.of_forall fun (y:E×ℝ)=>Eq.symm (show SU.fund (bud T (U y.1) y.2 i) = SU.fund (bud T 1 y.2 i)*SU.fund (U y.1 i) by simp [bud, RG.increment, SU.fund_mul])))
 exact Allows.bilinear (ContinuousLinearMap.mul ℝ (Op SU.F)) (comps (x:=(x,(0:ℝ))) (f:=fun y:ℝ=> SU.fund (bud T 1 y i)) (ContinuousLinearMap.snd ℝ E ℝ) (show Allows 7 _ _ c from he i) (ContinuousLinearMap.norm_snd_le ..)) (comps (x:=(x,(0:ℝ))) (f:=fun y=> SU.fund (U y i)) (ContinuousLinearMap.fst ℝ E ℝ) (show Allows 7 _ _ b from hq i) (ContinuousLinearMap.norm_fst_le ..)) le_rfl
omit hp
lemma bud_c : Continuous fun i:ℝ × Pane N=> bud T i.2 i.1:=by unfold bud RG.increment; refine continuous_pi fun j=> ?_; exact (SU.group.lieExp_cont.comp (f:=fun a:ℝ × Pane N=> a.1 • T j) (continuous_fst.smul continuous_const)).mul ((continuous_apply j).comp continuous_snd)
end
section
variable (T: tangD (CSide m B))(pT:‖T‖ ≤1) (p:hud_T 7 c)
def coefG (F:SheetT m B)(x:Pantry m B):ℂ:= deriv (fun t=>F (bud T x.1 t,x.2)) 0
namespace Ka
variable {F:SheetT m B} {R:Support (Domain m B)}
lemma inc_w (t:tangD N){x y:Pane N}{R:Support (More N)}(g:Agrees R x y)(z:ℝ):Agrees R (bud t x z) (bud t y z):= fun i u v=> congrArg (_ * ·) (g i u v)
lemma coef_local (H:Ka b 7 e R F v) {x y: Pantry m B}(px:x∈ Lobby m B e)(py:y∈ Lobby m B e)(g:Agrees R x.1 y.1)(k:Phase.Sample.AgreeF (complexA m B R) x.2 y.2): coefG T F x=coefG T F y:=by
 have he(i:Pantry m B)(p:i∈ Lobby m B e):∀ᶠ t in 𝓝 (0:ℝ),(bud T i.1 t,i.2)∈ Lobby m B e:=by
    let f(t:ℝ):= (bud T i.1 t,i.2); have h:Continuous f:= ((bud_c T).comp (continuous_id.prodMk continuous_const)).prodMk continuous_const
    exact h.continuousAt.eventually (lobby_o.mem_nhds (by simp [f,bud_x,p] : f 0∈Lobby m B e))
 unfold coefG; apply Filter.EventuallyEq.deriv_eq; filter_upwards [he x px,he y py] with t hx hy; exact H.watch _ hx _ hy (inc_w T g t) k
include p pT
lemma coef_tone (H:Ka b 7 e R F v) {x:Pantry m B} (px:x∈ Lobby m B e)(hb:c≤ b): HasDerivAt (fun t=> F (bud T x.1 t,x.2)) (coefG T F x) 0:= ((H.narrow hb|>.track ℝ (bud T x.1) 0 x.2 (by rw [bud_x]; exact px) (bud_T _ pT p _ 0 (mem_ball_self zero_lt_one))).smooth.differentiableAt (by norm_num)).hasDerivAt
omit pT p
private lemma moment_1 {X:Type} [TopologicalSpace X](q:X)(g:ℝ→X→ℂ)(P:Set X)(Hp:P∈𝓝 q)(Q:Set ℝ)(u:IsOpen Q)(H: (0:ℝ) ∈ Q) (v:∀ t∈Q,ContinuousOn (g t) P) {Y:ℝ} (w:∀ x∈P,∀ t∈Q,Allows 7 (fun r=>g r x) t Y):ContinuousAt (fun x=> deriv (fun r=>g r x) 0) q:=by
 let K(i:P)(t:ℝ):=g t i.val
 have p:Continuous fun i:P=> fderiv ℝ (K i) 0 1:=Rue.quota_v u (k:=5) (C:=Y) (fun t p i=> w _ i.2 _ p) (fun t p=>continuousOn_iff_continuous_restrict.mp (v _ p)) H 1
 have h:ContinuousOn (fun i=> deriv (fun t=> g t i) 0) P:= continuousOn_iff_continuous_restrict.mpr p
 exact (h q (mem_of_mem_nhds Hp)).continuousAt Hp
private lemma moment₂ {X:Type} [TopologicalSpace X] (P:Set X)(u:IsOpen P)(G:ℝ→ X→X)(h:Continuous (fun x:ℝ×X=> G x.1 x.2))(g:∀ x∈P,G 0 x=x)(F: X→ℂ)(v:ContinuousOn F P)(Y:ℝ)(w:∀ i:X,∀ t∈ Metric.ball (0:ℝ) 1, G t i∈P→Allows 7 (fun r=> F (G r i)) t Y):ContinuousOn (fun x=> deriv (fun r=> F (G r x)) 0) P:=by
 intro x hx; have he:∀ᶠ y in (𝓝 (0,x)),G y.1 y.2∈ P:= h.continuousAt.tendsto.eventually (u.mem_nhds (show G 0 x∈P from g x hx |>.symm ▸ hx))
 obtain ⟨T,pT,S,pS,H⟩:= Filter.mem_prod_iff.mp (show _ ∈ (𝓝 (0:ℝ)) ×ˢ 𝓝 x from nhds_prod_eq (x:=(0:ℝ)) (y:=x) ▸ he) -- tune
 obtain ⟨U,s,hs,hu'⟩:= _root_.mem_nhds_iff.mp pT; let V:= U ∩ Metric.ball (0:ℝ) 1; have hv(t)(p:t∈ V)(i)(a:i∈S): G t i∈P:= H (show (t,i) ∈ T ×ˢ S from ⟨s p.1,a⟩)
 refine (moment_1 x (fun t x=> F (G t x)) S pS V (hs.inter isOpen_ball) ⟨hu',mem_ball_self zero_lt_one⟩ (fun t p=> ?_) (fun i z j p'=> w i j p'.2 (hv j p' i z))).continuousWithinAt
 exact v.comp ((show Continuous (G t) from h.comp (f:=fun i:X=> (t,i)) (continuous_const.prodMk continuous_id)).continuousOn) (fun {i} z=>hv t p i z)
include pT p
lemma coef_ct (H:Ka b 7 e R F v)(hb:c ≤ b): ContinuousOn (coefG T F) (Lobby m B e):=by
 let G'(t:ℝ)(i:Pantry m B):= ((bud T i.1 t,i.2):Pantry m B); have hu:Continuous (fun x:ℝ× Pantry m B=> G' x.1 x.2):= ((bud_c T).comp (show Continuous (fun x:ℝ × Pantry m B=> (x.1,x.2.1)) from continuous_fst.prodMk (continuous_fst.comp continuous_snd))).prodMk (continuous_snd.comp continuous_snd)
 exact moment₂ _ lobby_o G' hu (fun x _=> by simp [G',bud_x]) F H.ct v (fun i j p' u=> (H.narrow hb).track ℝ (bud T i.1) j i.2 u (bud_T T pT p _ _ p'))

omit pT p in
private lemma monoPull {f:E→Bkg N}{x:E}(p:TransK n f x b)(s:b≤e):TransK n f x e:=fun i=> (p i).mono s -- includes issue
lemma coef_arr (H:Ka b 7 e R F v)(hb:c ≤ b)(ht:lin_T 7*c*d≤ b):Ka d 6 e R (coefG T F) v:=by
 refine ⟨H.pos,coef_ct T pT p H hb,fun _ px _ py=>coef_local T H px py,?_⟩
 intro E _ _ _ U x i a w
 -- ambient extension t path around any x. charge at center then differentiableAt near. local derivative = fderiv pulse.
 let t(y:E×ℝ):= (bud T (U y.1) y.2,i); let L:=F ∘ t; let S : E→L[ℝ] (E×ℝ):=ContinuousLinearMap.inl ..
 have hx:L=(F ∘ t):=rfl; have hy:S x=(x,0):=rfl; have hh:Allows 7 L (S x) v:= (H.narrow ht).track (E×ℝ) (fun y=> bud T (U y.1) y.2) (x,0) i (by simp only [bud_x]; exact a) (weld_T T pT p U x w)
 let a: E×ℝ :=(0,1); let A: ((E×ℝ)→L[ℝ]ℂ)→L[ℝ]ℂ:= ContinuousLinearMap.apply ℝ ℂ a; have hA:‖A‖≤1:= by
   refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun z=> (z.le_opNorm a).trans_eq ?_; unfold a; simp -- norm tuple
 have hu:‖S‖≤1:= by
   refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun z=>?_ ; change ‖((z,0):E×ℝ)‖ ≤_; simp
 have he':= ((comps S hh.slide hu).linear A hA); rw [one_mul] at he'
 refine he'.germ ?_
 filter_upwards [S.continuous.continuousAt.tendsto.eventually (hh.1.eventually (by simp))] with y hy
 let Kq(b:ℝ):E×ℝ:=(y,b); have hp: HasDerivAt Kq a 0:= (hasDerivAt_const _ _).prodMk (hasDerivAt_id' _)
 exact Eq.symm (((hy.differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt 0 hp).deriv) -- S bound whnf

end Ka
end
end XGarden
end YM.CF
end
