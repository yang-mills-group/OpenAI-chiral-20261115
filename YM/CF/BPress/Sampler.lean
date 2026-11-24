import YM.CF.BPress.Show
import YM.CF.BPress.CardMenu
/-! VolumeB-gate/gauge change. Angular samples per column and per gap, using ALL N lifts, same marks as test. Integrating all templates, not assuming positivity of the resulting integral. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BPress
open Function MeasureTheory LocalH Lattice SU Mag Cube Grid Filter Branch Tunnel Finset RG Wilson
open Law Push.SectorMeasure Env
open scoped Topology BigOperators Classical Matrix
variable {T : Sheet.Atlas}{C C' Lf y : ℝ}{b : ℕ}
section data
variable {s : Side}{B:BandWidth}(X : Bands s B)
namespace Bands
abbrev Sky:= X.Air→ E
abbrev Rain:= chain group.probHaar X.Air
@[simp] lemma Depth_p {k:ℕ} (h:k<B.D) : k+1 ≤ B.D := h
def atmospheric (x:X.Sky) : Micro s := fun i=> if h:∃ a:X.Air, X.skylink a=i then x h.choose else 1
def skyH (U:Micro s) (x:X.Air):= U (X.skylink x)
lemma rain_mp : MeasurePreserving X.skyH (prior group s) X.Rain:= keys _ _ X.sky_inj
lemma mat_atm (x:X.Sky)(i:X.Air): X.atmospheric x (X.skylink i)=x i:= by unfold atmospheric; rw [dif_pos ⟨i,rfl⟩]; exact congrArg x (X.sky_inj (Exists.choose_spec (show ∃ a, X.skylink a=X.skylink i from ⟨i,rfl⟩))) -- tune
lemma atmospheric_meas : Measurable X.atmospheric:=by apply measurable_pi_lambda; intro i; unfold atmospheric; split <;> fun_prop
lemma sky_air (x:Micro s): Set.EqOn (X.atmospheric (X.skyH x)) x X.air:=by intro i p; obtain ⟨j,_,rfl⟩:= mem_image.mp (mem_coe.mp p); rw [X.mat_atm]; rfl
lemma atm_hold (u:X.Sky): X.hold (X.atmospheric u):= fun _ h=> dif_neg (fun hx=>disjoint_left.mp X.pole_air h (let ⟨u,k⟩:= hx; mem_image.mpr ⟨u,mem_univ _,k⟩))

def ownerX (i : Link s) : X.Index:=if p:∃ a,i∈X.pay a then p.choose else 0
lemma owner_b (i: Link s)(a:X.Index)(p:i∈X.pay a): X.ownerX i=a:=by unfold ownerX; rw [dif_pos ⟨a,p⟩]; exact X.pay_uniq (Exists.choose_spec (show ∃ a,i∈X.pay a from ⟨a,p⟩)) p

def clear (v z: Micro s):= rep X.coins z (X.tone v)
lemma clear_joint : Measurable (fun x:Micro s× Micro s=> X.clear x.1 x.2):=by
 unfold clear; exact (Law.rep_joint X.coins).comp (measurable_snd.prodMk (X.tone_meas.comp measurable_fst))
lemma clear_hold (x y:Micro s): X.hold (X.clear x y):=fun i k=> (Law.rep_R X.coins y (X.tone x) i (disjoint_left.mp X.pole_dis k)).trans (X.tone_hold x i k)
lemma clear_air (x y : Micro s): Set.EqOn (X.clear x y) x X.air:= fun i p=> by rw [clear,rep_R _ _ _ _ (disjoint_left.mp X.air_dis p),tone,rep_R _ _ _ _ (disjoint_left.mp X.pole_air.symm p)]
lemma same_weather {x y:Micro s}(p:Set.EqOn x y X.air)(z:Micro s): X.clear x z=X.clear y z:=by
 funext i; rcases X.kind i with v|v|v; exact (X.clear_air x z v).trans ((p v).trans (X.clear_air y z v).symm); rw [clear,clear,rep_L _ _ _ _ v,rep_L _ _ _ _ v]; exact (X.clear_hold x z i v).trans (X.clear_hold y z i v).symm
lemma clear_coin (v u:Micro s)(i:X.Index)(k:Link s)(p:k∈ X.pay i): X.clear v u k=u k:=rep_L _ _ _ _ (X.coins_c i p)
lemma splice_tone (x y:Micro s): X.tone (rep X.coinsᶜ x y)= X.clear x y:= by
 funext i; rcases X.kind i with v|v|v; rw [X.clear_air x y v]; unfold tone; rw [rep_R _ _ _ _ (disjoint_left.mp X.pole_air.symm v), rep_L _ _ _ _ (mem_compl.mpr (disjoint_left.mp X.air_dis v))]
 rw [tone,clear,rep_R _ _ _ _ (disjoint_left.mp X.pole_dis.symm v),rep_R _ _ _ _ (fun p=>mem_compl.mp p v),rep_L _ _ _ _ v]
 exact (X.tone_hold _ i v).trans (X.clear_hold x y i v).symm
end Bands
open Bands
namespace Net
variable (F:Net s T Lf y C C' b)(w:X.Slates)
def see (x : Micro s) (i:X.Index):= X.putF T y x i (w i)
-- `chartH` price on charged links. defined at all
-- owner fallback; actual links are via rep. use full independent ball samples even on unused links
def chartH (x:Micro s) : Micro s:= fun i=> F.avgN X x (X.ownerX i) (see (T:=T) (y:=y) X w x (X.ownerX i)) i
def play (x:Micro s)(u:Micro s): Micro s := X.clear x (F.chartH X w x * u)
def roll (x:X.Sky) := F.play X w (X.atmospheric x)
lemma chartH_meas : Measurable (F.chartH X w):=by
 apply measurable_pi_lambda; intro i; unfold chartH avgN see; split; exact measurable_const; exact (measurable_pi_apply i).comp ((F.template_meas _).comp (((X.mark _).reads_cont.measurable).prodMk (X.putF_meas _ _ _ _))) -- tune stuck
lemma play_joint : Measurable (fun x:Micro s×Micro s=> F.play X w x.1 x.2):= X.clear_joint.comp (f:=fun x:Micro s×Micro s=>(x.1,F.chartH X w x.1*x.2)) (measurable_fst.prodMk (((F.chartH_meas X w).comp measurable_fst).mul measurable_snd))
lemma roll_joint : Measurable (fun x:X.Sky×Micro s=> F.roll X w x.1 x.2):= (F.play_joint X w).comp (f:=fun x:X.Sky×Micro s=>(X.atmospheric x.1,x.2)) ((X.atmospheric_meas.comp measurable_fst).prodMk measurable_snd)
lemma avg_air {x x' : Micro s}(h : Set.EqOn x x' X.air)(i:X.Index): F.avgN X x i (see (T:=T) (y:=y) X w x i)=F.avgN X x' i (see (T:=T) (y:=y) X w x' i):=by
 unfold avgN see; split; rfl; next p=> rw [X.putF_air _ _ h, (X.mark i).reads_crown x x' (h.mono (X.crown_air i (by simpa using p)))]
lemma chart_air {x x':Micro s}(h:Set.EqOn x x' X.air): F.chartH X w x= F.chartH X w x':=funext fun i=> congrFun (F.avg_air X w h (X.ownerX i)) i
lemma play_air {x x':Micro s}(h:Set.EqOn x x' X.air)(u: Micro s): F.play X w x u= F.play X w x' u:=by rw [play,play, F.chart_air X w h]; exact X.same_weather h _
lemma roll_hold (x:X.Sky)(u:Micro s): X.hold (F.roll X w x u):= X.clear_hold _ _
lemma roll_sky (x:X.Sky)(u:Micro s): X.skyH (F.roll X w x u)= x:=funext fun i=> (X.clear_air (X.atmospheric x) (F.chartH X w (X.atmospheric x)*u) (mem_image_of_mem X.skylink (mem_univ i))).trans (X.mat_atm ..)
lemma chart_pay (x:Micro s)(i:X.Index)(j:Link s)(p:j∈ X.pay i): F.chartH X w x j= F.avgN X x i (see (T:=T) (y:=y) X w x i) j:=by rw [chartH, X.owner_b _ _ p]
lemma play_ne {x u:Micro s} (p: 0<xi y)(v:xi y ≤ 1)(g:∀ i∈ X.coins, group.chord (u i)≤xi y)(i:X.Index): let U:=F.play X w x u; 0<F.takeN X U i (see (T:=T) (y:=y) X w U i):=by
 intro U; rw [F.charge_all X U (X.clear_hold x (F.chartH X w x * u))]; apply prod_pos; intro l k
 have hx : F.avgN X U i (see (T:=T) (y:=y) X w U i) l=F.chartH X w x l:=(congrFun (F.avg_air X w (X.clear_air x (F.chartH X w x*u)) i) l).trans (F.chart_pay X w x i l k).symm
 rw [hx,chord.ballDensity, if_pos ?_]; exact chord.charge_pos p v; unfold U play; rw [X.clear_coin _ _ _ _ k, Pi.mul_apply]; let H:=F.chartH X w x l; change chord (H* _) H ≤ _; nth_rw 2 [←mul_one H]; rw [chord.left,chord.one]; exact g _ (X.coins_c _ k)
end Net
end data
namespace Net
open Bands
variable {N:Side}{B:BandWidth}(X:Bands (More N) B)(F:Net (More N) T Lf y C C' b)(w:X.Slates) [IsProbabilityMeasure (noise SU.group (xi y))]
lemma clear_pay (x y' : Micro (More N)): F.stake X w (X.clear x y')=∏ i∈ X.coins,chord.ballDensity (xi y) (F.chartH X w x i) (y' i):=by
 rw [stake, coins, prod_biUnion]; swap; · intro i vi j vj p; exact disjoint_left.mpr fun x h v=> p (X.pay_uniq h v)
 apply prod_congr rfl; intro i _; rw [F.charge_all X (X.clear x y') (X.clear_hold x y')]; apply prod_congr rfl; intro j k; rw [X.clear_coin _ _ _ _ k, F.chart_pay X w x _ _ k]; exact congrArg (fun z=> chord.ballDensity (xi y) z (y' j)) (congrFun (F.avg_air X w (X.clear_air x y') i) j)
include w in -- variable order
lemma cash_out (g:Micro (More N)→ℂ)(h:Envelope g)(x:Micro (More N)) :
   (∫ v, F.stake X w (X.clear x v) • g (X.clear x v) ∂prior group _)=(∫ v, g (F.play X w x v) ∂chain (noise group (xi y)) _):=by
 simp_rw [F.clear_pay X w]; exact (choice_at X.coins g h (F.chartH X w x) _ (X.tone x)).symm
attribute [local instance] opCStarAlgebra
-- without Fock specs for column uses
omit w
open Girt Skye Scree
lemma attic (f:X.Slates→Micro (More N)→ℂ)(h:∀ i,Envelope (f i)): (∫ U, (∑ i∈X.permit T y (X.tone U), F.stake X i (X.tone U) • f i (X.tone U)) ∂prior group _)=∫ x, (∑ i∈X.permit T y (X.atmospheric x),∫ v, f i (F.roll X i x v)∂chain (noise group (xi y)) _)∂X.Rain:=by
 let μ:=prior group (More N); let ν:= chain (noise group (xi y)) (Link (More N)); let g(v : Micro (More N)):= ∑ i∈X.permit T y v, F.stake X i v • f i v; have he : Envelope g:= Law.partialP (X.permit T y) (X.permit_meas T y) (fun i v=> F.stake X i v • f i v) fun i=> Env.scale (F.shows_stake ..) (h i)
 let W(v:X.Sky):= ∑ i∈X.permit T y (X.atmospheric v), ∫ x,f i (F.roll X i v x) ∂ν
 have hv(i) : Envelope (fun v=> ∫ x, f i (F.roll X i v x)∂ν):= marginalP (f:=fun x=> f i (F.roll X i x.1 x.2)) (Env.along (h i) (F.roll_joint X i)) ν; have ht : Envelope W:= Law.partialP _ (fun i=> X.atmospheric_meas (X.permit_meas T y i)) _ hv
 rw [restore μ _ _ X.rain_mp W (integrableX ht _)]; change (∫ x,g (X.tone x)∂Law.chain group.probHaar _)= (∫ x,W (X.skyH x)∂Law.chain group.probHaar _); rw [splice_mem X.coinsᶜ group.probHaar (fun x=> g (X.tone x)) (Env.along he X.tone_meas)] -- tune definally
 apply integral_congr_ae; apply Eventually.of_forall; intro x; dsimp only; let V:= X.skyH x; let z:= X.atmospheric V; have hx:Set.EqOn z x X.air:= X.sky_air x -- alias set EqOn
 unfold g; simp_rw [X.splice_tone]; have ha(y':Micro (More N)): X.permit T y (X.clear x y')=X.permit T y z:=X.permit_air T y ((X.clear_air x y').trans hx.symm)
 simp_rw [ha]; rw [integral_finsetSum _]; unfold W; apply sum_congr rfl; intro i p; exact (F.cash_out X i (f i) (h i) x).trans (integral_congr_ae (Eventually.of_forall fun u=> congrArg (f i) (F.play_air X i hx u).symm))
 intro i _; exact integrableX (Env.along (Env.scale (F.shows_stake X i) (h i)) (X.clear_joint.comp (f:=fun y:Micro (More N)=>(x,y)) (measurable_const.prodMk measurable_id))) _
end Net
end YM.CF.BPress
