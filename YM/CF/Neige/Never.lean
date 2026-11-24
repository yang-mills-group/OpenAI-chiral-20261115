import YM.CF.Neige.Wool
set_option autoImplicit false
noncomputable section
namespace YM.CF.Neige
open Char Summit
open Function Filter Set Matrix Lattice Wilson RG Precision Pressure Tree Exterior MeasureTheory Metric Newt Jet
 AnalyticBridge.MarginalMultiplier3b1d AnalyticBridge.LocalGaussianLaws AnalyticBridge.SectorAffine
 AnalyticBridge.NonflatCovarianceLocality.Matching
open Push.SectorMeasure Next.Fluctuations Next.SectorChange Next.SectorChange.Wisps Next.SectorChange.Schur PhysicalNext.JointLoad PatchReads
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius InnerProductSpace
variable {P:RG.Patch}{G:Gauge}{c f:Side}{S:StepData c f}{T:Tube G S}{A A':Stores S}{F F':Forest S.ratio}{k k':S.Choices} {V W:Config G c}{x C:ℝ}{r l:ℕ}
 {Y: LinkArray G (Frozen A x F)}{Y':LinkArray G (Frozen A' x F')}{o:Site c}
variable {α E:Type} [Fintype α][DecidableEq α] [NormedAddCommGroup E][NormedSpace ℝ E] {p:α→Site c}{a:ℕ} {K v d s t:ℝ} {n:ℕ}
open Finset Filter
variable {q:Chi}{D m v' r' U N b:ℝ}
structure Loom (n:ℕ)(x C:ℝ)(V:Config G c)(T:Tube G S)(F:Forest S.ratio)(A: Stores S)(Y:LinkArray G (Frozen A x F))(k:S.Choices)(q:Chi)(D:ℝ)(l:ℕ):Prop where
 major: Protected n (majorX T x A F k q D Y l∘Vmove x V) 0 C
 payX: Protected n (bankX T x A F k q D Y l∘Vmove x V) 0 (C*lamp x)
 lump: Protected n (punt∘bankX T x A F k q D Y l∘Vmove x V) 0 (C*lamp x)
 link: Protected n (layX T x A F k q D Y l∘Vmove x V) 0 C
 back: Protected n (fun y=> (layX T x A F k q D Y l (Vmove x V y)).transpose) 0 C
 errorX: Protected n (fareX T x A F k q D Y l∘Vmove x V) 0 (C*lamp x^3)
 errorH: Protected n (cashX T x A F k q D Y l∘Vmove x V) 0 (C*lamp x)
private lemma stackB(hr:ShardIncome n x v C m T A F V k)(hp:Protected n (fun y=> driftN T x (Vmove x V y) k A F q D Y l) 0 (b*lamp x))(h: Real.exp (-v*↑(radiusB x/60)) ≤ lamp x)(hC:0 ≤ C):
 let Q:= 2^n*(2^n*C*b)*C+C
 Protected n (bankX T x A F k q D Y l ∘Vmove x V) 0 (Q*lamp x):=by
 intro Q
 have he:=fuseP hr.rootX hr.rootT hp; have hh:= attach he (hr.trouble.mono (mul_le_mul_of_nonneg_left h hC))
 refine ((hh.mono (le_of_eq (by dsimp only [Q]; ring))).germ (Eventually.of_forall fun y=>?_))
 dsimp only [Function.comp_apply]; apply congrArg; unfold fuseQ bankX perturb fuseQ driftN majorX musk bedX; rw [Matrix.mul_sub,Matrix.sub_mul]; abel
lemma vicar(X:ℝ)(hp:0 ≤  X) : 0 ≤  varyP n X ∧ 0 ≤  delve n X:=by unfold varyP delve; exact ⟨by positivity,by positivity⟩
def TellerC(n:ℕ)(b C:ℝ): ℝ:=
 let Q:= 2^n*(2^n*C*b)*C+C
 let L:= varyP n Q; let F:= 2^n*C*(1+L)
 1+(b+C)+ Q+ L+ F+delve n Q + (delve n Q + 2^n*(2^n*F*b)*F)
lemma metricsP(hr:ShardIncome n x v C m T A F V k)(hp:Protected n (fun y=> driftN T x (Vmove x V y) k A F q D Y l) 0 (b*lamp x))(hb:0 ≤ b)(h: Real.exp (-v*↑(radiusB x/60)) ≤ lamp x)(hv:lamp x ≤ 1):
 Loom n x (TellerC n b C) V T F A Y k q D l:=by
 let L:= lamp x; have hc:=hr.kernel.nonneg; have hL:0<L:=(Real.exp_pos _).trans_le h
 let Q:= 2^n*(2^n*C*b)*C+C; have hQ:0 ≤ Q:=by unfold Q; positivity
 let K:= varyP n Q; let X:=2^n*C*(1+K); let e:=delve n Q; let Y':=2^n*(2^n*X*b)*X; let Z:=TellerC n b C; have hk:0 ≤ K:=(vicar Q hQ).1; have he:0 ≤ e:=(vicar Q hQ).2; have hX:0 ≤ X:=by unfold X; positivity
 have ht:0 ≤ Y':=by unfold Y'; positivity
 have hz : Z=1+(b+C)+Q+K+X+e+(e+Y'):=rfl
 have hπ:=stackB hr hp h hc; have hr' : Protected n (bankX T x A F k q D Y l∘Vmove x V) 0 (Q*L):=hπ
 let ON(y):=bankX T x A F k q D Y l (Vmove x V y); have hℓ : Protected n (punt∘ON) 0 (K*L):=pitchM hr' hQ hL.le hv
 have hE: Protected n (fun y=>port (ON y)) 0 (1+K):=by apply attach (A:=fun _:Directions G c => (1:Shelf (Rows.In x A F (G:=G)))) (B:=punt ∘ ON) _ (hℓ.mono (mul_le_of_le_one_right hk hv)); exact allows_const _ (by rw [paint_one]; exact ContinuousLinearMap.norm_id_le)
 let T':=layX T x A F k q D Y l; have hh :Protected n (T'∘ Vmove x V) 0 X:=fuseN hr.rootX hE
 have hM :Protected n (fun y=>(T' (Vmove x V y)).transpose) 0 X:=by
    apply ((fuseN hE hr.rootT).mono (le_of_eq (by unfold X; ring))).germ; filter_upwards with y; unfold T' layX; rw [turnQ _ _ (sym_hessN l)]
 have hx: Protected n (fareX T x A F k q D Y l ∘ Vmove x V) 0 (e*L^3):=by
    apply (relic_p hπ hQ hL.le hv).germ; filter_upwards with y; dsimp only [Function.comp_apply,fareX]; rw [legacy_eq _ _ (sym_hessN l)] -- tune
 have hP: Protected n (cashX T x A F k q D Y l ∘ Vmove x V) 0 ((e+Y')*L):=by
    have hl:=fuseP hh hM hp; refine ((subsid (hx.mono (mul_le_mul_of_nonneg_left (pow_le_of_le_one hL.le hv (by decide)) he)) hl).mono (le_of_eq (by unfold Y'; unfold L; ring))).germ (Eventually.of_forall fun y=>?_)
    apply congrArg paintO; dsimp only [Function.comp_apply, fareX, legacy, T',cashX]; let P:=layX T x A F k q D Y l (Vmove x V y)
    change perturb P _-fuseQ P _= perturb P _; unfold perturb fuseQ driftN majorX baseX; rw [Matrix.mul_sub,Matrix.sub_mul]; abel
 refine ⟨?_,hπ.mono (mul_le_mul_of_nonneg_right (show Q  ≤  Z by rw [hz]; linarith) hL.le),hℓ.mono (mul_le_mul_of_nonneg_right (show K  ≤  Z by rw [hz]; linarith) hL.le),hh.mono (show X ≤  Z by rw [hz]; linarith),hM.mono (show X ≤  Z by rw [hz]; linarith),hx.mono (mul_le_mul_of_nonneg_right (show e  ≤  Z by rw [hz]; linarith) (pow_nonneg hL.le _)),hP.mono (mul_le_mul_of_nonneg_right (show e+Y'  ≤  Z by rw [hz]; linarith) hL.le)⟩
 apply (((attach (hp.mono (mul_le_of_le_one_right hb hv)) hr.kernel).mono (show b+C  ≤  Z by rw [hz]; linarith))).germ; exact Eventually.of_forall fun y=>by simp only [driftN,Function.comp_apply,baseX, sub_add_cancel] -- tune
lemma metricsU(K:Teller G)(P:Patch)(n l:ℕ)(hn:2 ≤ n)(hl:l ≤ 18)(ht:P.Branches K.bind G)(W: Push.Uniform.Before G K.top.width K.top.paths K.j K.bind (n+1+1)) :
 ∃ m v C D:ℝ,0< m ∧ 0<v ∧ 0<C ∧∀ᶠ x:ℝ in atTop, ∀ {c f:Side}(S:StepData c f)(T:Tube G S), Cert P K S T x→∀ (A:Stores S)(F:Forest S.ratio)(V:Config G c), A.flags=RG.flags (temp x) V→ sizedP G P K S T F→ ∀ k:S.Choices, ShardIncome n x v C m T A F V k ∧∀ q:Chi,∀(d:ℝ)(Y:LinkArray G (Frozen A x F)), Loom n x D V T F A Y k q d l:=by
 obtain ⟨m,v,C,hm,hv,hC,h⟩:=bear K P n ht; obtain ⟨B,M,hM,H⟩:=shipped K P ht n l hn hl W
 let E:ℝ:= Fintype.card (Site P.L)*( (3:ℝ)^4*Fintype.card Axis)*Fintype.card G.ColorIndex*(B*M)
 refine ⟨m,v,C,TellerC n E C,hm,hv,hC,?_⟩
 filter_upwards [h,H,Work.E01.radiusB_tendsto.eventually_ge_atTop 1000, lamp_s.eventually (ge_mem_nhds zero_lt_one),Newt.smallF (n:=1) hv 1] with x h he hv' hh hG c f S T hx A F V hp hc k
 have hK:= h S T hx A F V hp k; have hB:=he.2.2.1
 refine ⟨hK,fun q d Y=>?_⟩
 have ht:= paintD (B:=d) (Y:=Y) (k:=k) (q:=q) hv' he hx hc hp -- name B
 refine metricsP hK (ht.mono ?_) (show 0 ≤  E by unfold E; positivity) ?_ hh
 swap
 · have h0:0 ≤ temp x:= Work.E04.temp_nonneg x
   rw [pow_one,mul_one] at hG
   refine (le_trans (Real.exp_monotone (mul_le_mul_of_nonpos_left ?_ (neg_nonpos.mpr hv.le))) hG).trans (le_mul_of_one_le_left h0 (one_le_pow₀ (show 1  ≤  (radiusB x:ℝ) by exact_mod_cast (show 1  ≤  radiusB x by omega))))
   exact_mod_cast (show Stores.till x  ≤  radiusB x/60 by unfold Stores.till; omega)
 unfold E; rw [← hx.got]; exact hand_r hv' B hB.le hM.le
end YM.CF.Neige
