import YM.CF.Souk.Seal
/-! Trace-delta norms for true thermal. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.Souk
open Function Filter Set Matrix Lattice Wilson RG Precision Pressure Tree Exterior MeasureTheory Metric
 AnalyticBridge.MarginalMultiplier3b1d AnalyticBridge.LocalGaussianLaws AnalyticBridge.SectorAffine Char Jet Newt Hors Neige
open Push.SectorMeasure AnalyticBridge.RelativeLogdet.Ink
open Push
open Push.Uniform (curve Slope meetVar Positions upperCol lowerCol block meet_derivative bolt address Primary tint Multiplicity countCost)
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius InnerProductSpace
variable {P:RG.Patch}{G:Gauge}{c f:Side}{S:StepData c f}{T:Tube G S}{K:Teller G}{F:Forest S.ratio}{X E B:Type}[NormedAddCommGroup E][NormedSpace ℝ E][NormedAddCommGroup B][NormedSpace ℝ B]{t x s D A C Q V r:ℝ}{i n l:ℕ}
variable {ι τ:Type} [Fintype ι][Fintype τ] [DecidableEq τ]
open Planned.JetPort Finset
open Next.SectorChange PatchReads Next.SectorChange.Wisps
variable{X Y:Fish ι→ Fish τ}{x':Fish ι}{p:ι→Site c}{m:τ→Site c}{b j:ℕ}
lemma palm (h:Uniform.Envelope p m s i X 0 C)(hy:ContDiffAt ℝ i X 0)(hs:0<s)(hp:0 ≤ C)(hq:n+1 ≤ i)(q:Fin (n+1)→ι)(hm:Multiplicity m j)(H:Finset τ)(ht:∀ i∈H,b ≤ separation (p (q (Fin.last n))) (m i)) (ht':0 ≤ t)(hr:t ≤ 1):
 (∑ i∈H,|Uniform.entry (fun y=>X (t•y)) 0 q i|) ≤ C*Real.exp (-(s/2)*b)*(j*countCost (s/2)):=by
 let L:τ→ℝ:=fun i=>Uniform.Decay (s/2) (p (q (Fin.last n))) (m i); let Z:=Real.exp (-(s/2)*b); have hZ:0 ≤ Z:=(Real.exp_pos _).le
 simp_rw [entry_scale X t q 0 (show ContDiffAt ℝ (n+1:ℕ) X (t • 0) by rw [smul_zero]; exact hy.of_le (Nat.cast_le.mpr hq)),smul_zero, Pi.smul_apply,smul_eq_mul,abs_mul]
 have he v (hv:v∈H): |Uniform.entry X 0 q v| ≤ C*Z*L v:=by
    apply (h _ (by omega) hq q v).trans
    rw [glaze_last,mul_assoc]; apply mul_le_mul_of_nonneg_left ?_ hp; have h' : Uniform.Decay s (m v) (p (q (Fin.last n)))  ≤ Z* L v:=by
       rw [Uniform.decay_comm,decay_div]; apply mul_le_mul_of_nonneg_right _ (Uniform.decay_pos ..).le; unfold Z Uniform.Decay; apply Real.exp_monotone; apply mul_le_mul_of_nonpos_left _ (neg_nonpos.mpr (half_pos hs).le); exact_mod_cast (ht _ hv)
    refine (mul_le_of_le_one_right (Uniform.decay_pos ..).le (Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (by linarith) (by positivity)))).trans h'
 apply (sum_le_sum (fun v hv=> (mul_le_of_le_one_left (abs_nonneg _) ((abs_of_nonneg (pow_nonneg ht' _)).trans_le (pow_le_one₀ ht' hr))).trans (he v hv))).trans; rw [← Finset.mul_sum]; exact mul_le_mul_of_nonneg_left ((sum_le_sum_of_subset_of_nonneg (subset_univ H) (fun v _ _=> (Uniform.decay_pos ..).le)).trans (hm.count m (half_pos hs) _)) (mul_nonneg hp hZ)
section curve
variable{z:fieldDir G c 1→AxisChart G F}{k:S.Choices}
abbrev flute(F:Forest S.ratio)(z:Mast G c→Fish (Key F G))(s:ℝ)(y:Mast G c):=curve z (s•y)
lemma ray_of (s:ℝ)(f:Fish ι→Fish τ)(x:Fish ι) : let L:= fun y=>curve f (s•y); L x=upperCol (s•x) + lowerCol (f (s•x)):= Uniform.meet_columns .. -- tune
abbrev chit(G:Gauge)(P:Patch)(K:Teller G)(x:ℝ)(l:ℕ):=raised G P.L ((l+1)*radiusB x)+1
def GoodsR(F:Forest S.ratio)(m z:Mast G c→ Fish (Key F G))(s C t:ℝ): Prop:=
 let X:=flute F m s; let Y:=flute F z s; X 0=0∧Y 0=0∧ContDiffAt ℝ 2 X 0∧ContDiffAt ℝ 2 Y 0∧∀ i:ℕ,i<2→∀ j:Fin (i+1)→Primary c G,costU (Uniform.entry Y 0 j) ≤ C ∧ costU (Uniform.entry (X-Y) 0 j) ≤ t
lemma glow_up(x:Fish τ) : costU (lowerCol (ι:=ι) x)=costU x:=by unfold costU; rw [Fintype.sum_sum_type]; change ∑ i:ι,|(0:ℝ)|+ _=_; simp; rfl -- remove G
lemma horn(h:Cert P K S T x)(hr:Ready T x)(U:Mast G c→Fish (Key F G))(v:Fin (n+1)→Primary c G)(ht: ∀ i : Mast G c,‖i‖<1 → orbitP T x (facadeX G (s • i)) k (bareStores S) F Chi.canonical 1 1 l = leaveX F x (U i))(hp: ContDiffAt ℝ (n+1:ℕ) U 0) :∀ j,j∉ coverX T x F l (v (Fin.last n))→Uniform.entry U 0 v j=0:=by
 intro j hh; let L :=ContinuousLinearMap.proj (R:=ℝ) (φ:=fun _ :Key F G=> ℝ) j; let V:=L ∘ U
 have hV:ContDiffAt ℝ (n+1:ℕ) V 0:= L.contDiff.contDiffAt.comp _ hp
 have he: Uniform.entry V 0 v=Uniform.entry U 0 v j:=by unfold Uniform.entry V; rw [L.iteratedFDeriv_comp_left hp le_rfl]; rfl
 rw [← he]; apply Uniform.Requests.zero (s:=ball (0:Mast G c) 1) (l:=address F G ∘ Sum.inl) (y:=address F G (.inr j)) (R:=touchH ((l+1)*radiusB x) S.patch.L) ?_ (ball_mem_nhds _ zero_lt_one) hV _ (Fin.last n) ?_
 · intro a ha b hb H; have he:= lokal hr k l s F Chi.canonical 1 a b j H; dsimp only at he; rw [ht _ (mem_ball_zero_iff.mp ha), ht _ (mem_ball_zero_iff.mp hb)] at he; exact he
 rw [separation_comm]; simpa [coverX] using hh
lemma dale(K:Teller G)(P:Patch)(p:P.Branches K.bind G)(l:ℕ)(hG:G.Simple)(W: Uniform.Before G K.top.width K.top.paths K.j K.bind 5) : ∃ C:ℝ,0<C ∧∀ᶠ x:ℝ in atTop, ∀ {c f:Side}(S:StepData c f)(T:Tube G S)(F:Forest S.ratio), Cert P K S T x → sizedP G P K S T F → ∀ z,W.Service F T.high T.up z →∀ k:S.Choices,
 GoodsR F (sol S T k x F l) (Uniform.station z) (temp x) C (C*chit G P K x l*temp x^(l+2)):=by
 obtain ⟨a,A,v,D,b,ha,hA,hv,hD,hb,H⟩:= yields K 3 l (by decide) P p W; obtain ⟨u,ε,hu,hε,hF⟩:=cup 3 l (by decide) P K p W
 let Y':= W.tables K.top.clip P; let T:=pathRate Y' 2; let X:= if 0<T then T else 1; let g:=Uniform.townCost G
 let Z₀:= (pathCost Y' 2)*(g*countCost (X/2)); let C:=max (A+1) Z₀; have hC:0<C:=lt_of_lt_of_le (by linarith only [hA] : 0<A+1) (le_max_left ..)
 have hS: Tendsto temp atTop (𝓝 0):=by simpa using Work.E09.radiusB_temp 0
 refine ⟨C,hC,?_⟩
 filter_upwards [H,hF,hS.eventually (ge_mem_nhds (lt_min (lt_min hb hε) zero_lt_one)), eventually_gt_atTop (0:ℝ), Newt.smallF (n:=l+2) (half_pos hv) (D*(g*countCost (v/2))), PatchReads.reserve K P] with x hx hk he hx' hg he'
 intro c f S U F hr hv₀ z hz k; have hu': temp x ≤ min b ε:= he.trans (min_le_left ..); let t:=temp x; have ht:0<t:= Work.E09.temp_pos hx'; let m:=sol S U k x F l; let V(y:Mast G c):= t • y; let P':=Uniform.station z
 obtain ⟨z',hz',hZ,hP,hJ⟩:=hx S U F hr hv₀; obtain ⟨hU,hh⟩:= hk S U F hr hv₀ t ht le_rfl (hu'.trans (min_le_right ..)) l le_rfl
 let f:=curve P'; let H:=flute F m t; let K':=m∘V; let U':=P'∘V
 have hp:H=fun y=>upperCol (t•y)+lowerCol (K' y):= funext (ray_of t m)
 have hq: f∘V=fun y=>upperCol (t•y)+ lowerCol (U' y):= funext (ray_of t P')
 have hv(v:Mast G c)(hv:‖v‖<1):= (hh Chi.canonical 1 1 k v hv).1; have hy:‖(0:Mast G c)‖<1:=by simp
 have hK': Jet.Allows 3 K' 0 (u*t):= hU.root k 0 hy; have hL:ContDiffAt ℝ (2:ℕ) K' 0:=(hK'.order (by decide)).smooth
 have hw':V 0=0:=smul_zero _; have hh:H 0=0:=by
    have he:K' 0=0:=by
       have h:=hv 0 hy; change orbitP _ x (facadeX G (V 0)) _ _ _ _ _ _ _=_ at h
       rw [hw',show facadeX G (0:Mast G c)=1 from by simp [facadeX],Vol.shyX hG hr.funds.1 _ _ _ _ _] at h; rw [←visit_left (F:=F) (x:=x) (K' 0),show leaveX F x (K' 0)=0 from h.symm,map_zero]
    rw [hp]; dsimp only; rw [he,smul_zero,map_zero,map_zero,add_zero]
 let R:=address F G; obtain ⟨M,N,hx,hv'⟩:=hr.funds.1.feeds; have h:=hr.funds.1; rw [←h.high] at hx
 have hQ:Counter Y' 2 k U.high U.up z:=by unfold Y'; rw [←h.high,←hr.got]; exact Counter.service hz hx hr.pace h.atStep h.knobs k
 obtain ⟨hA,hC⟩:= hQ.carrier (x:=0) (by unfold Y'; rw [←h.high,←hr.got]; exact mem_ball_self hz.x_pos); obtain ⟨hT,hM,hI,hY⟩:=hC 2 (by decide)
 let S':=Uniform.station z'∘V; let Q':=K'-U'; have hV: ContDiff ℝ ω V:= contDiff_id.const_smul t
 have he'': S'=ᶠ[𝓝 0] U':= by
    have hh:= hz'.is_extension hz.critical; let L(y:Mast G c):= tint G _ (V y); have h:L 0=0:=by unfold L; rw [hw',map_zero]
    have ht : Tendsto L (𝓝 0) (𝓝 0):=by
       rw [← h]; exact ((tint G _).continuousAt.comp (f:=V) hV.continuous.continuousAt)
    filter_upwards [ht.eventually hh] with x hx; unfold S' U' P' Uniform.station Function.comp; rw [show z' _=z _ from hx.symm]
 have hB:= hZ 0 (by simpa using ha.le); have ht':ContDiffAt ℝ (3:ℕ) S' 0:= ((hw'.symm ▸ hB.1: ContDiffAt ℝ ω (Uniform.station z') (V 0)).comp (f:=V) _ hV.contDiffAt).of_le le_top
 have hK : Jet.Allows 3 Q' 0 (A*t^(l+2)):= ((hJ k _ ht le_rfl (hu'.trans (min_le_left ..))).due 0 hy).germ (he''.mono fun x hx=> by change K' x-S' x=_; rw [hx]; rfl) -- tune
 have hs:ContDiffAt ℝ (2:ℕ) U' 0:=(ht'.congr_of_eventuallyEq he''.symm).of_le (by norm_num)
 change H 0 =0 ∧ _; refine ⟨hh,?_,?_,?_,fun i hi j=>?_⟩
 · unfold flute curve Uniform.station; simp [ (show z 0=0 from hz.critical.1)]; unfold meetVar; rw [show ((0: Mast G c),(0: Fish (Key F G)))=0 from rfl,map_zero] -- name
 · change ContDiffAt ℝ 2 H 0; have h:ContDiffAt ℝ (2:ℕ) H 0:=by rw [hp]; exact ((upperCol (τ:=Key F G)).contDiff.contDiffAt.comp (f:=V) _ (hV.of_le le_top).contDiffAt).add ((lowerCol (ι:=Primary c G)).contDiff.contDiffAt.comp (f:=K') _ hL)
   simpa using h
 · exact ((hw'.symm ▸ hA:ContDiffAt ℝ ω f (V 0)).comp (f:=V) _ hV.contDiffAt).of_le le_top
 -- bound
 have heL:i+1≤2:=by omega
 change costU (Uniform.entry (f∘V) 0 j) ≤ C ∧ costU (Uniform.entry (H - f ∘ V) 0 j) ≤ _
 constructor
 · let h:=palm hI (hA.of_le le_top) hT hM.le heL j (Uniform.town F) Finset.univ (fun _ _=> show 0 ≤ _ from Nat.zero_le _) ht.le (he.trans (min_le_right ..))
   have hy:T>0:=hT; simp only [Nat.cast_zero,mul_zero,Real.exp_zero,mul_one] at h
   refine h.trans ?_; apply le_max_of_le_right; unfold Z₀ X; rw [if_pos hy] -- tune
 rw [show H-f ∘ V=lowerCol (ι:=Primary c G) ∘ Q' from ?_]; swap
 · rw [hp,hq]; funext y; unfold Q'; simp only [Pi.sub_apply,Function.comp_apply,map_sub]; abel
 have hG: Uniform.entry ((lowerCol (ι:=Primary c G))  ∘ Q') 0 j= lowerCol (Uniform.entry Q' 0 j):=by -- toFun
    unfold Uniform.entry; erw [ContinuousLinearMap.iteratedFDeriv_comp_left (lowerCol (ι:=Primary c G)) hK.smooth (by norm_cast; omega)]; rfl
 rw [hG,glow_up]; let B:=coverX U x F l (j (Fin.last i)); let g₀:= address F G ∘ Sum.inl; let g₁:=address F G ∘ Sum.inr; let z₀:=Hors.raised G P.L ((l+1)*radiusB x)
 let P''(i':Key F G):=|Uniform.entry Q' 0 j i'|; let A₀(w: Key F G):=|Uniform.entry S' 0 j w|
 have hR: (B.card:ℝ) ≤ z₀:=by unfold z₀; rw [←hr.got]; exact lit F _ _
 have he₂ a(ha:a∈ Bᶜ):P'' a=A₀ a:=by
    have hi: ∀ j',j'∉B → Uniform.entry K' 0 j j'=0:=horn hr (he' _ _ hr.got hr.size hr.funds.1) _ j hv (hL.of_le (by exact_mod_cast heL))
    have he : Uniform.entry Q' 0 j=Uniform.entry K' 0 j-Uniform.entry S' 0 j:=by
       unfold Uniform.entry Q'; rw [iteratedFDeriv_sub_apply (hL.of_le (by exact_mod_cast heL)) (hs.of_le (by exact_mod_cast heL)),← (he''.iteratedFDeriv ℝ (i+1)).eq_of_nhds]; rfl
    unfold P'' A₀; rw [he,Pi.sub_apply,hi _ (Finset.mem_compl.mp ha),zero_sub,abs_neg]
 have hb(a): P'' a ≤ A*t^(l+2):= (norm_le_pi_norm (Uniform.entry Q' 0 j) a).trans ((Uniform.entry_bound _).trans (hK.norm_le _ (by omega)))
 let Y:= t^(l+2); have h₀: A>0:=by assumption
 have hZ:0 ≤ z₀:=(Nat.cast_nonneg _).trans hR; have hY:0 ≤ Y:=pow_nonneg ht.le _
 have hu:(∑ i∈B,P'' i) ≤ z₀*(A*Y):=by apply (Finset.sum_le_sum (fun i _=>hb i)).trans; rw [Finset.sum_const,nsmul_eq_mul]; exact mul_le_mul_of_nonneg_right hR (mul_nonneg h₀.le hY)
 have hv:0<v:=by assumption
 have hb:(∑ i∈Bᶜ,A₀ i) ≤Y:=by
    apply (palm hB.2.2.2 hB.2.1.smooth hv hD.le (by omega) j (Uniform.Multiplicity.comp (Uniform.town F) Sum.inr_injective) Bᶜ (b:=Stores.till x) ?_ ht.le (he.trans (min_le_right ..))).trans (le_trans (le_of_eq (by unfold g at hg ⊢; ring)) hg); intro a ha
    have hh:= (not_le.mp (by simpa only [Finset.mem_compl, coverX,Finset.mem_filter,Finset.mem_univ,true_and,B,g₀,g₁,Function.comp_apply] using ha) : touchH ((l+1)*radiusB x) S.patch.L < separation (g₀ (j (Fin.last i))) (g₁ a)); have hp: Stores.till x ≤ (l+1)*radiusB x:=le_trans (b:=radiusB x) (by unfold Stores.till; omega) (le_mul_of_one_le_left (by omega) (by omega)); apply hp.trans; refine le_trans ?_ hh.le; unfold touchH; apply (le_mul_of_one_le_left (by omega) (show 1 ≤ S.patch.L.val from S.patch.L.property)).trans; omega
 change (∑ i,P'' i) ≤ C*(z₀+1)*Y; rw [←Finset.sum_add_sum_compl B, Finset.sum_congr rfl he₂]; apply (add_le_add hu hb).trans
 apply le_trans ?_ (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left (A+1) Z₀) (by linarith only [hZ])) hY); nlinarith only [h₀,hY,mul_nonneg h₀.le hY,mul_nonneg hZ hY]
end curve
end YM.CF.Souk
