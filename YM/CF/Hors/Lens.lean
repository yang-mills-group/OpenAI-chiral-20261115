import YM.CF.Hors.Post
set_option autoImplicit false
noncomputable section
namespace YM.CF.Hors
open Function Filter Set Matrix Lattice Wilson RG Precision Pressure Tree Exterior MeasureTheory Metric
 AnalyticBridge.MarginalMultiplier3b1d AnalyticBridge.LocalGaussianLaws AnalyticBridge.SectorAffine Char Jet Newt
open Push.SectorMeasure AnalyticBridge.RelativeLogdet.Ink
open Push
open Push.Uniform (curve Slope meetVar Positions upperCol lowerCol block meet_derivative bolt)
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius InnerProductSpace
variable {P:RG.Patch}{G:Gauge}{c f:Side}{S:StepData c f}{T:Tube G S}{K:Teller G}{F:Forest S.ratio}{X E B:Type}[NormedAddCommGroup E][NormedSpace ℝ E][NormedAddCommGroup B][NormedSpace ℝ B]{t x s D A C Q V r:ℝ}{i n l:ℕ}
open Push.Uniform (address Primary tint)
open Next.SectorChange Next.SectorChange.Wisps PatchReads
set_option maxHeartbeats 600000 in
lemma push_paid(K:Teller G)(P:Patch)(p:P.Branches K.bind G)(n l:ℕ)(hn:1 ≤ n)(W:Uniform.Before G K.top.width K.top.paths K.j K.bind (n+3)) :
 ∃ A ε:ℝ,0<A∧0<ε∧∀ᶠ x:ℝ in atTop,∀ {c f:Side}(S:StepData c f)(T:Tube G S)(F:Forest S.ratio), Cert P K S T x →sizedP G P K S T F → ∃ z,W.Service F T.high T.up z ∧∀ (k:S.Choices) (u:Mast G c), ∀ s, 0<s → temp x ≤ s → s ≤ ε → ‖u‖<1 →
 let m:=fun y=> sol S T k x F l (s•y); let v:=fun y=>Uniform.station z (s•y)
 let f:=firmX (clipped T x F k) m s-firmX (costP F k T.high T.up) v s
 ContDiffAt ℝ (n+1:ℕ) f u ∧ ∀ t,Allows n (glance f t) u (A*s^(l+3)*(raised G P.L ((l+1)*radiusB x)+1)):=by
 obtain ⟨C,r,hC,hr,H⟩:=cup (n+1) l (by omega) P K p W
 obtain ⟨a,t,h,D,v,ha,ht,hh,hD,hv,H'⟩:=yields K (n+1) l (by omega) P p W
 let A:=max D C; have hA:=hC.trans (le_max_right D C); have hF:0<A:= zero_lt_one.trans_le hA
 obtain ⟨B,d,b,hB,hd,hb,hP⟩:=mat_paid K P (n+3) (by omega) W
 obtain ⟨hx,hQ⟩:=tip_left (n+1) (l+2) P K
 let M(w:ℝ):= 1+Uniform.townCost G*Uniform.countCost w
 let R:= min B 1; let Y:= b*M d^(n+1); let Z:= M (peak (n+1) P K)^n
 let V:= composeCost n Z 1+ 2^n*composeCost n Y 1*t
 let N:= V*(2^n*A+1)
 have hX q (hq:0<q):0<M q:=add_pos_of_pos_of_nonneg zero_lt_one (mul_nonneg (by positivity) (Uniform.count_pos hq).le)
 have hy: 0<Y:= mul_pos hb (pow_pos (hX _ hd) _); have hz:0<Z:=pow_pos (hX _ hx) _; have hV:0<V:=by unfold V Jet.composeCost; positivity; -- yes
 have hR:0<R:=lt_min hB zero_lt_one; let q:= min R a
 have hq:0<q:=lt_min hR ha
 refine ⟨N,min r (min v ((q/2)/(3*A))), by unfold N; positivity, lt_min hr (lt_min hv (by positivity)), ?_⟩
 filter_upwards [PatchReads.reserve K P,H,H',hQ] with x hg Hx HY HX
 intro c f S T F H h; obtain ⟨z,hZ,hL,hg₀,hJ⟩:= HY S T F H h; let z':=Uniform.station z
 refine ⟨z,hZ,?_⟩; intro k u s hs he hB hu m v' f'
 obtain ⟨hc,hv⟩:= Hx S T F H h s hs he (hB.trans (min_le_left ..)) l le_rfl
 let f:=costP F k T.high T.up; let f₁:=clipped T x F k
 have hM:=mul_comm s (3*A); have hw: 3*A*s < q:=(hM.symm.trans_le ((le_div_iff₀ (show 0<3*A by positivity)).1 (hB.trans ((min_le_right ..).trans (min_le_right ..))))).trans_lt (half_lt_self hq)
 have hb':= hw.trans_le (min_le_left ..); have hfR:= hw.trans_le (min_le_right ..)
 have huS:s ≤ 3*A*s:=by nlinarith only [mul_le_mul_of_nonneg_right hA hs.le,hs.le]
 have e':= ((huS.trans hb'.le).trans (min_le_right ..)); have E(y:Mast G c) (hy:‖y‖<1):= (hc.root k y hy).mono (mul_le_mul_of_nonneg_right (le_max_right D C) hs.le)
 have Hc y (hy:‖y‖<1) : Allows (n+1) m y (A*s)  ∧ Allows (n+1) v' y (A*s)  ∧ Slope f (meetVar (s•y) (v' y))=0:=by
    have he :‖s•y‖ ≤ a:=by rw [norm_smul_of_nonneg hs.le]; exact ((mul_le_of_le_one_right hs.le hy.le).trans huS).trans hfR.le
    have hv:=near_s (f:=z') hs.le e' (show 1 ≤ n+1 by omega) (huS.trans_lt hfR) (fun y hy=> (hL y hy.le).2.1) hy.le
    simp_rw [show z' 0=0 from by simp [z',Uniform.station,hZ.critical.1],sub_zero] at hv
    exact ⟨E y hy,hv.mono (mul_le_mul_of_nonneg_right (le_max_left D C) hs.le),(hL _ he).2.2.1 k⟩ -- tune
 have hb y (hy:‖y‖<R):= (hP S T x H).2.2.2 F k |>.2 y (hy.trans_le (min_le_left ..)) -- Forest meta
 have hp w (hy:‖w‖<R):=HX S T H F k w (hy.trans_le (min_le_right ..)); let Q:= address F G
 have heP w (hw':‖w‖<R): ContDiffAt ℝ ω f₁ w:=by
    rw [←sub_sub_cancel f f₁]; exact (hb w hw').he.sub (hp w hw').he
 have hxM(w:Mast G c→ Fish (Key F G))(hD:Allows (n+1) w u (A*s)):Allows (n+1) (fun x' =>meetVar (s•x') (w x')) u (3*A*s):=(turn_safe hD hD hs.le hA hu 0 (Set.left_mem_Icc.mpr zero_le_one)).germ (Eventually.of_forall fun i=>by simp)
 have h₁:=hxM m (E u hu); have h₂:=hxM v' (Hc _ hu).2.1
 refine ⟨((heP _ (h₁.value.trans_lt hb')).of_le le_top|>.comp u h₁.smooth).sub (((hb _ (h₂.value.trans_lt hb')).1.of_le le_top).comp u h₂.smooth),fun i=>?_⟩ -- tune
 have hi y(hy:‖y‖<R) : DifferentiableAt ℝ f y∧ DifferentiableAt ℝ f₁ y∧∀ i, Allows (n+1) (glance f i) y Y ∧ Allows n (glance (f₁-f) i) y (s^(l+2)*Z):=by
    refine ⟨(hb y hy).he.differentiableAt (by simp),(heP _ hy).differentiableAt (by simp),fun i=>?_⟩
    have he:(hp y hy)=(hp y hy):=rfl
    let hZ:= ((hp y hy).mono (pow_le_pow_left₀ (Work.E04.temp_nonneg x) (show temp x ≤ s from by assumption) (l+2))); have hL:= (hb y hy)
    refine ⟨bolt_g hL.he (Uniform.town F) (fun j hj=> hL.hv j (hj.trans (by omega))) hd (show 0≤b by linarith only [show 0<b from by assumption]) _,?_⟩
    have hp':= (bolt_g (n:=n) hZ.he (Uniform.town F) hZ.hv hx (pow_nonneg hs.le _) i).smul (-1); simp only [abs_neg,abs_one,one_mul,neg_one_smul] at hp'
    apply hp'.germ; filter_upwards [Metric.isOpen_ball.mem_nhds (mem_ball_zero_iff.mpr hy)] with w (hw:w∈ball _ _)
    unfold glance arrow; have he: DifferentiableAt ℝ (f-f₁) w:= (hp w (mem_ball_zero_iff.mp hw)).he.differentiableAt (by simp)
    change -(fderiv ℝ (f-f₁) w (bolt i))=_; rw [← neg_sub f f₁,fderiv_neg]; rfl
 let L:= coverX T x F l i
 have hcL : (L.card:ℝ) ≤ raised G P.L ((l+1)*radiusB x):= by rw [← H.got]; exact lit F _ _
 have h:= hg S T H.got H.size H.funds.1; let W:= raised G P.L ((l+1)*radiusB x)
 have hp'' :=valve i L Hc hi hs.le hA hb' (hb'.le.trans (min_le_right ..)) hu (((hJ k s hs he (hB.trans ((min_le_right ..).trans (min_le_left ..)))).due _ hu).order (show n ≤ n+1 by omega)) (fun y hy => glide h k _ _ F m Chi.canonical 1 (fun z hZ=> (hv Chi.canonical 1 1 k z hZ).1) y hy ((Hc _ hy).1.order (show 1 ≤ n+1 by omega)|>.smooth) i)
 apply hp''.mono
 change s*_+_≤ _
 have he : composeCost n (s^(l+2)*Z) 1+2^n*composeCost n Y 1*(t*s^(l+2)) = V*s^(l+2):=by unfold V composeCost; ring
 rw [he]; have ho : 0≤ W:=(Nat.cast_nonneg L.card).trans hcL
 unfold N; calc
    _ ≤ s*(V*s^(l+2))+W*(2^n*(V*s^(l+2))*(A*s)) := by gcongr
    _ = V*(2^n*A*W+1)*s^(l+3) := by ring
    _ ≤ V*((2^n*A+1)*(W+1))*s^(l+3) := by gcongr; nlinarith only [show 0 ≤ (2^n:ℝ)*A by positivity,ho]
    _ = _ := by unfold W; ring
end YM.CF.Hors
