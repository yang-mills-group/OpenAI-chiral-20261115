import YM.CF.Char.Mu
set_option autoImplicit false
noncomputable section
namespace YM.CF.Char
open Function Filter Set Matrix Lattice Wilson RG Precision Pressure Tree Exterior MeasureTheory Metric Newt Jet
 AnalyticBridge.MarginalMultiplier3b1d AnalyticBridge.LocalGaussianLaws AnalyticBridge.SectorAffine
 AnalyticBridge.NonflatCovarianceLocality.Matching
open Push.SectorMeasure Next.Fluctuations Next.SectorChange Next.SectorChange.Wisps Next.SectorChange.Schur PhysicalNext.JointLoad PatchReads
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius InnerProductSpace
variable {P:RG.Patch}{G:Gauge}{c f:Side}{S:StepData c f}{T:Tube G S}{A A':Stores S}{F F':Forest S.ratio}{k k':S.Choices} {V W:Config G c}{x C:ℝ}{r l:ℕ}
 {Y: LinkArray G (Frozen A x F)}{Y':LinkArray G (Frozen A' x F')}{o:Site c}
open Push
open Push.Uniform (Before Primary curve Slope meetVar Positions upperCol lowerCol Joint block meet_derivative station)
variable {n m j:ℕ}{P:Patch}{Pt:Teller G}{q:Chi}{d v B b D r' A₀ ε X M s:ℝ}{Y₀:LinkArray G (Frozen (bareStores S) x F)}
lemma gram_post (K:Teller G)(P:Patch)(p:P.Branches K.bind G)(n:ℕ): ∃ C r:ℝ,0<C ∧0<r ∧∀ᶠ x:ℝ in atTop, ∀{c f:Side}(S:StepData c f)(T:Tube G S), Cert P K S T x→∀ (F:Forest S.ratio)(k:S.Choices)(u:Mast G c), ‖u‖<r → Allows n (fun y=>gabs T x k F (facadeX G y)) u C:=by
 obtain ⟨r,d,v,y,Q,Z,hr,hd,hv,-,-,hz,H⟩:=estimates G P K p n
 let M:= activation G n 0 d*Z; let C:= composeCost n M (Uniform.shade G); refine ⟨max 1 C,min r 1,lt_of_lt_of_le zero_lt_one (le_max_left ..),lt_min hr zero_lt_one,?_⟩
 filter_upwards [H] with x hx c f S T hQ F k u hu
 have h:= hx.2 S T hQ.got hQ.size hQ.funds.1 (bareStores S) F 1 (Heir.noFlags ..).symm k (reader G c (hull G c u)) ((hull_h u).trans (hu.le.trans (min_le_left ..)))
 have hc:Allows n (hull G c) u (Uniform.shade G):= Jet.allows_linear hull_n (((hull G c).le_opNorm _).trans ((mul_le_of_le_one_right (norm_nonneg _) (hu.le.trans (min_le_right ..))).trans hull_n))
 have he:= jump_up (leaveX (G:=G) F x) (visitX (G:=G) F x) (visit_n ..) (leave_n ..) ((polar_cash _ _ h.gramJets hz.le hd).comp hc)
 apply (he.mono (show C ≤  _ from le_max_right ..)).germ; filter_upwards with y; unfold gabs; rw [tableVisit]; unfold profileGram; ext1 v; simp only [ContinuousLinearMap.comp_apply,Function.comp_apply,reader_field]
lemma block_minus{f g:Positions (Joint F G) → ℝ} {u:Positions (Joint F G)}(he:ContDiffAt ℝ ω f u)(h:ContDiffAt ℝ ω (f-g) u): paintO (block (f-g) u)=paintO (block f u)-paintO (block g u):=by
 have hv:ContDiffAt ℝ ω g u:=by rw [← sub_sub_cancel f g]; exact he.sub h
 rw [← map_sub]; apply congrArg; ext i j; simp only [Uniform.block,Uniform.entry,Matrix.of_apply,Matrix.sub_apply,iteratedFDeriv_sub_apply (he.of_le le_top) (hv.of_le le_top),ContinuousMultilinearMap.sub_apply]
lemma famed (K:Teller G)(P:Patch)(p:P.Branches K.bind G)(n j:ℕ)(hN:2  ≤  n)(W:Before G K.top.width K.top.paths K.j K.bind (n+1+1)):
 ∃ C ε:ℝ,0<C∧0<ε∧∀ᶠ x:ℝ in atTop, ∀{c f:Side}(S:StepData c f)(T:Tube G S)(F:Forest S.ratio), Cert P K S T x → sizedP G P K S T F→∀ s,0<s→temp x ≤  s→s ≤ ε→∀ (k:S.Choices)(q:Chi)(d:ℝ)(Y:LinkArray G (Frozen (bareStores S) x F))(u:Mast G c),‖u‖<1 →
 let E(y:Mast G c):=facadeX G (s•y); let H:= bareStores S; let PP:=pageX (G:=G) F x
 Allows n (fun y=>paintO ((headed T x (E y) k H F (orbitP T x (E y) k H F q d Y j)).submatrix PP PP) -gabs T x k F (E y)) u (C*s):=by
 obtain ⟨C,r,hC,hr,h⟩:= gram_post K P p n; obtain ⟨A,ε,hA,hε,h'⟩:=cup n j hN P K p W
 obtain ⟨a,v,M,ha,hv,hM,hQ⟩:= Newt.mat_paid K P _ (show 3 ≤ n+1+1 by omega) W
 obtain ⟨hd,hG⟩:=tip_left (n+1+1) 1 P K
 let D:= peak (n+1+1) P K; let U:=Uniform.townCost G; let J:=M*(1+U*Uniform.countCost v)^(n+1); let X:=(1+U*Uniform.countCost D)^(n+1); have hB:0<A:=zero_lt_one.trans_le hA
 let B:=min a 1; have hB':0<B:=lt_min ha zero_lt_one
 let W₀:= Jet.composeCost n (J*(3*A)) 1+C+(1+ Jet.composeCost n X 1)
 refine ⟨max 1 W₀,min (min (B/2/(3*A)) (min r 1/2)) ε,lt_of_lt_of_le zero_lt_one (le_max_left ..), lt_min (lt_min (by positivity) (half_pos (lt_min hr zero_lt_one))) hε,?_⟩
 let N:= ozPay P K.bind K.top.width K.top.paths G
 filter_upwards [h,h',hG, smallF (n:=1) (show 0<K.top.width/4 from div_pos K.top.width_pos (by norm_num)) N] with x h he H he' c f S T F Q hc s hs hT hε' k q d Y u hu E S' PP
 have ht := Q.funds.1; obtain ⟨D',M',hP,hR⟩:=ht.feeds; rw [←ht.high] at hP
 let f:=costP F k T.high T.up; let g:=clipped T x F k
 have hH(u:Positions (Joint F G))(hp:‖u‖<B): Wax f u (n+1+1) v M:= ((hQ S T x Q).2.2.2 F k).2 _ (hp.trans_le (min_le_left ..))
 have hx(u:Positions (Joint F G))(hp:‖u‖<B): Wax (f-g) u (n+1+1) D s:= (H S T Q F k _ (hp.trans_le (min_le_right ..))).mono ((pow_one _).trans_le hT)
 have he'': ‖paintO (block f 0)-gabs T x k F 1‖  ≤  s:=by
    apply (octo F x k hP Q.pace Q.funds K.top.paths_pos.le).trans; rw [Q.got,ht.knobs]; exact he'.trans ((pow_one _).trans_le hT)
 have hK:=hε'.trans ((min_le_left ..).trans (min_le_right ..)); have hU:s< min r 1:=hK.trans_lt (half_lt_self (lt_min hr zero_lt_one))
 let z(y:Mast G c):= meetVar (s•y) (Newt.sol S T k x F j (s•y))
 have hh:=he S T F Q hc s hs hT (hε'.trans (min_le_right ..)) j le_rfl
 have hv':3*A*s < B:=lt_of_le_of_lt ((mul_comm ..).trans_le ((le_div_iff₀ (show 0<3*A by positivity)).1 (hε'.trans ((min_le_left ..).trans (min_le_left ..))))) (half_lt_self hB')
 have hL : 3*A*s ≤ 1:=hv'.le.trans (min_le_right ..)
 have hr' (y:Mast G c)(hy:‖y‖<1):Allows n z y (3*A*s):=by
    refine (turn_safe (z:=fun y=>Newt.sol S T k x F j (s•y)) (m:=fun y=>Newt.sol S T k x F j (s•y)) (hh.1.root k y hy) (hh.1.root k y hy) hs.le hA hy 0 ⟨le_rfl,zero_le_one⟩).germ (Eventually.of_forall fun y=> ?_); unfold z; simp
 let q₀:= z u; have h₀:=hx (z u) ((hr' u hu).value.trans_lt hv')
 have hg:= near_s (f:=fun y=> gabs T x k F (facadeX G y)) hs.le (hU.le.trans (min_le_right ..)) (show 1 ≤ n by omega) (hU.trans_le (min_le_left ..)) (h S T Q F k) hu.le
 have hm:=point_ne (s:=s) (M:=3*A) (C:=J) (f:=fun y=>paintO (block f y)) (hr' u hu) (fun y hy=> stiffness (hH y hy).hv (hH y hy).he (Uniform.town F) hM.le hv) (show 1 ≤ n by omega) hs (by positivity) hL hv'; have hh': Allows n (fun y=>paintO (block (f-g) (z y))) u (Jet.composeCost n (s*X) 1):= (stiffness h₀.hv h₀.he (Uniform.town F) hs.le hd).comp ((hr' u hu).mono hL)
 have hV:= subtract_p ((subtract_p hm hg).add (allows_const u he'')) hh'
 apply (hV.mono ?_).germ
 · filter_upwards [isOpen_ball.mem_nhds (mem_ball_zero_iff.mpr hu)] with y (hy:y∈ball (0:Mast G c) 1)
   have hp:=mem_ball_zero_iff.mp hy; have ht' := ((hr' y hp).value.trans_lt hv')
   change paintO _-paintO _-(_-_)+(_-_)-paintO _=paintO _-_
   rw [block_minus (hH _ ht').1 (hx _ ht').1, (hh.2 q d Y k y hp).2,show facadeX G (0:Mast G c)=1 from by simp [facadeX]]; change _-(_-gabs T x k F 1)+ (paintO _-_) - (paintO (block f (z y))-paintO (block g (z y))) = paintO (block g (z y))- _ -- tune
   unfold E; abel
 apply le_trans ?_ (mul_le_mul_of_nonneg_right (le_max_right 1 W₀) hs.le); unfold W₀ Jet.composeCost; exact le_of_eq (by ring)
end YM.CF.Char
