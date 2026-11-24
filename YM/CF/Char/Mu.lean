import YM.CF.Char.Melon
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
lemma Service.same (W:Before G Pt.top.width Pt.top.paths Pt.j Pt.bind n) (k:S.Choices) {z z':fieldDir G c 1→AxisChart G F} (h:W.Service F T.high T.up z)(hp:W.Service F T.high T.up z')(u:Mast G c)(hx: u∈ ball 0 (W.tables T.high S.patch).horizon): station z u=station z' u:=by
 let K:= W.tables T.high S.patch; have he := h.choice k hx; have hc : (Uniform.tint G _).symm (Uniform.tint G _ u) ∈ ball 0 K.horizon:= by rw [ContinuousLinearEquiv.symm_apply_apply]; exact hx
 have ht := ((hp.2.2.2.2.2.2 _ hc).2.2 k _ (h.landed hx)).1 he; unfold station; exact congr_arg _ ht
lemma tender (n i:ℕ) (hn:2 ≤ n)(P:Patch)(K:Teller G)(p:P.Branches K.bind G)(W:Before G K.top.width K.top.paths K.j K.bind (n+1+1)) :
 ∃ A ε:ℝ,0<A∧0<ε ∧∀ᶠ x:ℝ in atTop, ∀{c f:Side}(S:StepData c f)(T:Tube G S)(F:Forest S.ratio), Cert P K S T x → sizedP G P K S T F→ ∀ s,0<s→temp x ≤  s→s ≤ ε→∀(k:S.Choices)(q:Chi)(d:ℝ)(Y:LinkArray G (Frozen (bareStores S) x F))(u:Mast G c), ‖u‖<1 →
 Jet.Allows n (fun y=> orbitP T x (facadeX G (s•y)) k (bareStores S) F q d Y i-Offset.mean T x k (bareStores S) F q d Y (facadeX G (s•y))) u (A*s^2):=by
 obtain ⟨a,t,v,C,r,ha,ht,hv,hC,hR,h⟩:=yields K n i hn P p W; obtain ⟨a',t',v',C',r',ha',ht',hv',hC',hR',h'⟩:=yields K n 0 hn P p W; obtain ⟨X,e,hX,he,H⟩:=cup n i hn P K p W
 let Z:= (W.tables K.top.clip P).horizon; let m:= if 0<Z then Z else 1; have hm:0< m:=by unfold m; split; assumption; exact zero_lt_one
 refine ⟨t+t', min (min (min (min r r') e) 1) m,add_pos ht ht',lt_min (lt_min (lt_min (lt_min hR hR') he) zero_lt_one) hm,?_⟩
 filter_upwards [h,h',H] with x hx he HH c f S T F Q g s hs hT hY k q d Y u hu
 obtain ⟨z,hz,hJ,hq,h₁⟩:=hx _ _ F Q g; obtain ⟨z',hz',hJ',hq',h₂⟩:=he _ _ F Q g
 have hU:=hY.trans ((min_le_left ..).trans (min_le_left ..)); have hW:=hU.trans (min_le_left ..); have hH:=hY.trans ((min_le_left ..).trans (min_le_right ..))
 have H:=h₁ k s hs hT (hW.trans (min_le_left ..)); have H':=h₂ k s hs hT (hW.trans (min_le_right ..))
 have hM:Z=(W.tables T.high S.patch).horizon:= by rw [Q.got, Q.funds.1.high]
 have hr: m=(W.tables T.high S.patch).horizon:=by unfold m; rw [hM,if_pos hz.x_pos]
 have ht(v:Mast G c)(hv:‖v‖<1): station z (s•v)=station z' (s•v):=by
    apply Service.same W k hz hz'; rw [← hr,mem_ball_zero_iff,norm_smul,Real.norm_eq_abs,abs_of_pos hs]; exact (mul_lt_of_lt_one_right hs hv).trans_le (hY.trans (min_le_right ..))
 have hπ:=H.due u hu; have hπ':=H'.due u hu
 have hp:= ( subtract_p (hπ.mono (mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one hs.le hH (show 2 ≤ i+2 by omega)) (show 0 ≤ t from (show 0<t by assumption).le))) hπ').linear (leaveX (G:=G) F x) (leave_n (G:=G) F x)
 apply (hp.mono (_root_.le_of_eq ?_)).germ
 · filter_upwards [isOpen_ball.mem_nhds (mem_ball_zero_iff.mpr hu)] with y hy
   have hw : ‖y‖ < 1:= mem_ball_zero_iff.mp hy
   have Hh (j:ℕ) (he: j  ≤  i):= (((HH S T F Q g s hs hT (hU.trans (min_le_right ..)) j he).2 q d Y k y hw))
   obtain ⟨hrr,-⟩:= Hh 0 (Nat.zero_le _); obtain ⟨hrr',-⟩:= Hh i le_rfl
   change leaveX F x (_-_)= _; rw [hrr', show Offset.mean T x k (bareStores S) F q d Y (facadeX G (s•y))=_ from hrr,ht y hw]; simp
 · rw [one_mul, add_mul]
end YM.CF.Char
