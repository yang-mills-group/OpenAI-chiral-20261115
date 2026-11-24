import YM.CF.Newt.Dawn
set_option autoImplicit false
noncomputable section
namespace YM.CF.Newt
open Function Filter Set Matrix Lattice Wilson RG Precision Pressure Tree Exterior MeasureTheory Metric
 AnalyticBridge.RelativeLogdet.Ink PhysicalNext.JointLoad.Heir Jet Push AnalyticBridge.LocalGaussianLaws AnalyticBridge.SectorAffine
open Push.Uniform (Before Primary curve Slope meetVar Positions upperCol lowerCol block meet_derivative entry)
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius InnerProductSpace
variable {C D v K d N X U s r a e:ℝ}{n l:ℕ}
open Next.SectorChange (panels shots)
open Next.SectorChange.Rows (gram)
variable {G:Gauge}{P:Patch}{c f:Side}{T:StepData c f}{R:Tube G T}{T':Teller G}
def jewel(T:RG.StepData c f)(U:Tube G T)(F:Forest T.ratio)(z: fieldDir G c 1→AxisChart G F)(p :Uniform.ChartPrices)(n m:ℕ)(t d a:ℝ): Prop:= ∀ x:Mast G c, ‖x‖ ≤ t→
 ContDiffAt ℝ ω (Uniform.station z) x ∧ Allows m (Uniform.station z) x a ∧
 (∀ k:T.Choices,Slope (costP F k U.high U.up) (curve (Uniform.station z) x)=0)∧ Uniform.Envelope (Uniform.address F G ∘ Sum.inl) (Uniform.address F G ∘ Sum.inr) d m (Uniform.station z) x a
lemma zenith (P:Patch)(K:Teller G)(n m:ℕ)(hk:m<n)(W:Before G K.top.width K.top.paths K.j K.bind n):∃ t a d:ℝ,0<t∧0<a∧0<d∧∀ {c f:Side}(T:StepData c f)(U:Tube G T)(x:ℝ)(F:Forest T.ratio), Cert P K T U x →
 ∃ z, W.Service F U.high U.up z ∧ jewel T U F z (W.tables K.top.clip P) n m t d a:=by
 let p:=W.tables K.top.clip P; let X:=p.zone; let R:=p.horizon; let H:= p.coords; let d:=Uniform.responseRate H n p.value p.width p.gap
 let t:= if 0<R then R/2 else 1; let a':=Uniform.curveCost H p.value p.width p.gap m; let a:= max 1 (max (a'*(1+H*Uniform.countCost d)^m) X)
 refine ⟨t,a,if 0<d then d else 1,by unfold t; split; positivity; exact zero_lt_one,lt_of_lt_of_le zero_lt_one (le_max_left ..),by split; assumption; exact zero_lt_one,?_⟩
 intro c f T U x F h; have ht:= h.funds.1; obtain ⟨A,B,hx,hp⟩:= ht.feeds; rw [← ht.high] at hx
 obtain ⟨z,hz⟩:= W.graph F hx h.pace ht.atStep ht.knobs
 have he: p=W.tables U.high T.patch:=by rw [ht.high, h.got]
 have hR:R>0:=by unfold R; rw [he]; exact hz.x_pos
 let k:=Classical.arbitrary T.Choices; have hr:Uniform.Receipt (Uniform.address F G) p.width n H p.value p.initial p.gap (costP F k U.high U.up):=by unfold H; rw [he]; exact (W.receipt F k hx h.pace ht.atStep ht.knobs).1
 have hd:0<d:=Uniform.rate_pos hr; have hf:1≤a':=Uniform.curveCost_ge hr _
 let q:=1+H*Uniform.countCost d; have hq:1≤q:= le_add_of_nonneg_right (mul_nonneg (Nat.cast_nonneg _) (Uniform.count_pos hd).le); have hp': a'*q^m ≤ a := le_max_of_le_right (le_max_left ..); have hE:a' ≤ a:= (le_mul_of_one_le_right (zero_le_one.trans hf) (one_le_pow₀ hq)).trans hp'; have hF:= (zero_le_one.trans hf).trans hE
 refine ⟨z,hz,?_⟩; rw [if_pos hd]; intro i hi
 have hi' : i∈ball 0 ((W.tables U.high T.patch).horizon) :=by unfold t at hi; rw [if_pos hR] at hi; rw [← he,mem_ball_zero_iff]; exact hi.trans_lt (half_lt_self hR)
 let Z:= Uniform.station z; have hh : ContDiffAt ℝ ω Z i:= hz.series hi'; have hm : ∀ k:T.Choices, Slope (costP F k U.high U.up) (Uniform.curve Z i)=0:=fun k=> (hz.entered hx h.pace ht.atStep ht.knobs hi' k).self_of_nhds
 have hw := hz.coefficient hx h.pace ht.atStep ht.knobs hk hi'; have HW : Uniform.Envelope (Uniform.address F G ∘ Sum.inl) (Uniform.address F G∘ Sum.inr) d m (Uniform.station z) i a':=by
    dsimp only at hw; rw [← he] at hw; exact hw
 refine ⟨hh, Jet.allows_pi hF (fun j=>?_),hm,HW.more_cost hE⟩
 let f(v:Mast G c):=Z v j
 have he : ContDiffAt ℝ m f i:= ((ContinuousLinearMap.proj (R:=ℝ) (φ:=fun _ : Key F G=>ℝ) j).contDiff.contDiffAt.comp _ hh).of_le le_top
 refine ⟨he,fun k hl=>?_⟩
 by_cases h' : k=0; · subst k; rw [norm_iteratedFDeriv_zero]; refine (norm_le_pi_norm ..).trans ?_; have hj:=mem_closedBall_zero_iff.mp (hz.landed hi'); unfold X at *; exact hj.trans (show (W.tables U.high T.patch).zone ≤ a by -- rename
    rw [ht.high,h.got]; unfold a; apply le_max_of_le_right; apply le_max_right)
 change ‖iteratedFDeriv ℝ k f i‖≤ _
 apply (stall (iteratedFDeriv ℝ k f i) ((Uniform.address F G ∘ Sum.inr) j) (Uniform.address F G ∘ Sum.inl) _ (hr.mult.comp Sum.inl_injective) (zero_le_one.trans hf) hd).trans ((mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hq hl) (zero_le_one.trans hf)).trans hp')
 intro v'; change ‖iteratedFDeriv ℝ k ((ContinuousLinearMap.proj (R:=ℝ) (φ:=fun _ : Key F G=>ℝ) j) ∘ Z) i _‖≤ _; rw [ContinuousLinearMap.iteratedFDeriv_comp_left _ hh le_top]; exact HW k h' hl v' j

end YM.CF.Newt
