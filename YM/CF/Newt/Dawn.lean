import YM.CF.Newt.Quest
set_option autoImplicit false
noncomputable section
namespace YM.CF.Newt
open Function Filter Set Matrix Lattice Wilson RG Precision Pressure Tree Exterior MeasureTheory Metric
 AnalyticBridge.RelativeLogdet.Ink PhysicalNext.JointLoad.Heir Jet Push AnalyticBridge.LocalGaussianLaws AnalyticBridge.SectorAffine
open Push.Uniform (Before Primary curve Slope meetVar Positions upperCol lowerCol block meet_derivative)
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius InnerProductSpace
variable {C D v K d N X U s r a e:ℝ}{n l:ℕ}
open Next.SectorChange (panels shots)
open Next.SectorChange.Rows (gram)
variable {G:Gauge}{P:Patch}{c f:Side}{T:StepData c f}{R:Tube G T}{T':Teller G}
def budX (R:Tube G T) (x:ℝ)(F:Forest T.ratio)(k:T.Choices)(z:Mast G c): Fish (Key F G):=visitX F x (forecast R x F k (hull G c z))
def herX (R:Tube G T) (x:ℝ)(F:Forest T.ratio)(k:T.Choices): Mast G c →L[ℝ] Fish (Key F G):= (visitX F x).comp ((PhysicalNext.JointLoad.Heir.first R F x).comp (hull G c))
lemma recover (F:Forest T.ratio)(x:ℝ)(k:T.Choices)
 (z:fieldDir G c 1→AxisChart G F)(t:ContDiffAt ℝ ω z 0)(h:@Guessed _ _ T _ F (Bloch.installed T.ratio R.R.A0) z): fderiv ℝ (Uniform.station z) 0= herX R x F k:=by
 let U:= Uniform.tint G (Body 1 c); let X:fieldDir G c 1→ AxisChart G F:=z; let L:= Uniform.tint G F.Free; let g:= herX R x F k
 have he:DifferentiableAt ℝ z (U 0):=by rw [map_zero]; exact t.differentiableAt (by simp)
 ext1 y
 have hh:(fderiv ℝ z (U 0)) (U y) = relative F (Bloch.installed T.ratio R.R.A0) (U y):= by rw [map_zero]; apply HasDerivAt.unique _ (h _); exact Push.side z (by simpa using he) (U y) -- tune
 have hx : Uniform.station z=L.symm ∘ (z ∘ U):=rfl
 rw [hx, fderiv_comp _ L.symm.differentiableAt (he.comp _ U.differentiableAt), ContinuousLinearEquiv.fderiv, fderiv_comp _ he U.differentiableAt, ContinuousLinearEquiv.fderiv]
 change L.symm ((fderiv ℝ z (U 0)) (U y)) = visitX F x ((PhysicalNext.JointLoad.Heir.first ..) (hull G c y))
 rw [hh, PhysicalNext.JointLoad.Heir.first_read,show Next.SectorChange.Flat.labels (hull G c y)=U y from AnalyticBridge.LocalGaussianLaws.Lift.converted (U y)]; ext1 i
 change relative F _ _ i.1 i.2=AnalyticBridge.LocalGaussianLaws.Lift.doc R F _ i.1 i.2
 unfold Lift.doc collect Lift.low Bid.stretch
 simp only [← Exterior.coord_map]
 dsimp only [Pi.sub_apply,PiLp.sub_apply]
 simp only [axisEquiv.symm_apply_apply,Prod.mk.eta]
 rw [dif_neg (show i.1.val∉F.trunks from i.1.property)] -- orientation stretch formula? 
 simp [Lift.blueprint,Next.SectorChange.Flat.labels]
 simp only [← coord_map,axisEquiv.symm_apply_apply,Prod.mk.eta,add_sub_cancel_left]
lemma bub (F: Forest T.ratio)(x:ℝ)(k:T.Choices)(hp:0≤C)(u:Mast G c)(hx:‖u‖≤1)(h:Offset.Through n (forecast R x F k) (hull G c u) C): Allows n (budX R x F k) u (composeCost n C (Uniform.shade G)):=by
 have he:Allows n (hull G c) u (Uniform.shade G) := allows_linear hull_n (((hull G c).le_opNorm _).trans ((mul_le_of_le_one_right (norm_nonneg _) hx).trans hull_n))
 have ht:= (show Allows n (forecast R x F k) (hull G c u) C from ⟨h.1,h.2⟩).comp he
 exact (ht.linear (visitX F x) (visit_n ..)).mono (one_mul _).le
lemma month(K:Teller G)(p:P.Branches K.bind G)(n:ℕ)(hn:1≤n):∃ r C:ℝ,0<r ∧0<C ∧∀ᶠ x in atTop,
 ∀{c f:Side}(T:StepData c f)(R:Tube G T), Cert P K T R x → ∀ (F:Forest T.ratio)(k:T.Choices),
 Portrait (budX R x F k) (herX R x F k) n (temp x) r C:=by
 obtain ⟨r,Y,hr,hY,H⟩:= survey G P K p n
 let D:= Uniform.shade G; let C:=composeCost n Y D; let B:=max C D; have hd :0<D:=Uniform.shade_pos _
 refine ⟨min 1 (r/D), B, lt_min zero_lt_one (by positivity),hd.trans_le (le_max_right ..),?_⟩
 filter_upwards [H,dissent G P K p] with x hx hp
 intro c f T U h0 F k; let T:=hull G c; let V:=visitX F x (G:=G); have ht:= hp _ U h0.got h0.funds h0.size F k
 have hh y (hy:‖y‖≤r) := hx _ U h0.got h0.funds.1 h0.size F k y hy
 have hS:= (hh 0 (by simpa using hr.le)); have hB:DifferentiableAt ℝ (forecast U x F k) (T 0):=by rw [map_zero]; exact (hS.smooth.of_le (m:=1) (by exact_mod_cast hn)).differentiableAt (by simp)
 refine ⟨fun i hi=> ?_,?_,?_⟩
 · have hp : ‖T i‖ ≤ r := (T.le_opNorm i).trans ((mul_le_mul_of_nonneg_right hull_n (norm_nonneg _)).trans ((mul_comm D _).trans_le ((le_div_iff₀ hd).1 (hi.trans (min_le_right ..)))))
   have he: Allows n (budX U x F k) i C:= bub _ _ _ hY.le _ (hi.trans (min_le_left ..)) (hh _ hp); refine ⟨he.smooth,fun j hj=> (he.mono (show C≤B from le_max_left ..)).norm_le j hj⟩
 · unfold budX; obtain ⟨hy,-⟩:=ht; unfold difference at hy; rw [Pi.sub_apply,map_zero,sub_zero] at hy; rw [map_zero,hy,map_zero]
 unfold difference at ht
 let L:=herX U x F k; let P:= PhysicalNext.JointLoad.Heir.first U F x
 have he:(fderiv ℝ (budX U x F k) 0) -L= V.comp ((fderiv ℝ ((forecast U x F k)-⇑P) 0).comp T):=by
    rw [show budX U x F k=V ∘ (forecast U x F k ∘ T) from rfl,fderiv_comp _ V.differentiableAt (hB.comp _ T.differentiableAt), V.fderiv, fderiv_comp _ hB T.differentiableAt,T.fderiv]
    rw [map_zero] at hB ⊢
    rw [fderiv_sub hB P.differentiableAt,P.fderiv]; ext i j; simp only [_root_.sub_apply, ContinuousLinearMap.comp_apply,map_sub,Pi.sub_apply]; rfl
 change ‖_ - L‖≤ B*_ ; rw [he]; apply ((ContinuousLinearMap.opNorm_comp_le ..).trans (mul_le_of_le_one_left (norm_nonneg _) (visit_n ..))).trans
 refine ((ContinuousLinearMap.opNorm_comp_le ..).trans (mul_le_mul ht.2 (hull_n.trans (le_max_right ..)) (norm_nonneg _) (Work.E04.temp_nonneg _))).trans_eq (mul_comm ..)
end YM.CF.Newt
