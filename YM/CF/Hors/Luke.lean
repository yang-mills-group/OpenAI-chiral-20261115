import YM.CF.Hors.Lens
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
open Push.Uniform (weaker signedFine entryWidth Beacon)
variable {p q:Clip}{R:PathData G}{r':Ratio c f}{B': Forest r'}
def cubeF(c:Side):Ratio c c:= ⟨1,by simp⟩
lemma cube_here {c: Side}(x:Site c): (cubeF c).embed x=x:=by
 nth_rw 1 [← wrap_lift x]; rw [Ratio.embed_wrap, show (cubeF c).count.val=1 from rfl, one_nsmul,wrap_lift]
lemma tia (hc:2 ≤ c.val)(B:Forest (cubeF c))(x:Mast G c)(s:Signed): signedFine B (upperCol x) s=pull s 0 (represent (tint G _ x)):=by
 have hz(y:Config G c):replica (cubeF c) y=y:=by
    have hi(i:Site c): (cubeF c).parent i=i:=by nth_rw 1 [← cube_here i]; exact Ratio.embed_parent ..
    funext i
    haveI: Fact (1 < c.val):=⟨hc⟩; unfold replica; rw [hi,hi]; apply if_neg ?_; intro H; have he:= congrFun (add_left_cancel (a:=i.1) (H.trans (add_zero _).symm)) i.2; simpa using he
 unfold signedFine Uniform.fine Uniform.outer; rw [show (Uniform.paint B G) (upperCol x)=((tint G _) x,0) from rfl]; change pull s 0 (lifting B _ 0)=_; rw [lifted,hz]
lemma label_A {R:ℕ→ Atom G i}(p:SumBudget (fun j=>(R j).budget r) C)(hr:0<r)(h:Uniform.PaintSupply G n D)(x:Positions (Uniform.Joint B' G))(hx:‖x‖<1)(s:Signed):
 let d:=entryWidth n r'.count r
 let K:=(fun y=>uncut R (signedFine B' y s))
 ContDiffAt ℝ ω K x ∧Uniform.Scatter (address B' G) (weaker n d) n K x (C*fareX G i n D r r'.count):=by
 intro d K; have hy:= mem_ball_zero_iff.mpr hx
 have he(i):= Uniform.atom_beacon B' s hr p h x hy i; have hh(i):=Uniform.label_analytic B' R hr p s h i x hy -- tune
 have hp : Injective (affine (R:=Per f) s 0) := fun i j h=>by unfold affine at h; simpa using congrArg s⁻¹.act (add_right_cancel h)
 have hq := Uniform.width_positive hr n r'.count; have ht:0 ≤ C:= (tsum_nonneg p.1).trans p.2.2; have hv:=Uniform.scatter (Uniform.Multiplicity.injective hp) hh he hq (mul_nonneg ht (Uniform.atomCost_nn h hr i))
 refine ⟨ContDiffAt.sum (s:=Finset.univ) fun i _=>hh i,hv.mono ?_⟩; exact le_of_eq (by unfold fareX; ring)
lemma priceCut {R:ℕ→Atom G i}(p:SumBudget (fun j=>(R j).budget r) C)(hr:0<r)(h:Uniform.PaintSupply G (n+1) D)(hc:2 ≤ c.val)(x:Mast G c)(hx:‖x‖<1)(s:Signed)(t:Primary c G):
 let d:=weaker (n+1) (entryWidth (n+1) 1 r)
 let K:=(fun x:Mast G c=>uncut R (pull s 0 (facadeX G x)))
 ContDiffAt ℝ ω K x ∧ Allows n (glance K t) x (composeCost n (C*fareX G i (n+1) D r 1 * (1+Uniform.townCost G*Uniform.countCost d)^n) 1):=by
 intro d K; let L:=cubeF c; let F:= (Tree.select L (show Odd L.count.val from ⟨0,rfl⟩)).some; let U:Mast G c →L[ℝ] Positions (Uniform.Joint F G):=upperCol
 let H(y):=uncut R (signedFine F y s); have hU(y: Mast G c):‖U y‖=‖y‖:=by change ‖meetVar y (0:Positions _)‖= _; simp [Uniform.norm_meet,norm_nonneg]
 have hK:K=H ∘ U:=funext fun y=>congr_arg (uncut R) (tia hc F y s).symm
 have hu:‖U x‖<1:=(hU x).trans_lt hx; obtain ⟨ha,hY⟩:=label_A p hr h (U x) hu s; rw [hK]
 have hf : ‖U‖ ≤ 1:=by apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one; intro y; rw [hU,one_mul]
 have hhx := Uniform.width_positive hr (n+1) 1; have ht:0<d:=by unfold d Uniform.weaker; positivity
 let W:= glance H (Sum.inl t : Uniform.Joint F G); have hg:0≤Uniform.countCost (entryWidth (n+1) (L.count) r/2):=(Uniform.count_pos (half_pos hhx)).le
 refine ⟨ha.comp x U.contDiff.contDiffAt,(Allows.comp (f:=U) (show Allows n W (U x) _ from bolt_g ha (Uniform.town F) hY ht (mul_nonneg ((tsum_nonneg p.1).trans p.2.2) (mul_nonneg (Uniform.atomCost_nn h hr i) hg)) (Sum.inl t)) (allows_linear hf hu.le)).germ ?_⟩
 filter_upwards [isOpen_ball.mem_nhds (mem_ball_zero_iff.mpr hx)] with y (hy:y∈ball _ _)
 unfold W glance arrow; rw [fderiv_comp _ ((label_A p hr h (U y) ((hU y).trans_lt (mem_ball_zero_iff.mp hy)) s).1.differentiableAt (by simp)) U.differentiableAt,U.fderiv]; simp only [ContinuousLinearMap.comp_apply,U,Uniform.upper_bolt]; rfl
end YM.CF.Hors
