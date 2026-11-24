import YM.CF.Vol.Hues
import YM.Push.FINITE_DETECTION.NoLinear
set_option autoImplicit false
noncomputable section
namespace YM.CF.Vol
open Function Filter Set Matrix Lattice Wilson RG Precision Pressure Tree Exterior MeasureTheory Metric
 AnalyticBridge.MarginalMultiplier3b1d AnalyticBridge.LocalGaussianLaws AnalyticBridge.SectorAffine Char Newt
open Push.SectorMeasure AnalyticBridge.RelativeLogdet.Ink
open Push Push.Uniform Hors Finset Laurent Bloch
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius InnerProductSpace
variable {P:RG.Patch}{G:Gauge}{c f:Side}{S:StepData c f}{T:Tube G S}{K:Teller G}{F:Forest S.ratio}{X E B:Type}[NormedAddCommGroup E][NormedSpace ℝ E][NormedAddCommGroup B][NormedSpace ℝ B]{t x s D A C Q V r:ℝ}{i n l:ℕ}
open Tube Next.Fluctuations Work.F03
open Next.SectorChange AnalyticBridge.GaussianFieldAlignment Orthogonal Tensor PhysicalNext.OrderedAffine2B.SymRows Gauges
lemma shyX (p:G.Simple)(h:K.Funds S T)(F:Forest S.ratio)(k:S.Choices)(q:Chi)(r:ℝ)(l:ℕ): orbitP T x (1:Config G c) k (bareStores S) F q r 1 l = 0:=by
 let Y:=bareStores S; let V:= orbitP T x (1:Config G c) k Y F q r 1 l
 have hp:∀ i:Active Y x F,tape V i=0:=by
    intro i; apply FiniteDetection.Low.center_trivial p (tape V i); intro g
    let k' (_: Site c):=g; have he:Lattice.gauge k' (1:Config G c)=1:=by ext1 i; simp [Lattice.gauge,k']
    have hG: gaugeY k' x Y F (1:LinkArray G _)=1:= funext fun i=> False.elim ((notChilled _ _ _ i.val) i.property)
    obtain ⟨A,B,H,H'⟩:=h.feeds; rw [← h.high] at H
    have H0: S.patch.Branches S.kernel G:=by rw [h.knobs]; exact h.kernel
    have hh: V=Orthogonal.move (onBond (rotating (constantGauge k' S.ratio))) (Equiv.refl _) V:=by
        have hh:= (gaugeH T Y F x 1 k q r 1 k' H H0).orbitM H H0 l; rw [he,hG] at hh; exact hh
    have hz:= congrArg (fun x=> tape x i) hh.symm; change tape (Orthogonal.move (onBond _) _ V) i=tape V i at hz
    rw [move_tape] at hz; exact hz
 funext i; change tape V i.1 i.2 = _; rw [hp]; rfl
-- Through n, launch comparator plus O(t^l)
lemma lift_paid (p:G.Simple)(K:Teller G)(P:Patch)(hp:P.Branches K.bind G)(n l:ℕ)(hn:2 ≤ n)(W:Uniform.Before G K.top.width K.top.paths K.j K.bind (n+2)):
 ∃ C V b:ℝ, 0<C∧0<V∧0<b ∧∀ᶠ x:ℝ in atTop,∀{c f:Side}(S:StepData c f)(T:Tube G S)(F:Forest S.ratio),Cert P K S T x → sizedP G P K S T F → ∃ z,W.Service F T.high T.up z ∧ Guessed F (installed S.ratio T.R.A0) z ∧∀ (k:S.Choices),
 let v:=sol S T k x F l; ∀ u:Mast G c, ‖u‖ < b → Jet.Allows n v u C ∧ v 0=0 ∧ ‖fderiv ℝ v 0 - fderiv ℝ (station z) 0‖ ≤ V*temp x^(l+1):=by
 obtain ⟨a,t,G',U,v,ha,ht,hG,hu,hv,hT⟩:=yields K n l hn P hp W; obtain ⟨D,v',hd,hv',hP⟩:=cup n l hn P K hp W; have hD:0<D:=zero_lt_one.trans_le hd; let b:= min v v'; have hb:0<b:=lt_min hv hv'; let Y:= Jet.composeCost n (D*b) (1+b⁻¹)
 refine ⟨Y,t,b,by unfold Y Jet.composeCost; positivity,ht,hb,?_⟩
 filter_upwards [hT,hP,(show Tendsto temp atTop (𝓝 0) by simpa using Work.E09.radiusB_temp 0).eventually (ge_mem_nhds hb), eventually_gt_atTop (0:ℝ)] with x hx hZ hL ht'
 intro c f S T F h hk; obtain ⟨z,hz,hJ,hw,hr⟩:=hx _ _ F h hk
 refine ⟨z,hz,hw,?_⟩
 intro k v u hu; let B:= ContinuousLinearMap.id ℝ (Mast G c); let T':= b⁻¹ • B
 obtain ⟨hD',H⟩:=hZ S T F h hk b hb hL (min_le_right ..) l le_rfl
 have hu y (hy:‖y‖<b): Jet.Allows n v y Y:=by
    have hh:‖T' y‖<1:=by change ‖b⁻¹ • y‖< _; rw [norm_smul_of_nonneg (inv_pos.mpr hb).le, inv_mul_lt_iff₀ hb,mul_one]; exact hy
    have hp:0≤ b⁻¹:=by positivity
    have hr:Jet.Allows n T' y (1+b⁻¹):=Jet.allows_linear ((pole0 _ (Mast G c) (Mast G c) hp).trans (le_add_of_nonneg_left zero_le_one)) (hh.le.trans (le_add_of_nonneg_right hp))
    exact ((hD'.root k _ hh).comp (f:=T') hr).germ (Eventually.of_forall fun y=>by change v (b • (b⁻¹ • y))=v y; rw [smul_inv_smul₀ hb.ne'])
 have h0: v 0=0:=by
    let q:= Chi.canonical; have hy:‖(0:Mast G c)‖<1:=by simp
    have hX:= (H q 1 1 k 0 hy).1; rw [smul_zero, show facadeX G (0:Mast G c)=1 from by simp [facadeX], shyX p h.funds.1 _ _ _ _ _] at hX -- tune
    rw [← visit_left (F:=F) (x:=x) (v 0), ← hX,map_zero]
 refine ⟨hu _ (by assumption),h0,?_⟩
 let H(y):=v y-station z y; let S':=temp x • B; have hs:0<temp x:= Work.E09.temp_pos ht'
 have he: DifferentiableAt ℝ v 0:=(hu 0 (by simpa using hb)).smooth.differentiableAt (by exact_mod_cast (by omega : n≠0))
 have hS:DifferentiableAt ℝ (station z) 0:= (hJ 0 (by simpa using ha.le)).1.differentiableAt (by simp)
 have hK:fderiv ℝ (H ∘ S') 0=(temp x) • (fderiv ℝ v 0-fderiv ℝ (station z) 0):=by
    rw [fderiv_comp _ (show DifferentiableAt ℝ H (S' 0) by rw [map_zero]; exact he.sub hS) S'.differentiableAt,map_zero,S'.fderiv, show H=v-station z from rfl, fderiv_sub he hS]; ext t; simp [S',B]
 have hx : Jet.Allows n (H∘S') 0 (t*temp x^(l+2)):= (hr k _ hs le_rfl (hL.trans (min_le_left ..))).due 0 (by simp)
 have hp:= hx.norm_le 1 (by omega); rw [norm_iteratedFDeriv_one,hK,norm_smul,Real.norm_of_nonneg hs.le] at hp; exact le_of_mul_le_mul_left (hp.trans_eq (show t*temp x^(l+2)= temp x * (t*temp x^(l+1)) by ring)) hs
end YM.CF.Vol
