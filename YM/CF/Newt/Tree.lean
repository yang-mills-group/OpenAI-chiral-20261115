import YM.CF.Newt.Cure
set_option autoImplicit false
noncomputable section
namespace YM.CF.Newt
open Function Filter Set Matrix Lattice Wilson RG Precision Pressure Tree Exterior MeasureTheory Metric
 AnalyticBridge.RelativeLogdet.Ink PhysicalNext.JointLoad.Heir Jet Push AnalyticBridge.LocalGaussianLaws AnalyticBridge.SectorAffine
open Push.Uniform (Before Primary curve Slope meetVar Positions upperCol lowerCol block meet_derivative)
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius InnerProductSpace
variable {ι τ: Type} [Fintype ι] [Fintype τ] {C D v K d N X U s r a e:ℝ}{n:ℕ}
open Next.SectorChange (panels shots)
variable {P:RG.Patch}{G:Gauge}{c f:Side}{T:StepData c f}{R:Tube G T}{T':Teller G}
section high
open Next.SectorChange.Rows (gram)
lemma recount (F:Forest T.ratio)(x:ℝ)(k:T.Choices)(h:R.up.Bounds R.high v C D)(p:Bid.Larger (G:=G) T)(Q:Lift.Booth T' T R) :
 (gram R x 1 k (shots T x) (bareStores T) F).submatrix (pageX F x) (pageX F x)=FreeResolvent.Affine.primary T F k R.high R.up (FreeResolvent.Affine.shorter (Stores.till x)) 0 ∧ Push.Uniform.block (costP F k R.high R.up) 0=FreeResolvent.Affine.primary T F k R.high R.up FreeResolvent.Affine.all 0 :=by
 obtain ⟨hl,H,H',A,C',B,D',hh1,hh2,hv,hv',hy,hy',-⟩:= Q
 refine ⟨?_,?_⟩
 · have he := (Assembly.notarized T R x k (bareStores T) F h p.1 .endpoint).self_of_nhds
   have hb := (he.2 (Assembly.bare_is_Clear T x F)).1
   rw [show Assembly.enroll (n:=c) (G:=G) 0=1 from ?_] at hb; exact hb
   apply link_one
 obtain ⟨hP,H'⟩:= Work.F03.answer G _ _ T p F H _ R.up v C D _ _ hh1 h hv hy (Work.F02.answer G _ R.up v C D h)
 let L : Positions (Primary c G):=0; let K : Positions (Key F G):=0
 have he : meetVar L K = 0:= map_zero ((Push.Uniform.partSpace ..).symm)

 rw [← he,Uniform.block_congr F k,show L=(0: Positions _) from rfl,show K=(0:Positions _) from rfl,map_zero,map_zero,FreeResolvent.Tests.checked_loop F H k _ _ hP H']
 · exact (FreeResolvent.Affine.identifies T F k p.1 h hv hh1.roots hy).symm
 rw [he]; let Q:=Uniform.paint F G; have hr : Q 0=0:=map_zero Q
 exact (hr.symm ▸ hP k).comp (f:=Q) _ Q.contDiff.contDiffAt

def gabs (R:Tube G T) (x:ℝ)(k:T.Choices)(F:Forest T.ratio)(V:Config G c):= paintO ( (gram R x V k (shots T x) (bareStores T) F).submatrix (pageX F x) (pageX F x))
def ozPay(P:RG.Patch)(K:KernelChoices)(v C:ℝ)(G:Gauge):=2*FreeResolvent.tagPrice 1 0 (FreeResolvent.Affine.phasePrice G P K 0 C v) (FreeResolvent.Affine.phasePrice G P K 0 C v)
lemma octo(F:Forest T.ratio)(x:ℝ)(k:T.Choices)(h:R.up.Bounds R.high v C D)(p:Bid.Larger (G:=G) T)(Q:Lift.Booth T' T R)(hC:0≤C) :
 ‖paintO (block (costP F k R.high R.up) 0)-gabs R x k F 1‖ ≤ Real.exp (-(v/4)*Stores.till x)*ozPay T.patch T.kernel v C G:=by
 let U:= costP F k R.high R.up; let L:= Stores.till x; let C':=ozPay T.patch T.kernel v C G
 obtain ⟨he,hh⟩:=recount F x k h p Q
 unfold gabs; rw [he,hh,← map_sub]
 have hx:= FreeResolvent.Affine.phase_nn G T.patch T.kernel (k:=0) h.width hC
 have ht := FreeResolvent.Affine.ordering h.width 0
 have hb : 0 ≤ C':= by unfold C' ozPay; apply mul_nonneg (by positivity) (FreeResolvent.Affine.tag_nn hx hx)
 apply mtr_op _ (p:=FreeResolvent.theta T.ratio F) (v:=FreeResolvent.Affine.tier v 0) _ ht.1.le (mul_nonneg (Real.exp_pos _).le hb)
 have hf := AnalyticBridge.RelativeLogdet.Differential.recovered (FreeResolvent.Affine.tail_primary T p.2.2 h.width hC (show FreeResolvent.Affine.Sheet R.up v C from h.rows) ht.1.le le_rfl L F R.high k)
 exact hf
end high
end YM.CF.Newt
