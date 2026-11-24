import GaugeFieldConstruction.Zeno
import GaugeFieldConstruction.Levana
import GaugeFieldConstruction.FramesWick
set_option autoImplicit false
noncomputable section
namespace YM.StressFHeat
open Function Filter Metric MeasureTheory Real BigOperators
open GaussianFourier Maxwell Analysis
open scoped RealInnerProductSpace Topology ContDiff
local notation "I"=> Complex.I
open HopeC Finset CF.Crest CF.Vale.Veins
-- cloud of ribbons
local notation "τ"=> (2:ℝ)⁻¹
def wireU : HopeC ℝ where
 μ:= volume.restrict (Set.Ioc (-τ) τ)
 isProb:= ⟨by rw [Measure.restrict_apply_univ]; rw [Real.volume_Ioc]; norm_num⟩
 site:=Set.Icc (-τ) τ
 k:=isCompact_Icc
 onA:=(ae_restrict_mem measurableSet_Ioc).mono fun _ h=>Set.Ioc_subset_Icc_self h
abbrev Rodς (a:Axis) := lift wireU (fun t:ℝ=> t • basis a) (by fun_prop)
lemma RodBill (a:Axis)(p:E4): ξH (Rodς a) p= skirt (p a):=by unfold Rodς ξH; rw [rolled (v:=(show Continuous (fun x=> rider x p) from by unfold rider; fun_prop).continuousOn)]; unfold rider; simp_rw [real_inner_smul_left,basis_inner]; simpa only [wireU, surge, one_div] using skirt_area (p a)
abbrev Larch (a: Axis):=addQ (point (τ • basis a)) (Rodς a)
lemma Larch_W (a:Axis)(p:E4): ξH (Larch a) p= glowτ (p a):=by rw [adds,xi_point,RodBill]; unfold rider glowτ; rw [real_inner_smul_left,basis_inner]; push_cast; ring_nf
abbrev Foliants (a:Lattice.PlaqAxes): HopeC E4:=addQ (Larch a.val.1) (Larch a.val.2)
abbrev CubeW :HopeC E4:= addQ (addQ (Rodς 0) (Rodς 1)) (addQ (Rodς 2) (Rodς 3))
abbrev SpecW : HopeC E4:= addQ (addQ CubeW CubeW) (addQ CubeW CubeW)
lemma specie (p:E4): ξH SpecW p=(CF.Crest.Shore.weave p.ofLp)^4:=by
 have he: ξH CubeW p= CF.Crest.Shore.weave p.ofLp:=by unfold CubeW CF.Crest.Shore.weave; simp_rw [adds,RodBill]; rw [Fin.prod_univ_four]; ring -- tune
 unfold SpecW; rw [adds, adds,he]; ring
abbrev off (x: Lattice.Cover):E4:= WithLp.toLp 2 (fun i:Axis=> (x i:ℝ))
lemma off_r(p:E4)(x:Lattice.Cover) : rider (off x) p=Laurent.mode (CF.Fir.tmap p.ofLp) x:=by unfold rider Laurent.mode; rw [PiLp.inner_apply,Complex.ofReal_sum]; congr 2; exact sum_congr rfl (fun i _=>by simp [CF.Fir.tmap,off,RCLike.inner_apply])
lemma shaft (x:ℝ): Next.Free.chip (x:ℂ)=I*x*glowτ x:=by
 let g:= Complex.exp (I*x/2); let w:= surge (-(1/2:ℝ)) x; have he : surge (1/2:ℝ) x=g:=by unfold surge g; push_cast; ring_nf
 have hv:g*w=1:=by unfold g w surge; rw [← Complex.exp_add]; push_cast; ring_nf; simp
 have hk:= step_sinc x
 change -(I*x)*skirt x= -(surge (1/2) x-w) at hk; rw [he,neg_mul,neg_inj] at hk; unfold Next.Free.chip
 rw [show Complex.exp _=g*g from ?_]; swap; · unfold g; rw [← Complex.exp_add]; ring_nf
 change g*g-1=I*x*(g*skirt x); rw [mul_left_comm, hk, mul_sub, hv]
-- ribbon color numerator per potential direction ν
open Lattice Exterior
abbrev FlatR (a:Cover × PlaqAxes): HopeC E4:= addQ (point (off a.1)) (addQ (Foliants a.2) SpecW)
/-- coefficient at derivative direction a for target F with given chart coordinate v -/
abbrev spikeT (j:PlaqAxes)(v:TypeFace 1)(a:Axis):ℝ:= (if j.val.1=a ∧ coord j.val.2=v then 1 else 0)-(if j.val.2=a ∧ coord j.val.1=v then 1 else 0)
abbrev standU (j:PlaqAxes)(v:TypeFace 1)(p:E4):ℂ:= ∑ a:Axis, (spikeT j v a:ℂ)*dotbill p [a]
lemma stand_v (u:PlaqAxes)(v:TypeFace 1)(p:E4): standU u v p=(if coord u.val.2=v then I*(p u.val.1:ℂ) else 0)-(if coord u.val.1=v then I*(p u.val.2:ℂ) else 0):=by
 unfold standU dotbill spikeT; by_cases h:coord u.val.2=v <;> by_cases u':coord u.val.1=v <;> simp_rw [Complex.ofReal_sub,apply_ite ((↑) : ℝ→ℂ),sub_mul, sum_sub_distrib] <;> simp [h,u',ite_mul,sum_ite_eq]
lemma Bart_r (x:Cover× PlaqAxes)(p:E4)(v:TypeFace 1): Pontiff x p.ofLp v= ξH (FlatR x) p * standU x.2 v p:=by
 let a:=x.2.val.1; let b:=x.2.val.2
 have he:Pontiff x p.ofLp v= (CF.Crest.Shore.weave p.ofLp)^4*glowτ (p (axisEquiv.symm v))*Laurent.mode (CF.Fir.tmap p.ofLp) x.1 * ((if coord b=v then Next.Free.chip (p a) else 0)-(if coord a=v then Next.Free.chip (p b) else 0)):=by unfold Pontiff creditW; simp only; unfold a b; rw [mul_assoc ( (CF.Crest.Shore.weave _ ^4)*_)]; rfl -- tune shape reassoc
 rw [he, stand_v]; unfold FlatR Foliants; rw [adds,adds,adds,specie,Larch_W,Larch_W,xi_point,off_r]; let K(p:E4):= CF.Crest.Shore.weave p.ofLp
 change _= _ * ((if coord b=v then _ else 0)-(if coord a=v then _ else 0))
 have ht:a≠b:= x.2.property.ne
 have hm (i:Axis):axisEquiv.symm (coord i)=i:=axisEquiv.symm_apply_apply i
 have hx:coord a ≠ coord b:=fun p=> ht (axisEquiv.injective p)
 by_cases h1:coord a=v; · subst v; simp only [Ne.symm hx,if_false,if_true,zero_sub,mul_neg,neg_inj,hm]; rw [shaft]; unfold a b at *; ring -- tune
 by_cases h2:coord b=v<;> simp only [h1,h2, ↓reduceIte,sub_zero,mul_zero]; rw [←h2,hm,shaft]; unfold a b; ring -- tune
end YM.StressFHeat
end
