import GaugeFieldConstruction.ItaliaQc
/-!
# Derivative operations by annihilator
-/
set_option autoImplicit false
set_option synthInstance.maxSize 7800
noncomputable section
namespace YM.GaugeFieldConstruction.Ember.Hulse
open Calibration Raw Cauchy LabelAction Empire Fathom Payroll Function Filter Set TopologicalSpace Analysis MeasureTheory Points Bulb Palace Salam
open Floor Sailing
open scoped Topology BigOperators ContDiff Classical
attribute [local instance] iG iF iX iU iT2 iW2 iV iS
local notation "l"=> UV five
variable {n : ℕ} {S:City} (Y:AreaQc S)
lemma aukQc (r:Equiv.Perm (Fin n))(x:Points n)(h:x∈generic n): rearrange r x∈generic n:= fun a=>(h a).comp r.injective
lemma FitPegQc (x:E4)(t:Points (n+1)): riders (rearrange rotor (LensQc x t))=t+ LonelyQc x:=by
 ext1 i; refine Fin.cases ?_ ?_ i
 · rw [show riders (rearrange rotor (LensQc x t)) 0=(LensQc x t) 0 from (hop (LensQc x t))]; simp [LonelyQc, Lens0p,Points.cons]
 intro j; rw [show riders (rearrange rotor (LensQc x t)) j.succ=(LensQc x t) j.succ.succ from (by change (LensQc x t) (rotor j.succ.succ)=_; rw [external']), LensIp]; simp [LonelyQc,Points.cons]
lemma uniteQc (x:E4)(q:HintQc)(B:UV five)(u:guild x): BillQc Y q (Empire.one five) B x= ∫ t:Points (q.n+1), q.f t * Y.fee _ (Fathom.add B q.x) (t+ LonelyQc x):=by
 apply integral_congr_ae; filter_upwards [HeelQc (n:=q.n) x u] with t ht
 change q.f t*Y.fee _ _ (LensQc x t)=_; rw [← Y.rearr _ rotor _ ht,Palace.on_labels, Y.unit _ _ _ (aukQc rotor _ ht), FitPegQc]
lemma GuildSmQc (x:E4)(q:guild x)(t:ℝ)(h:t≠0): guild (t • x):= fun i=>mul_ne_zero h (q i)
lemma LoneSmQc (x:E4)(t:ℝ):LonelyQc (n:=n) (t • x)=t • LonelyQc x:=by ext1 j; refine Fin.cases ?_ ?_ j <;> simp [LonelyQc,Points.cons] -- tune
variable {X:Type*}[AddCommGroup X][Module ℂ X](L : X→ₗ[ℂ] l)(N:NickleQc)(B:l)(w:ℕ→ℝ)
variable (p: BloomQc Y L (Empire.one five) B w N)(R:Tendsto (fun i=> (N.e i)⁻¹*w i) atTop (𝓝 0))
noncomputable def HeightTiltQc (Y:AreaQc S)(q:HintQc)(B:l)(x:E4):ℂ:= - (tilt (LonelyQc x) q.f).applyTo (Y.fee _ (Fathom.add B q.x))
include p R
lemma TiltProofQc {J:Type}(I:Finset J)(c:J→HintQc)(a:J→ℂ)(H:∀ Q:X,∑ j∈I, a j* DriftQc S L Q (c j)=0)(x:E4)(v:guild x)(r:AnnulusQc 1 x)(F:X)(f:L F=B): ∑ j∈I,a j* HeightTiltQc Y (c j) B x=0:=by
 let G (j:J):=Y.fee _ (Fathom.add B (c j).x); let C (j:J):= WindQc (LonelyQc x) (G j) (c j).f; let s (t:ℝ):=∑ j∈I,a j*C j t; let H0(j):= HeightTiltQc Y (c j) B x
 have ht (j): HasDerivAt (fun (t:ℝ)=>a j*C j t) (a j* H0 j) 0:= by
    exact (CostTiltQc (LonelyQc x) (c j).f (G j) (Y.reg ..)).const_mul (a j) -- implicit derivative real? const_mul ℝ vs ℂ, theorem RCLike.Complex tune
 have hd:HasDerivAt s (∑ j∈I,a j*H0 j) 0:= HasDerivAt.fun_sum (fun i _=>ht i)
 have h':Tendsto N.e atTop (𝓝[≠] (0:ℝ)):= tendsto_nhdsWithin_iff.mpr ⟨N.small,Eventually.of_forall fun i=> (N.positive i).ne'⟩
 have He(i):s (N.e i)=∑ j∈I,a j* BillQc Y (c j) (Empire.one five) B ((N.e i) • x):= Finset.sum_congr rfl fun j _=> by
    rw[uniteQc Y _ (c j) B (GuildSmQc x v _ (N.positive i).ne'),LoneSmQc]; rfl
 have hz:s 0=0:=by
    unfold s; rw [← H F]; apply Finset.sum_congr rfl; intro i _; rw[DriftCostQc,Y.price,f]; unfold C G WindQc; simp [Test.applyTo, Fathom.add]
 obtain ⟨Q,_g,h⟩:=p.fee I c a H
 apply tendsto_nhds_unique (hd.tendsto_slope.comp h')
 refine squeeze_zero_norm' ?_ (by simpa only [zero_mul] using R.mul_const Q)
 filter_upwards [h] with i q; change ‖slope s 0 (N.e i)‖ ≤ _
 rw [slope_def_module,sub_zero,He,hz,sub_zero, norm_smul]; have hi:=N.positive i
 rw [Real.norm_eq_abs,abs_of_nonneg (inv_nonneg.mpr hi.le)]
 exact (mul_le_mul_of_nonneg_left (q _ (LevelQc x r _ hi) (GuildSmQc x v _ hi.ne')) (inv_pos.mpr hi).le).trans_eq (by ring) -- tune q
#check HasDerivAt.const_mul
#check HasFDerivAt.clm_apply
#check HasDerivAt.fun_sum
#print axioms TiltProofQc
end YM.GaugeFieldConstruction.Ember.Hulse
