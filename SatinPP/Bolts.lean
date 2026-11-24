import SatinPP.Grenadier
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 3500
set_option maxHeartbeats 650000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common Ballad Cordial
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
open Germ Alliance Lamour.Bridge.Celeste Designs Twah Prototype
open Lamour.Bridge.Celeste.Morn
namespace Spine
open Aria Casting Six MacroGrid

open Set SatinJets DoseTravel
abbrev sampleBrae : SampleDose:= slider 0 (relative 0 1 (by norm_num))
abbrev pixel' (a:Vantage) (r:ℝ)(h:0<r):= slider a (relative a r h)

abbrev lode:=relative (0:Vantage) 1 (by norm_num)
private lemma pic (a:Vantage) {r:ℝ}(h:0<r)(p:Vantage): relative a r h p= lode (r⁻¹ • (p-a)):=by
 change (someContDiffBumpBase Vantage).toFun (r/(r/2)) ((r/2)⁻¹ • (p-a))=_ 
 change _=(someContDiffBumpBase Vantage).toFun _ (((1:ℝ)/2)⁻¹ • (r⁻¹ • (p-a) - 0))
 rw [sub_zero,smul_smul,show ((r/2)⁻¹) = (1/2:ℝ)⁻¹*r⁻¹ by field_simp]
 change _=(someContDiffBumpBase Vantage).toFun (1/(1/2:ℝ)) _
 rw [show r/(r/2)=1/(1/2:ℝ) by field_simp]
private abbrev m:=Module.finrank ℝ Vantage

private lemma pixelized (a:Vantage){r:ℝ}(h:0<r)(p:Vantage):
    (pixel' a r h).val p = sampleBrae.val (r⁻¹ • (p-a))/r^m:=by
 change relative a r h p / (∫ q, relative a r h q)= lode _/(∫ q,lode q)/r^m
 have A: (∫ q,lode (r⁻¹ • (q-a)))=r^m*(∫ q,lode q):= by
    simp_rw [sub_eq_add_neg]
    rw [integral_add_right_eq_self (fun q=>lode (r⁻¹ • q)) (-a),Measure.integral_comp_smul,smul_eq_mul,inv_pow,inv_inv,abs_of_pos (pow_pos h _)]
 simp_rw [pic a h]
 rw [A,div_eq_mul_inv, mul_inv_rev]

 ring


abbrev nick (v:Vantage)(d:ℝ)(p:Vantage) (f:SampleDose):ℝ:=(f.val p-f.val (p-d • v))/d
private lemma blade_p {s:ℝ}(h:0<s)(p v:Vantage) (f:SampleDose):
 ∃ a∈Set.Ioc (0:ℝ) s, nick v s p f = fderiv ℝ f.val (p-a • v) v:=by
 let g(t:ℝ):=p-t • v
 have t₀(t): HasDerivAt g (-v) t:=by
    simpa using! (hasDerivAt_const t p).sub ((hasDerivAt_id' t).smul_const v)
 have d(t):= (f.smooth.differentiable (by simp) _).hasFDerivAt.comp_hasDerivAt t (t₀ t)
 obtain ⟨a,r,w⟩:=exists_deriv_eq_slope (f.val ∘ g) h (continuousOn_of_forall_continuousAt fun t _=> (d t).continuousAt) (fun t _=> (d t).differentiableAt.differentiableWithinAt)
 refine ⟨a,⟨r.1,r.2.le⟩,neg_inj.mp ?_⟩
 unfold nick
 rw [←neg_div,neg_sub]
 have y:deriv (f.val ∘ g) a=(f.val (g s)-f.val p)/s:= w.trans (by simp [g])
 rw [show p-s • v=g s from rfl,←y,(d a).deriv,map_neg]
def bike (v:Vantage)(f:SampleDose)(t:ℝ) : SampleDose where
 val:=fun p=>nick v t p f
 smooth:= by
    unfold nick
    exact (f.smooth.sub (f.smooth.comp (contDiff_id.sub contDiff_const))).div_const _
 budget:=by

    have y:= f.budget.sub (f.budget.comp_homeomorph (Homeomorph.subRight (t • v)))
    apply y.mono
    intro p z r; apply z; have w:f.val p-f.val (p-t • v)=0:= r
    change nick v t p f=0;unfold nick;rw [w,zero_div]


lemma blade_s (f:SampleDose):
 ∃ K> (0:ℝ),∀ {h t:ℝ}, 0<t→ t ≤ h → ∀ (p v:Vantage), ‖v‖ ≤ 1 → |nick v t p f-nick v h p f| ≤ K*h:=by
 let y:=fderiv ℝ f.val
 have g:=f.smooth.fderiv_right (m:=1) (by decide)
 obtain ⟨k,z⟩:= ContDiff.lipschitzWith_of_hasCompactSupport (f.budget.fderiv ℝ) g (by simp)
 let w:=max (k:ℝ) 1
 have w₀:0<w:=zero_lt_one.trans_le (le_max_right _ _)
 refine ⟨w,w₀,fun {h t} ht u p v hv=>?_⟩
 obtain ⟨a,⟨a₁,a₂⟩,d⟩:=blade_p ht p v f
 obtain ⟨b,⟨b₁,b₂⟩,e⟩:=blade_p (ht.trans_le u) p v f
 rw [d,e,←_root_.sub_apply,←Real.norm_eq_abs]
 apply (ContinuousLinearMap.le_opNorm ..).trans
 apply (mul_le_of_le_one_right (norm_nonneg _) hv).trans
 let p₁:=p-b • v;let p₂:=p-a • v
 have e': ‖y p₂ - y p₁‖≤ w * ‖p₂-p₁‖:= (z.norm_sub_le ..).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _))
 refine e'.trans (mul_le_mul_of_nonneg_left ?_ w₀.le)
 rw [show p₂-p₁=(b-a) • v from by unfold p₂ p₁;rw [sub_smul];abel,norm_smul,Real.norm_eq_abs]
 exact (mul_le_of_le_one_right (abs_nonneg _) hv).trans (abs_le.mpr ⟨by linarith only [u,a₂,b₁],by linarith only [b₂,a₁]⟩)

private lemma nick_scale (a v p:Vantage){r h:ℝ}(e:0<r)(u:0<h):
 nick v h p (pixel' a r e)=
 nick v (h/r) (r⁻¹ • (p-a)) sampleBrae /(r*r^m):= by
 unfold nick
 rw [pixelized _ e, pixelized _ e]
 have t:r⁻¹ • (p-h • v - a)=r⁻¹ • (p-a) - (h/r) • v:=by
    rw [sub_right_comm,smul_sub,smul_smul,div_eq_inv_mul]
 rw [t]
 field_simp
abbrev coverall (a:Vantage) {r:ℝ}(h:0<r):= pixel' a (4*r) (mul_pos (by norm_num) h)
lemma cover_ok (a:Vantage){r:ℝ}(h:0<r):(coverall a h).Normalized:= prescribed _ _
private def BZ:= (sampleBrae.val 0)/ 4^m
private lemma BZ_pos : 0<BZ:= by
 have h:0<(sampleBrae.val 0):= by
    rw [show sampleBrae.val 0=lode 0/(∫ q,lode q) from rfl, lode.one_of_mem_closedBall (mem_closedBall_self lode.rIn_pos.le)]
    exact div_pos zero_lt_one lode.integral_pos
 exact div_pos h (by positivity)


private lemma BZ_charge (a:Vantage){r:ℝ}(h:0<r){p:Vantage}(y: dist p a ≤2*r):
 (coverall a h).val p= BZ/r^m:=by
 let e:0<4*r:=by positivity
 let B:=relative a (4*r) e
 have ht:p∈closedBall a B.rIn:=show dist p a≤4*r/2 from y.trans_eq (by ring)
 have q:(coverall a h).val p=(coverall a h).val a:= by
    change B p/_ = B a/_
    rw [B.one_of_mem_closedBall ht,B.one_of_mem_closedBall (mem_closedBall_self B.rIn_pos.le)]
 unfold BZ
 rw [q,pixelized a e _,sub_self,smul_zero,mul_pow];field_simp
private lemma miss (a:Vantage){r:ℝ}(h:0<r){p:Vantage}(y:r<dist p a): (pixel' a r h).val p=0:=by
 by_contra t
 have e: p∈closedBall a r:=(DoseTravel.supported a (relative a r h)).subset (subset_closure t)
 exact y.not_ge (mem_closedBall.mp e)


lemma bolts:
 ∃ C> (0:ℝ),∀ (a:Vantage) {r:ℝ}(e:0<r){t h:ℝ},0<t → t≤h → h≤r → ∀ (p v:Vantage), ‖v‖≤1 →
 |nick v t p (pixel' a r e)-nick v h p (pixel' a r e)| ≤ (C*(h/r^2))* (coverall a e).val p:=by
 obtain ⟨K,k,T⟩:=blade_s sampleBrae
 refine ⟨K/BZ,div_pos k BZ_pos,fun a r e t h t₀ u w p v hv=>?_⟩
 have h₀:0<h:=lt_of_lt_of_le t₀ u
 by_cases Z: dist p a≤2*r
 · rw [BZ_charge _ e Z,nick_scale a v p e t₀,nick_scale a v p e h₀, ←sub_div,abs_div,abs_of_pos (show 0<r*r^m by positivity)]
   refine (div_le_div_of_nonneg_right (T (div_pos t₀ e) (div_le_div_of_nonneg_right u e.le) _ v hv) (by positivity)).trans_eq ?_
   have b:=BZ_pos
   field_simp

 have t':∀d:ℝ,0<d→d≤r→ r<dist (p-d • v) a:=by
    intro d f g
    have ht:=dist_triangle p (p-d • v) a
    rw [dist_eq_norm p (p-d • v),sub_sub_cancel,norm_smul,Real.norm_eq_abs,abs_of_pos f] at ht
    linarith only [not_le.mp Z,ht,(mul_le_of_le_one_right f.le hv).trans g] 
 unfold nick
 rw [miss a e (lt_of_not_ge (fun d'=>Z (by linarith only [d',e]))),miss a e (t' _ t₀ (u.trans w)), miss a e (t' _ h₀ w),
   sub_self,zero_div,zero_div,sub_self,abs_zero]
 have b:=BZ_pos
 exact mul_nonneg (by positivity) ((cover_ok a e).1 p)

