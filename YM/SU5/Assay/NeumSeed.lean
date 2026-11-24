import YM.SU5.Assay.Taste
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 4900
set_option maxHeartbeats 420000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine
open Function Filter NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
variable {P:Spine}{j:Axis}{s v w:ℕ}{f g:P.Test}
local notation "Λ"=> P.par
local notation "Y"=> P.run
local notation "K"=> P.calibration
local notation "V"=> P.law
local notation "L"=> (Λ).R.L.val
local notation "π"=> P.history
local notation "Qt"=> P.projection.clipped
local notation "C₀"=> P.room j
local notation "σ"=> P.shifts j

variable {y:ℂ}{S:Finset Cover}
local notation "T₀"=> enclave P.calibration

lemma budget_exp_small (t:ℝ)(p:0≤t)(h:t≤1/2):Real.exp t ≤1+2*t:=by
 have u:t<1:=by linarith
 apply (Real.exp_bound_div_one_sub_of_interval p u).trans
 apply (div_le_iff₀ (sub_pos.mpr u)).mpr; nlinarith only [mul_le_mul_of_nonneg_right h p]

-- Adapted from Relativistic/Royard.
private lemma budget_tiny {x:ℂ}(W t:ℝ)(h:0<W)(q:0<t)
    (A:‖1+(W:ℂ)*x‖ ≤1+2*t*W)(B:‖1+ (-(W:ℂ))*x‖ ≤1+2*t*W)(C: ‖1+ Complex.I *(W:ℂ)*x‖≤1+2*t*W)(D:‖1+ (-Complex.I)*(W:ℂ)*x‖ ≤1+2*t*W): ‖x‖ ≤4*t:=by
 have hv :(0:ℝ)<2*t:=by positivity
 have H(x:ℂ)(g:‖x‖≤ 1+2*t*W): x.re≤ 1+2*t*W:= (Complex.re_le_norm _).trans g
 obtain ⟨ha,hb,hc,hd⟩:= (show _ from And.intro (H _ A) (And.intro (H _ B) (And.intro (H _ C) (H _ D))))
 simp only [Complex.add_re,Complex.mul_re,Complex.one_re,Complex.I_re,Complex.I_im,Complex.ofReal_re,Complex.ofReal_im,Complex.neg_re,zero_mul, sub_zero,Complex.mul_im,mul_zero,neg_mul,one_mul] at ha hb hc hd
 have he: |x.re|≤2*t:=abs_le.mpr (by constructor <;> nlinarith)
 have hx: |x.im|≤ 2*t:=abs_le.mpr (by constructor <;> nlinarith)
 exact (Complex.norm_le_abs_re_add_abs_im _).trans (by linarith)

lemma Taste.watch (u:f∈bay K S true)(g:f∈T₀)(q:P.Taste f S y)(j:Axis)(ε:ℝ)(he:0<ε):
    ∀ᶠ s in atTop,∀ x:P.Spectrum0 j, ‖P.singleState j s x f-y‖≤ ε:=by
 let t:=ε/16; have ht:0<t:=by unfold t; positivity
 obtain ⟨ζ,p,G⟩:=q j _ ht
 let W:=min ζ (1/(6*t)); have hW:0<W:=lt_min p (by positivity); let A:ℂ:=↑W
 have hA:‖A‖=W:=by unfold A; rw [Complex.norm_real,Real.norm_of_nonneg hW.le]
 have hx(Z:ℂ)(e:‖Z‖=W):∀ᶠ s in atTop,∀ x:P.Spectrum0 j,‖1+ Z*(P.singleState j s x f-y)‖≤ 1+ 2*(3*t)*W:=by
    obtain ⟨d,v,B,h⟩:=G Z (e.symm ▸ hW) (e.trans_le (min_le_left ..))
    have hu:=B.admit (tasteTest_bay u y Z) d j le_rfl (v:=d+d) (by omega) (by omega)
    filter_upwards [h] with s h x
    have hh:=(singleState_le_meanBox s x hu (P.shifts_keep j d (tasteTest_color g y Z))).trans h
    rw [slide_single,tasteTest,map_add,map_smul,map_add,map_smul,show P.singleState j s x 1=1 from by rw [P.single_state,P.reading_unit,map_one],smul_eq_mul,smul_eq_mul,mul_one,←sub_eq_add_neg,e] at hh
    apply hh.trans; rw [←mul_assoc 3,mul_assoc 2 (3*t)]
    apply budget_exp_small _ (by positivity)
    have u':W ≤ 1/(6*t):=min_le_right ..
    rw [le_div_iff₀ (by positivity:0<6*t)] at u'; nlinarith only[u']
 filter_upwards [hx A hA,hx (-A) (by rw [norm_neg,hA]),hx (Complex.I*A) (by simp [hA]),hx ((-Complex.I)*A) (by simp [hA])] with s X Y' Z Q x
 have he':= budget_tiny W (3*t) hW (by positivity) (X x) (Y' x) (Z x) (Q x)
 apply he'.trans; unfold t; linarith

/-! One Neumann factor R:=1-a•f. d width ticks at each resolution.
 Gain `0≤c<1` independent of resolution. -/
variable (P)
def ResidualTag (j:Axis) (f:P.Test)(S:Finset Cover)(d:ℕ)(a:ℂ)(c:ℝ):Prop:=
   0<d ∧ a≠0 ∧ 0≤c ∧ c<1 ∧ P.BFits d S ∧
    ∀ᶠ s in atTop,‖P.meanBox j s (d+d) (P.shifts j d (1-a•f))‖ ≤ c

lemma Taste.neum (q:P.Taste f S y)(u:f∈bay K S true)(p:y≠0)(j:Axis):
 ∃ d a c,P.ResidualTag j f S d a c:=by
 let ε:=‖y‖/12; have hy:=norm_pos_iff.mpr p
 obtain ⟨ζ,h,g⟩:= q j ε (by unfold ε; linarith)
 let t:ℝ:=min (ζ*‖y‖) 1; have H₀ : t≤1:=min_le_right ..; have hv:0<t:=lt_min (mul_pos h hy) zero_lt_one
 let k:ℝ:=1+t; have hk:0<k:=by unfold k; linarith
 have ht' : (t:ℂ)≠0:=Complex.ofReal_ne_zero.mpr hv.ne'
 have hk':(k:ℂ)≠0:=Complex.ofReal_ne_zero.mpr hk.ne'
 let z:ℂ:= -((t:ℂ)/y); let a:= -(k:ℂ)⁻¹*z
 have ha:a≠0:=mul_ne_zero (neg_ne_zero.mpr (inv_ne_zero hk')) (neg_ne_zero.mpr (div_ne_zero ht' p))
 have hz:‖z‖=t/‖y‖:=by unfold z; rw [norm_neg,norm_div,Complex.norm_real,Real.norm_of_nonneg hv.le]
 obtain ⟨d,v,B,G⟩:=g z (hz.symm ▸ div_pos hv hy) (hz.symm ▸ (div_le_iff₀ hy).mpr (min_le_left ..))
 let c:= k⁻¹*Real.exp (3*(ε*‖z‖))
 have he:3*(ε*‖z‖)=t/4:=by unfold ε; rw [hz]; field_simp; ring
 have hy:Real.exp (3*(ε*‖z‖)) < k:=by rw [he]; apply (budget_exp_small _ (by positivity) (by linarith)).trans_lt; unfold k; linarith
 refine ⟨d,a,c,v,ha,(by unfold c; positivity),(inv_mul_lt_one₀ hk).mpr hy,B,?_⟩
 have hx:1-a•f=(k:ℂ)⁻¹ • tasteTest f y z:=by
   have hw:z*(-y)=t:=by unfold z; field_simp
   have h₁:(k:ℂ)⁻¹+(k:ℂ)⁻¹*(t:ℂ)=1:=by rw [←mul_one_add,show (1:ℂ)+(t:ℂ)=(k:ℂ) by unfold k; push_cast; rfl,inv_mul_cancel₀ hk']
   unfold tasteTest; rw [smul_add z,smul_smul,hw]; unfold a; calc
     _=( (k:ℂ)⁻¹+(k:ℂ)⁻¹*(t:ℂ)) • (1:P.Test)+ (((k:ℂ)⁻¹*z)• f) := by rw [h₁,one_smul]; module
     _=_:=by module
 have w:=B.admit (tasteTest_bay u y z) d j le_rfl (v:=d+d) (by omega) (by omega)
 filter_upwards [G] with s g
 rw [hx,map_smul,meanBox_smul s w,norm_smul,norm_inv,Complex.norm_real,Real.norm_of_nonneg hk.le]
 exact mul_le_mul_of_nonneg_left g (by positivity)
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine
