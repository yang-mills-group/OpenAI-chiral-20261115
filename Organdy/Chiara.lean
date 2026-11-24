import YM.SU5.FiniteGaugeData.Tower.Diagram
import Organdy.Treasury
import YM.SU5.Selected.MeshSym

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.flexible false
set_option synthInstance.maxSize 24000
set_option maxRecDepth 6000
set_option maxHeartbeats 500000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Organdy.Royal
open Buffered Buffered.Afterglow
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Pastry Tenant Tower

open VacuumSelection


/- Moment estimates for P.selected; chrono-CS iteration independent of density rule. -/
section
variable (P:Spine)(s:ℕ)(j:Axis)
local notation "H"=>P.calibration
variable (x:P.Spectrum0 j)
local notation "R" t:max=> Heat.gaugeShift P.par.block t
local notation "eS"=> P.singleState j s x

open Tapestry
lemma single_one : eS 1=1:=by rw [P.single_state,P.reading_unit,map_one]
lemma single_star (u:ℤ)(f:P.Test): eS (aureole H j (R u) f)=star (eS f):=by 
 rw [P.single_state,P.lightStar,map_star];rfl

/-- CS against the unit, real form for propagation through moments. -/
lemma prestissimo (S:Finset Cover)(u:ℤ)
 (f:P.Test)(h:f∈ bay H S true)(q:Tower.region j (R u) (H).ℓ S):
 ‖eS f‖^2 ≤ (eS (aureole H j (R u) f * f)).re := by
 let a:=aureole H j (R u)
 let c:=eS f
 let v:= -c
 let k:=f + v • 1
 have d:0≤eS (a k*k):=
   P.elevated j s x k u ((bay H S true).add_mem h ((bay H S true).smul_mem (one_mem _) v)) q
 have w:a k = a f + star v • 1:=by
    apply Subtype.ext
    change Tower.mirror H j (R u) (f.val + v • 1)= Tower.mirror H j (R u) f.val + star v • 1
    rw [mirror_plus,mirror_scale,mirror_unit]
 have b:(-star c)*(-c)=(↑(‖c‖^2:ℝ):ℂ):=by
    rw [neg_mul_neg,mul_comm,Complex.sq_norm,←Complex.mul_conj]; rfl

 have b':star c*c=(↑(‖c‖^2:ℝ):ℂ):=by rwa [neg_mul_neg] at b
 unfold v at w
 have u1:=single_star P s j x u f
 rw [w, show k=f+(-c) • 1 from rfl, add_mul,mul_add,mul_add,
     Algebra.mul_smul_comm,Algebra.smul_mul_assoc,Algebra.smul_mul_assoc, one_mul,mul_one,one_mul,map_add,map_add,map_add,
     map_smul,map_smul,map_smul,map_smul,single_one,smul_eq_mul,smul_eq_mul,smul_eq_mul,smul_eq_mul,star_neg] at d
 rw [show eS (a f)=star c from u1,show eS f=c from rfl,mul_one,b,
    neg_mul,neg_mul,mul_comm c (star c),b'] at d
 have g:=Complex.re_le_re d
 rw [Complex.zero_re,Complex.add_re,Complex.add_re,Complex.add_re,Complex.neg_re,Complex.ofReal_re] at g
 exact (show ‖c‖^2≤(eS (a f*f)).re by linarith only [g])

#print axioms prestissimo

/- Local moment lemma like Staved.thine, full support purchased here
    with Spine.Register. -/
open Set MeasureTheory.Measure TopologicalSpace
private lemma thine {X:Type*}[MetricSpace X][CompactSpace X][MeasurableSpace X][BorelSpace X](μ:Measure X)[IsProbabilityMeasure μ][μ.IsOpenPosMeasure] (f:X→ℝ)(v:Continuous f)(c:ℝ)(t:0≤c)(e:∀ x,0≤f x)
    (P0:∀ n:ℕ, (∫ i,(f i)^(2*(2^n)) ∂μ) ≤ c^(2*(2^n))) (x:X) : f x≤ c:=by
 classical
 by_contra! h; obtain ⟨u,r,p⟩:= exists_between h
 let F:= {x| u<f x}; have hu: IsOpen F:=isOpen_lt continuous_const v; let T:= μ.real F; have hT:0<T:= ENNReal.toReal_pos (Measure.IsOpenPosMeasure.open_pos _ hu ⟨x,p⟩) (measure_ne_top _ _)
 have he(n:ℕ):T ≤ (c/u)^(2*(2^n)):=by
    let k:=2*(2^n); let a(i:X):=(f i)^k; have hf:Integrable a μ:= (v.pow _).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
    rw [div_pow]; apply (le_div_iff₀ (pow_pos (t.trans_lt r) _)).2
    apply (P0 n).trans'; change T*u^k ≤ _; rw [show T*u^k=∫ _ in F,u^k ∂μ by simp [T]]
    exact (setIntegral_mono_on (integrable_const _) hf.integrableOn hu.measurableSet (fun y hy=> pow_le_pow_left₀ (t.trans_lt r).le (show u<f y from hy).le _)).trans (setIntegral_le_integral hf (ae_of_all _ (fun i=> pow_nonneg (e i) _)))
 have hz:Tendsto (fun n:ℕ=>2*(2^n)) atTop atTop:= tendsto_atTop_mono (fun i=> le_trans Nat.lt_two_pow_self.le (Nat.le_mul_of_pos_left _ two_pos)) (show Tendsto id (atTop:Filter ℕ) atTop from tendsto_id) -- tune
 exact hT.not_ge (ge_of_tendsto' ((tendsto_pow_atTop_nhds_zero_of_lt_one (div_nonneg t (t.trans_lt r).le) (div_lt_one (t.trans_lt r)|>.2 r)).comp hz) he)



theorem swell (K:P.Register)(f:P.Test){w:ℝ}(v:0 ≤ w)
 (b:∀ n:ℕ,∃ g:P.Test,
    (∀x:P.Spectrum0 j, ‖P.singleState j s x f‖^(2*(2^n)) ≤ (P.singleState j s x g).re)
        ∧ (P.E s g.val).re ≤ w^(2*(2^n))):
 ‖P.singleState j s x f‖≤w:=by
 haveI:=P.metricX j K; letI:=metrizableSpaceMetric (P.Spectrum0 j); haveI:=P.pillar_support j K
 let a (h:P.Test)(t:P.Spectrum0 j):=P.singleState j s t h
 have hc(h):Continuous (a h):= P.chi_joint j _
 refine thine (P.pillars j) (fun t=>‖a f t‖) (hc f).norm _ v (fun _=>norm_nonneg _) (fun n=>?_) x
 obtain ⟨g,d,t⟩:=b n
 have h:= P.recovery j (P.reading j s g)
 have u:=P.occupied j s g

 have o:(∫ t,a g t ∂P.pillars j) = P.E s g.val:=h.trans u
 have g1:= (hc g).integrable_of_hasCompactSupport (μ:=P.pillars j) (HasCompactSupport.of_compactSpace _)
 apply (integral_mono (((hc f).norm.pow (2*(2^n))).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)) g1.re d).trans
 rw [integral_re g1,o];exact t
#print axioms swell


#check Tapestry.broadCompile
#print Spine.persona