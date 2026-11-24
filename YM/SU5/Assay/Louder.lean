import YM.SU5.Assay.Draught
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
local notation "H"=> P.large
local notation "b"=> ruler (Λ).block
local notation "V"=> P.law
local notation "L"=> (Λ).R.L.val
local notation "π"=> P.history
local notation "Qt"=> P.projection.clipped
local notation "C₀"=> P.room j
local notation "σ"=> P.shifts j

local notation "μ"=> P.meanBox
local notation "ν"=> P.euclOp
local notation "T"=> P.shiftOp
local notation "Ν"=> whenly (timeMesh (Λ))
local notation "Ω"=> P.floorVec
local notation "S"=> enclave K
local notation "ℵ"=> P.Ensemble j
local notation "ℙ"=>P.pillars j
local notation "χ"=>P.chi j
local notation "ω"=>P.groundZero j
local notation "Φ"=> P.vacuum j
local notation "U"=> P.slabAlgebra j -- not using
local notation "ρ"=> P.reading j s
variable (P j)
/-! Rising power test via recovery. -/
lemma listen (c:ℵ): (∫x,‖χ x c‖^2 ∂ℙ)= ‖c.val ω‖^2:= by
 have he(y:ℂ):star y*y=↑(‖y‖^2:ℝ):=by
    rw [Complex.sq_norm,← Complex.mul_conj y,mul_comm];rfl
 have hx:= P.recovery j (star c*c)
 simp_rw [map_mul,map_star,he] at hx
 have hj: inner ℂ ω ((star c*c).val ω)=inner ℂ (c.val ω) (c.val ω):=ContinuousLinearMap.adjoint_inner_right c.val _ _
 rw [integral_complex_ofReal,hj,inner_self_eq_norm_sq_to_K] at hx
 apply Complex.ofReal_injective
 rw [hx,Complex.ofReal_pow]
 rfl

variable (r:P.Register)(c:P.Ensemble j)(x:P.Spectrum0 j)(D:ℝ) (p:0≤D)
include p r in
lemma hears
  (h:∀n:ℕ, ‖(c^n).val ω‖^2 ≤ D^n) : ‖χ x c‖^2≤ D:=by
 by_contra! v
 obtain ⟨q,a,k⟩:= exists_between v
 let O:Set (P.Spectrum0 j):={y|q<‖χ y c‖^2}
 have hp:IsOpen O:=isOpen_lt continuous_const ((P.chi_joint j c).norm.pow 2)
 have he:0< (ℙ).real O:=by
    letI:=P.pillar_support j r
    exact ENNReal.toReal_pos (hp.measure_ne_zero _ ⟨x,k⟩) (measure_ne_top _ _)
 have hq:=p.trans_lt a
 obtain ⟨n,u⟩:= ((tendsto_pow_atTop_nhds_zero_of_lt_one (div_nonneg p hq.le) ((div_lt_one hq).mpr a)).eventually (gt_mem_nhds he)).exists
 rw [div_pow,div_lt_iff₀ (pow_pos hq n)] at u
 suffices (ℙ).real O * q^n ≤ D^n from u.not_ge this
 rw [←smul_eq_mul, ← setIntegral_const]
 let g(y:P.Spectrum0 j):ℝ:= ‖χ y (c^n)‖^2
 have t:Integrable g ℙ:=((P.chi_joint j (c^n)).norm.pow 2).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
 calc
   _ ≤ ∫y in O,g y ∂ℙ:=by
    apply setIntegral_mono_on (integrable_const _) t.integrableOn hp.measurableSet
    intro y e;change q^n ≤ ‖χ y (c^n)‖^2
    rw [map_pow,norm_pow,pow_right_comm]
    exact pow_le_pow_left₀ hq.le (show q<‖χ y c‖^2 from e).le n
   _ ≤ ∫y,g y ∂ℙ:=setIntegral_le_integral t (Eventually.of_forall fun y=>sq_nonneg _)
   _ ≤ _:=le_trans (P.listen j _).le (h n)
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine
