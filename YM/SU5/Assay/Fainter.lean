import YM.SU5.Assay.Louder
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
private lemma factors_exist (D e:ℝ)(p:0<e): ∃ t:ℝ,0<t∧ t*D^2≤e∧e*t<1:=by
 obtain ⟨t,h,v⟩:= exists_between (show (0:ℝ)< min (e/(D^2+1)) e⁻¹ by positivity)
 obtain ⟨a,z⟩:=lt_min_iff.mp v
 refine ⟨t,h,?_,?_⟩
 · rw [lt_div_iff₀ (by positivity)] at a;linarith
 rwa [mul_comm,←lt_div_iff₀ p,one_div]

variable (P j)
lemma inaudible_at (R:P.Register)(x:P.Spectrum0 j)(N:Submodule ℂ (P.vacuum j))(e:ℝ)(p:0<e)(c:ℵ)
  (o:χ x c=0)(Q:ω∈N)(M:∀u∈N,c.val u∈N): ∃u∈N,(inner ℂ u (c.val u)).re<e*‖u‖^2:=by
 by_contra! v
 obtain ⟨t,h,t',z⟩:=factors_exist ‖c.val‖ e p
 let D:=1-e*t
 have g:0≤D:=(sub_pos_of_lt z).le
 let B:ℵ:=1-(t:ℂ)•c
 have Bu (u:Φ): B.val u=u- (t:ℂ)•(c.val u):=rfl
 have m(u:Φ)(r:u∈N): ‖B.val u‖^2 ≤ D*‖u‖^2:=by
   rw [Bu,norm_sub_sq (𝕜:=ℂ), norm_smul,Complex.norm_real,Real.norm_of_nonneg h.le,inner_smul_right]
   have f:(RCLike.re ((↑t:ℂ)*inner ℂ u (c.val u)))=t*(inner ℂ u (c.val u)).re:=by change ((↑t:ℂ)*inner ℂ u _).re=_; simp [Complex.mul_re]
   rw [f]
   have hy:= mul_le_mul_of_nonneg_left (v _ r) h.le
   have y:(t*‖c.val u‖)^2 ≤ t*e*‖u‖^2:=by
     calc
       _ ≤ (t*(‖c.val‖*‖u‖))^2:=by gcongr; exact c.val.le_opNorm u
       _ = t*(t*‖c.val‖^2)*‖u‖^2:=by ring
       _ ≤ _:=by gcongr
   unfold D; linarith only [hy,y]
 have A(n:ℕ):(B^n).val ω ∈N∧‖(B^n).val ω‖^2 ≤D^n:=by
    induction n with
    | zero=>
      rw [pow_zero,pow_zero]
      change ω∈N∧ ‖ω‖^2≤1
      simpa [P.ground_norm]
    | succ n ih=>
      rw [pow_succ',pow_succ' D]
      let y:=(B^n).val ω
      change B.val y∈N∧‖B.val y‖^2≤D*_
      refine ⟨?_,le_trans (m y ih.1) (mul_le_mul_of_nonneg_left ih.2 g)⟩
      rw [Bu]; exact N.sub_mem ih.1 (N.smul_mem _ (M _ ih.1))
 have k:= P.hears j R B x D g (fun i=>(A i).2)
 unfold B at k; rw [map_sub,map_one,map_smul,o,smul_zero,sub_zero,norm_one,one_pow] at k
 exact k.not_gt (sub_lt_self _ (mul_pos p h))
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine
