import YM.SU5.Assay.Fainter
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
variable (P j){I:Type*}(N:Submodule ℂ (P.vacuum j))
local notation "F" a:max => ∀y∈N, StarSubalgebra.subtype (P.compressionAlgebra j) a y ∈N
variable (X:Finset I)(D:I→P.Ensemble j)
private lemma actions (p:∀i∈X, F (D i)∧F (star (D i))):
 let q:= ∑i∈X,star (D i)*D i
 (F q)∧∀u:Φ,(inner ℂ u (q.val u)).re=∑i∈X,‖(D i).val u‖^2:= by
 induction X using Finset.induction with
 | empty=>
    simp only [Finset.sum_empty]; constructor
    · exact fun _ _=> by rw [map_zero,zero_apply]; exact N.zero_mem
    intro u;change (inner ℂ u ((0:P.GroundOp j) u)).re=0;simp
 | insert i X z h=>
    obtain ⟨k,g⟩:=p i (mem_insert_self _ _)
    obtain ⟨l,t⟩:=h fun y e=>p y (mem_insert_of_mem e)
    rw [Finset.sum_insert z]
    let c:= ∑i∈X,star (D i)*D i
    constructor
    · intro y e;exact N.add_mem (g _ (k _ e)) (l _ e)
    intro u
    rw [Finset.sum_insert z]
    change (inner ℂ u ((D i).val.adjoint ((D i).val u)+c.val u)).re=_
    rw [inner_add_right,ContinuousLinearMap.adjoint_inner_right,Complex.add_re,t]
    exact congrArg (·+ _) (@inner_self_eq_norm_sq ℂ _ _ _ _ _)
lemma quieter (R:P.Register)(x:P.Spectrum0 j)(p:∀i∈X, F (D i)∧F (star (D i)))
  (o:∀i∈X,χ x (D i)=0)(b':ω∈N)(δ:ℝ)(y:0<δ): ∃u∈N,‖u‖=1∧∀i∈X, ‖(D i).val u‖<δ:=by
 let c:= ∑i∈X,star (D i)*D i
 have h:χ x c=0:=by
   unfold c; rw [map_sum]; exact Finset.sum_eq_zero fun i e=> by rw [map_mul,o i e,mul_zero]
 obtain ⟨p,e⟩:=P.actions j N X D p
 obtain ⟨u,t,g⟩:=P.inaudible_at j R x N (δ^2) (pow_pos y _) c h b' p
 change ∀u:Φ,(inner ℂ u (c.val u)).re=_ at e
 rw [e] at g
 have v:0<‖u‖:=lt_of_le_of_ne (norm_nonneg _) (by
   intro p;rw [←p,zero_pow two_ne_zero,mul_zero] at g; exact (Finset.sum_nonneg fun _ _=>sq_nonneg _).not_gt g)
 refine ⟨((↑‖u‖:ℂ)⁻¹)•u,N.smul_mem _ t,?_,?_⟩
 · rw [norm_smul,norm_inv,Complex.norm_real,Real.norm_of_nonneg v.le,inv_mul_cancel₀ v.ne']
 intro i p; rw [map_smul,norm_smul,norm_inv,Complex.norm_real,Real.norm_of_nonneg v.le,inv_mul_lt_iff₀ v, mul_comm]
 refine lt_of_pow_lt_pow_left₀ 2 (mul_nonneg y.le v.le) ?_ -- #check
 rw [mul_pow]; exact lt_of_le_of_lt (Finset.single_le_sum (fun i _=>sq_nonneg ‖(D i).val u‖) p) g
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine
