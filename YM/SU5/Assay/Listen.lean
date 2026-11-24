import YM.SU5.Assay.Hushed
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
variable(s){X:Set P.Test}{n a:ℕ}
local notation "Z"=> P.trail j s w n X
local notation "G"=> (Z).comap (P.inHil j).toLinearMap
local notation "E"=>P.Placard j w n X
local notation "A" c:max=> ∀u∈G, StarSubalgebra.subtype (P.compressionAlgebra j) c u ∈ G
lemma Placard.acts (p:E a f):A (ρ f):=by
 intro u e
 change P.inHil j (P.compressed j s f u) ∈Z
 rw [P.meanBox_state s p.earns]
 exact P.trail_project j s w n X _ (show μ j s a f (P.inHil j u)∈Z from P.trails_draught s p _ e) -- tune
lemma riposte_fee (p:P.BEntry j a f): star (ρ f)=ρ (P.riposte j a f):=by
 apply Subtype.ext
 change (P.compressed j s f).adjoint=P.compressed j s _
 rw [meanBox_state s p,ContinuousLinearMap.adjoint_comp,ContinuousLinearMap.adjoint_comp, meanBox_state s p.riposte]
 unfold piZero inHil; rw [Submodule.adjoint_orthogonalProjectionOnto,Submodule.adjoint_subtypeL]
 change (((Φ).orthogonalProjectionOnto.comp (star (μ j s a f))).comp _)=_
 rw [P.meanBox_star s p];rfl
variable (X n w)
lemma in_scope (h:f∈X)(p:P.BEntry j w f): (A (ρ f))∧ A (star (ρ f)):=by
 have q:E (n+w+n) (σ n f):=Placard.facing h p
 have eq:ρ f=ρ (σ n f):=(P.shifted_read j s n f).symm
 rw [eq,riposte_fee s q.earns]
 exact ⟨q.acts s,q.turn.acts s⟩

variable (P j){X}
local notation "W"=>P.singleState j s
set_option maxHeartbeats 1330000 in
lemma near_ground (D:Finset P.Test)(h:∀i∈D,P.BEntry j w i)(x:P.Spectrum0 j)(R:P.Register)(δ:ℝ)(y:0<δ):
 ∃u:Φ,P.inHil j u ∈ P.trail j s w n D ∧‖u‖=1∧
   ∀i∈D,‖P.compressed j s i u-W x i•u‖<δ:= by
 let c(i:P.Test):ℵ:=ρ i-W x i • 1
 let X:Set P.Test:=D
 let N:Submodule ℂ (Φ):=(P.trail j s w n X).comap (P.inHil j).toLinearMap
 have t(i:P.Test):χ x (c i)=0:=by unfold c;rw [map_sub,map_smul,map_one,smul_eq_mul,mul_one,P.single_state,sub_self]
 refine P.quieter j N D c R x ?_ (fun i _=>t i) (P.trails_start j s w n X) δ y
 intro i e
 obtain ⟨a,g⟩:=P.in_scope s w X n (f:=i) e (h _ e)
 unfold c;rw [star_sub,star_smul,star_one]
 exact ⟨fun z u=>N.sub_mem (a z u) (N.smul_mem (W x i) u),fun z u=> N.sub_mem (g z u) (N.smul_mem (star (W x i)) u)⟩
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine
