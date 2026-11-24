import YM.SatinExist.Ager
import YM.SU5.Selected.Reserved
import YM.SU5.Selected.CommonGround

/-! # Budget Azure's `Sphere` for the disclosed physical elected Phi (2)

Match full unselected Arena at every axis in actual FiniteGaugeData reconstruction. Crucial there isn't an
uncaptured superfluous gauge-dependent-mark sector in that prescription. Use exact `reserved_arena`
of CP18.
-/
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 4500
set_option maxHeartbeats 500000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
namespace Spine
variable (P : Spine)
local notation "K" => P.calibration
local notation "Λ" => P.par
local notation "ι" => P.width
local notation "Y" => P.run
local notation "H" => P.large
local notation "ℒ" => P.law
local notation "π"=> P.history
local notation "Λ₁"=> Λ.R.L
open Afterglow.Hierarchy Hierarchy
open Chrono Hills
variable {C:Call P.par P.width}{W:Wicket P.par P.width}(R:Rolled P.run P.large P.period P.cutoff W C)
variable (j: Axis) (s : ℕ)
local notation "M₀"=> P.room j
local notation "Λᵥ"=> purpose (K) -- later

/-- The very SAME Bud. On all consultations; constraint interpreted as WIP.
-/
noncomputable def azureVox (x:Chrono.Decko P.run P.large j) : P.Vox j s := by
  refine ⟨x.val.val, (purpose_ok ..).mpr ⟨?_,nofun⟩⟩
  obtain ⟨S,q,u⟩:= Decko.atlas Y H j x
  rw [area0]; exact ⟨S,u,q⟩
private lemma deckoVox_dense (x: Tower.Field P.run P.large s j 0 true) :
    ∃ b:Decko Y H j, Selected.admit Y H s j x=P.azureVox j s b:=by
  let y:= (Selected.admit Y H s j x); have e:= (purpose_ok ..).1 x.property
  let v:= P.voxTest j s y
  let F:Charm.W K := ⟨x.val,v.property, e.2 rfl⟩
  have hp:Canaan Y H j F 0:=by obtain ⟨S,p,u⟩:=e.1; exact ⟨S,(by rw [area0] at u; exact u),p⟩
  exact ⟨(⟨F,hp⟩:Decko Y H j), rfl⟩
local notation "X"=> P.Hil j
variable (A:Repertory P.run P.large P.law R j)
local notation "V"=> A.space
local notation "S₀" s:max=> store Y H s ℒ R j A
local notation "T₀" s:max x:max=> P.piece j s (P.azureVox j s x)
lemma volume_pea (x:Decko Y H j):
    T₀ (s+1) (nectar Y H s ℒ R j x)=T₀ s x:=by
  let y:= P.azureVox j s x
  have ht:P.azureVox j (s+1) (nectar Y H s ℒ R j x)= Raise Y H P.history.circuit j 0 false s (s+1) (by omega) y:=by
    apply Subtype.ext; change (Charm.next Y H s ℒ R x.val).val=stream Y H P.projection.refine s (s+1-s) x.val.val
    rw [show s+1-s=1 by omega]; exact P.azure_advances s R x.val
  rw [ht]; exact join_actor Y H ℒ P.history.circuit j 0 false (M₀) s (s+1) (by omega) y
private lemma through_here (i:ℕ)(p : s ≤ i)(x:Decko Y H j): ∃ y: Decko Y H j,
    (S₀ s) x=(S₀ i) y ∧ T₀ s x = T₀ i y :=by
  induction i,p using Nat.le_induction with
  | base=> exact ⟨x,rfl,rfl⟩
  | succ i p ih=> obtain ⟨y,h,e⟩:= ih; exact ⟨nectar Y H i ℒ R j y, h.trans (for_next Y H i ℒ R j A y).symm, e.trans (P.volume_pea R j i y).symm⟩
private lemma gramAzure (x y:Decko Y H j): inner ℂ ((S₀ s) x) ((S₀ s) y)=inner ℂ (T₀ s x) (T₀ s y):=by
  rw [lawStore]; change _ = inner ℂ (actor Y H s P.history.circuit j 0 false (M₀) _) (actor Y H s P.history.circuit j 0 false (M₀) _)
  rw [Tower.stems Y H ℒ P.history.circuit j 0 false (M₀), area0]
  rfl
local notation "Ι" => ℕ × Decko Y H j
include A
private lemma fullRange : ∃ e:A.space≃ₗᵢ[ℂ](P.Hil j).space,
    ∀ s:ℕ,∀ x:Decko Y H j,e ((S₀ s) x)=T₀ s x:=by
  let src (z:Ι):V := (S₀ z.1) z.2; let dst (z:Ι):X := T₀ z.1 z.2
  have hs:DenseRange src:= A.issued.mono (by rintro i ⟨x,rfl⟩; obtain ⟨s,h⟩:= (eventual_table Y H ℒ R j A x).exists; exact ⟨(s,days Y H s ℒ R j x),h⟩)
  have hb:DenseRange dst := (Selected.reserved_arena Y H ℒ π P.projection.clipped j (M₀)).mono (by
    rintro _ p; obtain ⟨s,x,rfl⟩:= Set.mem_iUnion.mp p; obtain ⟨x',e⟩:= P.deckoVox_dense j s x
    exact ⟨(s,x'),congrArg (P.piece j s) e.symm⟩)
  obtain ⟨g,h⟩:= intertwine («A»:=V) («B»:=X) src dst (hs.mono Submodule.subset_span) (hb.mono Submodule.subset_span) (by
    rintro ⟨i,x⟩ ⟨k,y⟩; obtain ⟨u,p,q⟩:= P.through_here R j i A (max i k) (le_max_left ..) x; obtain ⟨v,t,w⟩:= P.through_here R j k A (max i k) (le_max_right ..) y
    dsimp only [src,dst]; rw [p,q,t,w]; exact P.gramAzure ..)
  exact ⟨g,fun i x=>h (i,x)⟩
noncomputable def foyerAz : A.space≃ₗᵢ[ℂ](P.Hil j).space:=(P.fullRange R j A).choose
lemma azure_kin (s:ℕ)(x:Decko Y H j): P.foyerAz R j A ((S₀ s) x) = T₀ s x := (P.fullRange R j A).choose_spec s x
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
