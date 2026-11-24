import YM.SU5.Selected.GridU
set_option autoImplicit false
set_option synthInstance.maxSize 30000
set_option maxRecDepth 6000
set_option maxHeartbeats 600000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.PhaseChoice
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Heat Fock Analysis SlabMark Vacancy SatinVerification
variable {Λ:Preparation}{l:ℕ}(Y:Course Λ (VolumeCape.Dream.Nimbus l))(H:Real.exp 1≤Λ.x)
local notation "K"=>tent Y H
variable {i k:ℕ→ℕ}{I:ℕ→Family (tent Y H)→ℕ→ℂ}{E:ℕ→Family (tent Y H)→ℂ}
  (V:Universal Y H i k I E)
  (G:GroundExtension (i:=i) (k:=k) (E:=E) Y H)
variable (j : Axis) (strict : Bool) (C : Arena Y H G.history.circuit j 0 strict)
local notation "A"=>Ark.Ht Y H G.history.circuit j 0 strict C
local notation "Fₛ" i:max=>Tower.Field Y H i j 0 strict
local notation "κ" s:max=>actor Y H s G.history.circuit j 0 strict C
local notation "ω"=>floorV Y H G.history.circuit j 0 strict C
local notation "Γ"=>Aurora Y H V G.history j strict C
local notation "Ω"=>seat0 Y H V G.history j strict C
local notation "ι₀"=> (Γ).subtypeL
local notation "π"=> (Γ).orthogonalProjectionOnto
local notation "B" s:max f:max h:max=>boxOp Y H V s G.history G.clipped j strict C _ f h
local notation "P" s:max=>cap Y H V s G.history G.clipped j strict C
/-!
# Resolving one parity: the option of doubled time was safe but unnecessary
for this grid (8B gauge spacing shift at the tower's `tick s 1`). Complete
RP on the full Form at center plane (4B at s and forward support from there)
employs the same readings. Use to remove spectral-root ambiguity even at
fixed s. Does not immediately resolve shorter motion by 2 gauge sites, nor
spatial discontinuous characters. Doesn't identify continuous spatial phases.
-/
open Set MeshClock

section mark
variable {Z:Calibration}{S:Finset Cover}{w b:Bool} {F:Family Z}(p:InTest Z w S b F)
local notation "R" z:max=> mirror Z j z
local notation "U" z:max=> chime Z j z
variable (z x:ℤ)
include p
lemma slides1 : (R z) ((U z) F)= (R 0) F:=reversal Z j z (axial Z j 0 p)
lemma slidesPlane : (R z) F= (U z) ((R 0) F):=(congrArg (R z) (reversal Z j 0 p).symm)
omit p
lemma chimePlane (q:InTest Z true S false F) : (U x) ((R z) F)= (R (z+2*x)) ((U x) F):=by
  rw [slidesPlane j q z,slidesPlane j (flow_port Z j x q) (z+2*x)]
  have h: (R 0) ((U x) F)=(U (-x)) ((R 0) F):=by rw [chime_diag Z j (-x) 0 q,neg_neg]
  rw [h,Tower.bumps Z j _ _ (axial Z j 0 q),Tower.bumps Z j _ _ (axial Z j 0 q), show z+2*x+-x=x+z by omega]
end mark

section law
local notation "ε" x:max=> gaugeShift Λ.block x
local notation "m" x:max => Λ.R.L.val ^ x
local notation "ρ" s:max v:max=> ripple Y H V s G.history.circuit j 0 strict C v
include C V
private lemma oddE (t:ℕ)(x:Fₛ t)(z:ℕ) : 0 ≤ inner ℂ ((κ t) x) ((κ t) (tick Y H t j 0 strict z x)):= by
  obtain ⟨S,h,t'⟩:=(show ∃ S:Finset Cover,InTest K true S false x.val ∧ Tower.region j (meshface (Λ:=Λ) 0 t) (K).ℓ S from ((purpose_ok ..).mp x.property).1)
  let v:= ε z
  have hp : 0≤v:=by unfold v Heat.gaugeShift; positivity
  have r: Tower.region j (ε z) (K).ℓ (address j (ε z) S):=by
     rw [area0] at t'
     intro i e; obtain ⟨k,u,rfl⟩:=mem_image.mp e
     change _+_≤_; simp; specialize t' k u; change v+_ ≤ _+2*v; omega
  rw [stems Y H V,area0]; change 0 ≤ E t (mirror _ _ _ _ * chime K j (ε z) x.val)
  rw [← slides1 j h (ε z)]
  exact boson_axial Y H V t (flow_port K j (ε z) h) r
lemma tick_positive (s v:ℕ) : 0 ≤ ρ s v:= by
  let T:=ρ s v
  have hT : T.adjoint=T:=current_adjoint ..
  apply ContinuousLinearMap.nonneg_iff_isPositive _|>.mpr
  refine ContinuousLinearMap.isPositive_iff' T |>.mpr ⟨hT,fun x=> ?_⟩
  rw [← hT,ContinuousLinearMap.adjoint_inner_left]; change (fun y:A=> 0 ≤ inner ℂ y (T y)) x
  refine closure_minimal (s:=itinerary Y H V G.history.circuit j 0 strict C) (t:={x|0 ≤ inner ℂ x (T x)}) ?rest ?closed (sounds Y H V G.history.circuit j 0 strict C x)
  case closed => exact isClosed_le (f:=fun y:A=> (0:ℂ)) continuous_const (continuous_id.inner T.continuous)
  intro u hu; obtain ⟨w,x⟩:= mem_iUnion.mp hu
  obtain ⟨x,rfl⟩:=x
  let t:=max s w; change 0 ≤ inner ℂ ((κ w) x) (T ((κ w) x))
  rw [← join_actor Y H V G.history.circuit j 0 strict C w t (le_max_right ..)]; unfold T
  rw [limited_time Y H V s G.history.circuit j 0 strict C v (le_max_left s w)]
  exact oddE Y H V G j strict C ..
local notation "M"=>timeMesh Λ
local notation "Q"=>advance Y H V G.history.circuit j 0 strict C
lemma warm_nonneg (r:ℝ≥0):0 ≤ Q r:=by
  set t:=r/2; have h : Q r = star (Q t)*Q t:=by
    have ht: star (Q t)=Q t:=advance_adjoint ..
    rw [ht]; nth_rw 1 [← add_halves r]; exact advance_smag ..
  rw [h]; exact star_mul_self_nonneg _
lemma undoubles (s i:ℕ) : Q (whenly M s i / 2)=ρ s i:= by
  refine (rooted (d:=ρ s (2*i)) ?_ ?_ (warm_nonneg Y H V G j strict C _) (tick_positive Y H V G j strict C s i))
  · have h:= (advance_smag Y H V G.history.circuit j 0 strict C (whenly M s i / 2) (whenly M s i / 2)).symm
    rw [add_halves,advance_at] at h; exact h
  rw [show (ρ s i)*(ρ s i)=ρ s (i+i) from breeds ..,← two_mul]
where rooted {W:Hilbert} {a b d:W→L[ℂ] W}(p:a*a=d)(q:b*b=d)(h:0≤a)(t:0≤b):a=b:=(CFC.sqrt_unique p h).symm.trans (CFC.sqrt_unique q t)
end law

end YM.CF.Buffered.Afterglow.Tower.PhaseChoice
#print axioms YM.CF.Buffered.Afterglow.Tower.PhaseChoice.undoubles
