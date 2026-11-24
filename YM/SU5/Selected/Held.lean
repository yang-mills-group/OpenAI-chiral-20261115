import YM.SU5.Selected.Interpret

/-! Lifts of integer-grid Euclidean presentation to any representation of the
selected slab/translation B. No expansion of the spacetime algebra. Use the
actual selected state supplied by Interpret in Physical; here just a representation,
so that all the norm/adjoint/commutation calculations are checked for all cases
including strict. Helps keep proofs feasible without typeclass instance blowup. -/
set_option autoImplicit false
set_option synthInstance.maxSize 30000
set_option maxRecDepth 6000
set_option maxHeartbeats 300000
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
open Set MeshClock
local notation "S"=>stationC Y H V G j strict C
local notation "M"=>timeMesh Λ
local notation "Q"=>heatOp Y H V G j strict C
local notation "U"=>shiftOp Y H V G j strict C
local notation "Be"=>boxElement Y H V G j strict C

structure Acting where
  space : Hilbert
  showL : stationC Y H V G j strict C →⋆ₐ[ℂ] space.Op
  ground : space
  norm1 : ‖ground‖=1
  holds (u:S) : u∈approach Y H V G j strict C → showL u ground=ground
  sees : DenseRange fun t=>showL t ground

namespace Acting
variable (X:Acting Y H V G j strict C)
local notation "ω₀"=>X.ground
local notation "U₀"=>X.showL
noncomputable def clock(t:ℝ≥0):= X.showL (Q t)
local notation "Q₁"=>X.clock Y H V G j strict C
noncomputable def lattice (a:Trans j) (x:marks (timeMesh Λ)) := X.showL (U a x)
local notation "V₁"=>X.lattice Y H V G j strict C

lemma vacuum_time(t:ℝ≥0):Q₁ t ω₀=ω₀:= X.holds _ (Or.inl ⟨_,rfl⟩)
lemma vacuum_space(a:Trans j)(x:marks (timeMesh Λ)): V₁ a x ω₀=ω₀:=X.holds _ (Or.inr ⟨(a,x),rfl⟩)
lemma clock_sum(t u:ℝ≥0): Q₁ (t+u)=Q₁ t * Q₁ u:= by
  have h : Q (t+u)= Q t*Q u:=Subtype.ext (advance_smag ..)
  unfold clock; rw [h,map_mul]
lemma clock_symm(t:ℝ≥0): ContinuousLinearMap.adjoint (Q₁ t)=Q₁ t:=
  have h : star (Q t)= Q t:=Subtype.ext (advance_adjoint ..)
  (map_star X.showL (Q t)).symm.trans (congrArg (X.showL) h)
lemma clock_law (t:ℝ≥0): ‖Q₁ t‖≤1:= (show ‖X.showL (Q t)‖≤ ‖Q t‖ from NonUnitalStarAlgHom.norm_apply_le X.showL _).trans
    (advance_small Y H V G.history.circuit j 0 strict C t)
lemma clock_zero : Q₁ 0=1:=by unfold clock; rw [show Q 0=(1:S) from Subtype.ext (advance_source ..),map_one]
lemma roll_sum(a:Trans j)(x y: marks M): V₁ a (x+y)=V₁ a x*V₁ a y:=by
  have h : U a (x+y)= U a x*U a y:=Subtype.ext (shift_group Y H V G j strict C a x y).symm
  unfold lattice; rw [h,map_mul]
lemma roll_sym(a:Trans j)(x:marks M):star (V₁ a x)=V₁ a (-x):=by
  have h: star (U a x)=U a (-x):=Subtype.ext (shift_star ..)
  unfold lattice; rw [←map_star, h]
lemma roll_zero(a:Trans j): V₁ a 0=1:=by
  unfold lattice; rw [show U a 0=(1:S) from Subtype.ext (shift_origin ..),map_one]
lemma roll_unit(a:Trans j)(x:marks M): V₁ a x ∈ unitary X.space.Op:= by
  rw [Unitary.mem_iff,roll_sym, ← roll_sum, ← roll_sum,neg_add_cancel,add_neg_cancel, roll_zero]
  exact ⟨rfl,rfl⟩
lemma roll_clock(a:Trans j)(x:marks M)(t:ℝ≥0): Commute (V₁ a x) (Q₁ t):= Commute.map (show U a x * Q t= Q t * U a x from Subtype.ext (shift_heat ..|>.eq)) _
lemma roll_commutes(a b:Trans j)(x y:marks M): Commute (V₁ a x) (V₁ b y):= Commute.map (show U a x * U b y= U b y * U a x from Subtype.ext (shift_commutes ..|>.eq)) _

noncomputable def watches(s u:ℕ)(f:Entry Y H s j strict u)(p:0<u):= X.showL (Be s u f p)
local notation "O" s:max f:max p:max=>X.watches Y H V G j strict C s _ f p
lemma box_star {s u:ℕ}(x:Entry Y H s j strict u)(p:0<u): star (O s x p)= O s (inverse Y H s j strict u x) p:=
  (map_star X.showL (Be s u x p)).symm.trans (congrArg X.showL
    (Subtype.ext (respects Y H V s G.history G.clipped j strict C u x p) : star (Be s u x p)=Be s u (inverse Y H s j strict u x) p))
lemma box_product {s u w:ℕ}(x:Entry Y H s j strict u)(y:Entry Y H s j strict w)(p:0<u)(q:0<w):
    (O s x p)*(O s y q)= O s (edit Y H s j strict u w x y) (by omega) :=
  (map_mul X.showL (Be s u x p) (Be s w y q)).symm.trans (congrArg X.showL
    (Subtype.ext (edit_comp Y H V s G.history G.clipped j strict C u w x y p q) :
      (Be s u x p)*(Be s w y q)=Be s (u+w) (edit Y H s j strict u w x y) (by omega)))
lemma box_shift {s u}(x:Entry Y H s j strict u)(p:0<u)(a:Trans j)(i:ℤ):
    V₁ a (notch M s i) * O s x p= O s (alongS Y H s j strict u x a i) p * V₁ a (notch M s i):=by
  have h : U a (notch M s i) * Be s u x p= Be s u (alongS Y H s j strict u x a i) p * U a (notch M s i):=Subtype.ext (notch_comp Y H V G j strict C a x p i)
  unfold lattice watches; rw [←map_mul,←map_mul,h]
lemma blank_clock {s u}(p:0<u): (O s (SlabMark.identity Y H s j strict u) p)=Q₁ (whenly M s u) :=
  congrArg X.showL (Subtype.ext (ticket_birth Y H V s G.history G.clipped j strict C u p) : Be s u (SlabMark.identity Y H s j strict u) p=Q (whenly M s u))
lemma same_box {s u}(t:ℕ)(h:s≤t)(x:Entry Y H s j strict u)(p:0<u):
    O s x p= O t (furnished Y H s G.history j strict u x t h) (Nat.mul_pos (pow_pos Λ.R.L.property _) p):=
  congrArg X.showL (Subtype.ext (refined_box Y H V s G.history G.clipped j strict C u x p t h) : Be s u x p= Be t _ (furnished Y H s G.history j strict u x t h) (Nat.mul_pos (pow_pos Λ.R.L.property _) p))
lemma box_subset {s u}(x:Entry Y H s j strict u)(p:0<u):
    ‖O s x p‖ ≤ ‖B s x p‖ := NonUnitalStarAlgHom.norm_apply_le X.showL (Be s u x p)
end Acting
end YM.CF.Buffered.Afterglow.Tower.PhaseChoice
#print axioms YM.CF.Buffered.Afterglow.Tower.PhaseChoice.Acting.roll_clock
#print axioms YM.CF.Buffered.Afterglow.Tower.PhaseChoice.Acting.box_star
#print axioms YM.CF.Buffered.Afterglow.Tower.PhaseChoice.Acting.box_product
