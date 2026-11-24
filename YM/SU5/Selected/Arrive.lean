import YM.SU5.Selected.Agency
/-! # C0 positive time reconstruction on this phase

Carry at every supported level and on Elector (χ) Born vectors. Single Gauge time step and
physical spatial integer directions. C0 in *time*, no shortcut on the strong spatial test.
Short term solves even and odd with full-season permissions; reconstruction in this sense
still Euclidean. 
-/
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 4500
set_option maxHeartbeats 300000
set_option quotPrecheck false
noncomputable section

namespace YM.CF.Buffered.Afterglow.Tower.Selection
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory
open RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder
open scoped InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Heat Fock Analysis SlabMark OS.Semigroup MeshClock
open Vacancy

variable {Λ : Preparation} {l : ℕ} (Y : Course Λ (VolumeCape.Dream.Nimbus l))
  (H : Real.exp 1 ≤ Λ.x)
local notation "K" => tent Y H
variable {i k : ℕ → ℕ} {I : ℕ → Family (tent Y H) → ℕ → ℂ}
  {E : ℕ → Family (tent Y H) → ℂ} (V : Universal Y H i k I E)
  {D : ℕ → Family (tent Y H) → Family (tent Y H)} {a b : ℕ → ℕ}
  (Q : Coherent (i := i) (k := k) (E := E) Y H D a b)
  (Qc : Clipped Y H (i ∘ a) (k ∘ b))
  (j : Axis) (r : Bool) (C : Arena Y H Q.circuit j 0 r)
local notation "R" => Aurora Y H V Q j r C
local notation "A" => Ark.Ht Y H Q.circuit j 0 r C
local notation "W" => floorV Y H Q.circuit j 0 r C
local notation "F₊" n:max => Tower.Field Y H n j 0 r
local notation "φ" n:max => actor Y H n Q.circuit j 0 r C
local notation "Ω" => seat0 Y H V Q j r C
local notation "π₀" => (R).orthogonalProjectionOnto
local notation "N" n:max => cap Y H V n Q Qc j r C
local notation "Test" => Vacancy.observable (tent Y H) r
local notation "Lab" => Beacon (tent Y H) r

local notation "B" => groundAlgebra Y H V Q Qc j r C
local notation "Β" => pruner Y H V Q Qc j r C
local notation "M" s:max => liftCap Y H V Q Qc j r C s
local notation "uℋ" => basisRoom Y H V Q j r C
local notation "U₀" s:max => timePruner Y H V Q Qc j r C s
local notation "p₀" s:max => spacePruner Y H V Q Qc j r C s
local notation "τ" s:max => tick Y H s j 0 r
local notation "ρ" s:max => ripple Y H V s Q.circuit j 0 r C
local notation "P₀" s:max => stretches Y H V Q Qc j r C s
variable {χ : CapCharacter Y H V Q Qc j r C} (U : Birthplace Y H V Q Qc j r C χ)
local notation "λ₀" => vacuum Y H V Q Qc j r C U
local notation "η" s:max => markedActor Y H V Q Qc j r C U s
local notation "η₀" => leave Y H V Q Qc j r C U

section heat
variable (s : ℕ)
include V Q Qc C
lemma atom_seed : (U₀ s) 0=1 := Subtype.ext (unleash Y H V s Q.circuit j 0 r C)
lemma atom_smalls (k : ℕ) : ‖((U₀ s) k).val‖≤1 := ripple_le Y H V s Q.circuit j 0 r C k
lemma atom_add (a b : ℕ) : (U₀ s) a * (U₀ s) b = (U₀ s) (a+b) := Subtype.ext (breeds Y H V s Q.circuit j 0 r C a b)
lemma atom_refines (u x : ℕ) (p : s ≤ u) : (U₀ s) x= (U₀ u) (amount Λ s u x):=Subtype.ext ((consistent_τ Y H V s Q.circuit j 0 r C x u p).symm)
lemma atom_star (x : ℕ) : star ((U₀ s) x) = (U₀ s) x := Subtype.ext (current_adjoint Y H V s Q.circuit j 0 r C x)
lemma atom_positive (x : ℕ) : 0 ≤ ((U₀ s) x).val := ripple_pos Y H V Q j r C s x
abbrev walking (x : ℕ) := η₀ ((U₀ s) x)
local notation "X" s:max => walking Y H V Q Qc j r C U s
include U
lemma tempo (i t : ℕ) (p : s ≤ t) (x : F₊ t) : (X s) i ((η t) x) = (η t) ((τ t) (amount Λ s t i) x) := acts_on Y H V Q Qc j r C t U _ t x _ (timeAction Y H V Q Qc j r C s t i p x).symm -- U order
lemma tempo_now (i : ℕ) (x : F₊ s) : (X s) i ((η s) x) = (η s) ((τ s) i x) := by rw [tempo Y H V Q Qc j r C U s i s le_rfl, amount_reset]
lemma tempo_unit (t : ℕ) : (X s) t λ₀=λ₀:= by
  -- change both via congr rather than rewrite under iso metric?
  have h := normal_base Y H V Q Qc j r C U s
  exact (congrArg ((X s) t) h).trans ((tempo_now Y H V Q Qc j r C U s t _).trans ((congrArg (η s) (tick_unit Y H s j 0 r t)).trans h.symm))
omit V Q Qc C U in
private lemma dense_predecessor (L : Hilbert) (F : ℕ → Type) (ι : (s:ℕ) → F s → L) (T : ℕ → L → L)
    (p : Dense (⋃ (i:ℕ) (_:0 ≤ i), Set.range (ι i)))
    (h : ∀ i x,∃ v:ℕ, ∃ y:L, T v y=ι i x) : Dense (⋃ (i:ℕ), Set.range (T i)) := by
  refine p.mono ?_
  intro x t; obtain ⟨i,v⟩ := Set.mem_iUnion.mp t; obtain ⟨z,y,rfl⟩ := Set.mem_iUnion.mp v
  obtain ⟨k,u,v⟩ := h i y; exact Set.mem_iUnion.mpr ⟨k,u,v⟩
private lemma backwards (z : F₊ s) : ∃ v : ℕ, ∃ y : U.H, (X v) 2 y = (η s) z := by
  obtain ⟨v,y,h⟩ := predecessor Y H s Q.circuit j 0 r z
  exact ⟨s+v, (η (s+v)) y, (tempo_now Y H V Q Qc j r C U (s+v) 2 y).trans
    ((congrArg (η (s+v)) h).trans (path Y H V Q Qc j r C U s (s+v) (by omega) z))⟩
lemma opens_dense : Dense (⋃ i:ℕ, Set.range (fun x => (X i) 2 x)) :=
  dense_predecessor U.H (fun i => ↥(F₊ i)) (fun i => ⇑(η i)) _
    (born_dense Y H V Q Qc j r C U 0) (backwards Y H V Q Qc j r C U)
-- avoid isDefEq cost of these rewrites whenever possible
lemma tempo_birth : (X s) 0 = ContinuousLinearMap.id ℂ U.H := (congrArg η₀ (atom_seed Y H V Q Qc j r C s)).trans (map_one _)
lemma tempo_star (t : ℕ) : ((X s) t).adjoint=(X s) t:= ((η₀).map_star' _).symm.trans (congrArg η₀ (atom_star Y H V Q Qc j r C s t))
lemma tempo_cost (t : ℕ) : ‖(X s) t‖ ≤ 1 := (reserve_norm Y H V Q Qc j r C U _).trans (atom_smalls Y H V Q Qc j r C s t)

def journey : Many (timeMesh Λ) U.H where
  move s t := (X s) t
  source := tempo_birth Y H V Q Qc j r C U
  close := tempo_star Y H V Q Qc j r C U
  add s i k := ((η₀).map_mul _ _).symm.trans (congrArg η₀ (atom_add Y H V Q Qc j r C s i k))
  refines s t i h := congrArg η₀ (atom_refines Y H V Q Qc j r C s t i h)
  small := tempo_cost Y H V Q Qc j r C U
  early := opens_dense Y H V Q Qc j r C U
local notation "F₀" => journey Y H V Q Qc j r C U
lemma time_carry (t : ℕ) : (X s) t=(F₀).track (whenly (timeMesh Λ) s t/2) :=
  (many_half_time (F₀) s t (reserve_pos Y H V Q Qc j r C U ((U₀ s) t) (atom_positive ..))).symm
lemma time_floor (t : ℝ≥0) : (F₀).track t λ₀=λ₀:= (F₀).track_invariant _ (fun s i => tempo_unit Y H V Q Qc j r C U s (2*i)) t
end heat

section space
variable (s : ℕ) (v : Trans j)
include V Q Qc C
local notation "S₀" s:max t:max => sailV Y H V s Q.circuit j 0 r (t:Trans j).val t.property C
lemma space_cost (x : ℤ) : ‖((p₀ s) v x).val‖≤1 := sailV_small Y H V s Q.circuit j 0 r v.val v.property C x
lemma corner_sum (x y : ℤ) : ((p₀ s) v x)*((p₀ s) v y)=(p₀ s) v (x+y):=Subtype.ext (sailV_sum Y H V s Q.circuit j 0 r v.val v.property C x y)
lemma corner_source : (p₀ s) v 0=1:=Subtype.ext (sailV_source Y H V s Q.circuit j 0 r v.val v.property C)
lemma corner_adj (x : ℤ) : star ((p₀ s) v x)=(p₀ s) v (-x) := Subtype.ext (sails_adj Y H V Q Qc j r C s v x)
lemma corner_finer (t : ℕ) (x : ℤ) (p : s ≤ t) : (p₀ s) v x = (p₀ t) v (smill Λ s t x) := Subtype.ext (sailV_high Y H V s Q.circuit j 0 r v.val v.property C x t p)
lemma corner_time (x : ℤ) (t : ℕ) : Commute ((p₀ s) v x) ((U₀ s) t) := Subtype.ext (sailV_tide Y H V s Q.circuit j 0 r v.val v.property C x t)
lemma corner_cross (w : Trans j) (x y : ℤ) : Commute ((p₀ s) v x) ((p₀ s) w y) := Subtype.ext (sailV_commutes Y H V s Q.circuit j 0 r v.val v.property C w.val w.property x y)

abbrev travel_χ (x : ℤ) := η₀ ((p₀ s) v x)
local notation "S" s:max v:max => travel_χ Y H V Q Qc j r C U s v
include U
lemma travel_acts (x : ℤ) (t : ℕ) (p : s ≤ t) (f : F₊ t) : (S s v) x ((η t) f)=(η t) (sail Y H t j 0 r v.val v.property (smill Λ s t x) f) := acts_on Y H V Q Qc j r C t U _ t f _ (spaceAction Y H V Q Qc j r C s v x t p f).symm
lemma travel_step (x : ℤ) (f : F₊ s) : (S s v) x ((η s) f)=(η s) (sail Y H s j 0 r v.val v.property x f) :=by rw [travel_acts Y H V Q Qc j r C U s v x s le_rfl,smill_id]
lemma travel_floor (x : ℤ) : (S s v) x λ₀=λ₀:=by
  have h:= normal_base Y H V Q Qc j r C U s; exact (congrArg ((S s v) x) h).trans ((travel_step Y H V Q Qc j r C U s v x _).trans ((congrArg (η s) (sail_vacuum Y H s j 0 r v.val v.property x)).trans h.symm))
omit V U C Q Qc in
private lemma anyUnitary {H : Hilbert} {L : Type} [Semiring L] [Algebra ℂ L] [StarRing L] (f : L →⋆ₐ[ℂ] H.Op) (p : L) (h : star p*p=1) (x : H) : ‖f p x‖=‖x‖:= (ContinuousLinearMap.norm_map_iff_adjoint_comp_self _).2 (show star (f p)* f p=1 from by rw [← map_star f, ← map_mul,h,map_one]) x
lemma travel_unitary (x : ℤ) (f : U.H) : ‖((S s v) x) f‖=‖f‖ := by
  have he : star ((p₀ s) v x)*(p₀ s) v x=1:=by rw [corner_adj,corner_sum,neg_add_cancel,corner_source]
  exact anyUnitary (H:=U.H) η₀ _ he f
end space
end YM.CF.Buffered.Afterglow.Tower.Selection
