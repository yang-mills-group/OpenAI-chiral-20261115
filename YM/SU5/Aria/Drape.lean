import YM.SU5.Aria.Stagehand
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 4500
set_option maxHeartbeats 220000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
open Germ Alliance
namespace Spine
variable (P: Spine) (j:Axis) (x:P.Spectrum0 j)
open Aria Set TopologicalSpace Metric
local notation "Λ"=> P.par
local notation "κ"=> P.calibration
local notation "ℓ"=> (κ).ℓ
local notation "b"=> ruler P.par.block
local notation "ρ"=> P.width
local notation "Μ"=> timeMesh P.par
local notation "Γ"=> marks (timeMesh P.par)
local notation "H"=> P.large
local notation "Y₀"=> P.run
local notation "Φ" => P.colorSpace j x
/-
This is a PHYSICAL-resolution rectangle, with each axis lower & upper faces
at integer offsets from center at actual s. Physical field `Knot` still in
true P system using SU.group & same charge/poly costs etc. Neighborhood is in
fermion units (2 × these get gauge coords used in `V`). At VERY fine resolutions
one can successively shrink allowance, not claiming limit labels at points yet.
-/
structure Apron where
 s : ℕ
 u : Axis→ℕ
 pos(i:Axis) : 0<u i
 F : P.Test
 S : Finset Cover
 bay : F∈bay P.calibration S true
 realM : F∈enclave P.calibration
 shelter(i:Axis): Between P.calibration i (- ruler P.par.block*u i) (ruler P.par.block*u i) S
namespace Apron
variable (D:P.Apron)
local notation "ϑ"=> D.u j
noncomputable def realWidth (k:Axis):ℝ := bell (timeMesh P.par) D.s (D.u k)
def scenery (a: Vantage) : Set RSpace:= {p|∀ i,|p i - 2*a i| ≤ 2*D.realWidth P i} -- field notation Apron.realWidth P D; check
lemma distance_mark (n:ℕ)(x:ℤ) : 2*bell Μ n x=markZ Λ n (b*x):=by
 unfold bell mill markZ precisionAt ruler timeMesh -- tune order
 change 2*((x:ℝ)*(↑(((8:ℝ≥0)*P.par.block.val)/ (↑P.par.R.L.val:ℝ≥0)^n):ℝ))=_; push_cast; ring
lemma efficiency : printedHere P.par P.width D.s D.S (scenery P D 0):=by
 intro d z u v i
 have hz:=D.shelter i d z; obtain ⟨he,hj⟩:= hz
 let q:= P.par; let W:= D.realWidth P i; let T:ℤ:= b*D.u i; let μ := precisionAt Λ D.s
 have hw:0<μ:=positiveScale ..
 have ht: 2*W=markZ Λ D.s T:= distance_mark P D.s (D.u i)
 have hv := abs_le.mp (v i); change (-((Journey.reserve Λ P.width):ℝ) ≤ μ*u i-(d i:ℝ)) ∧ (_ ≤ (Journey.reserve Λ P.width:ℝ)) at hv
 obtain ⟨e,h⟩:=hv
 have hs:(d i:ℝ)+(Journey.reserve Λ P.width:ℝ) ≤ (T:ℝ):=by exact_mod_cast (show d i + (Journey.reserve Λ P.width:ℤ) ≤ T from hj)
 have ht':-(T:ℝ)+(Journey.reserve Λ P.width:ℝ) ≤ (d i:ℝ):=by exact_mod_cast (show -T+(Journey.reserve Λ P.width:ℤ) ≤ d i by rw [neg_mul] at he; exact he)
 change |u i- 2*0| ≤ 2*W; simp only [ht,mul_zero,sub_zero]
 rw [markZ,abs_le]; change -(T/μ) ≤ u i∧ _
 rw [← neg_div, div_le_iff₀ hw]; constructor
 · linarith
 apply (le_div_iff₀ hw).2; linarith
lemma ticket : D.F∈ keep Λ P.width D.s (κ) true (D.scenery P 0):=⟨_,D.bay,D.efficiency P⟩
local notation "S₀"=>P.shifts j ϑ D.F
local notation "Q"=>plow κ j ϑ D.S
lemma inside_shift : Between κ j 0 (b*(ϑ+ϑ)) Q := by
 have hx:=Between.relocate κ j (D.shelter j) ϑ; rw [show ruler (κ).B=b from rfl,neg_mul,add_neg_cancel, ← mul_add] at hx; exact hx
noncomputable def cardB : P.Card j D.s (ϑ+ϑ):=by
 let ht:=D.inside_shift P j; have h: S₀∈ Tapestry.bay κ Q true:= P.shifts_support _ _ D.S D.bay
 refine ⟨P.positiveVox j D.s Q (S₀) h (fun x t=> (ht x t).1), Q,h,?_⟩; rw [Nat.cast_add]; exact ht
lemma card_price : P.voxTest j D.s (D.cardB P j).val=S₀ := rfl
lemma color : S₀∈ enclave κ:= P.shifts_keep j _ D.realM -- syntax
noncomputable def engine : (P.ColorHil j x).Op:= Φ (P.door j D.s (ϑ+ϑ) (by have h:=D.pos j; omega) (D.cardB P j) (D.color P j))
lemma real_width_pos : 0< D.realWidth P j:=by
 change 0< (↑(↑(ϑ:ℕ):ℤ):ℝ)* _; have ht: 0<(↑(↑(D.u j):ℤ):ℝ):=by exact_mod_cast D.pos j
 exact mul_pos ht (mill_pos ..)
-- refines *and maintains op, widths in real units*. Satisfied on any n≥s.
abbrev zoom (n:ℕ) (i:Axis):ℕ:=P.par.R.L.val^(n-D.s)*D.u i
noncomputable def full (n:ℕ):= P.conveying D.s (n-D.s) D.F
variable (n:ℕ)(e:D.s ≤ n)
include e
lemma marks_equal : notch Μ n (D.zoom P n j)= notch Μ D.s (D.u j):=by
 have he:= notch_up Μ D.s n e (D.u j); rw [←he]; congr 1
lemma full_realizes :
   ∃ (u: P.Card j n (zoom P D n j+zoom P D n j)), P.voxTest j n u.val=P.shifts j (D.zoom P n j) (D.full P n) ∧ P.atSide j D.s (ϑ+ϑ) (add_pos (D.pos j) (D.pos j)) (D.cardB P j)=P.atSide j n _ (add_pos (mul_pos (pow_pos (Λ).R.L.property _) (D.pos j)) (mul_pos (pow_pos (Λ).R.L.property _) (D.pos j))) u:=by
 -- logic to avoid cast above use subgoal
 let d:=D.u j; let w:= D.zoom P n j+D.zoom P n j; let z:=D.cardB P j; let x':=furnished Y₀ H D.s P.history j false _ z n e
 have hz:w=(Λ).R.L.val^(n-D.s)*(d+d):=by unfold w zoom; rw [mul_add]
 have hp: P.shifts j (D.zoom P n j) (D.full P n)= P.voxTest j n x'.val:=by
   rw [show (D.zoom P n j:ℤ)=(castor Μ D.s n d) from (notch_tight _ _ ((D.marks_equal P j n e).trans (notch_up _ _ _ e d).symm)),Apron.full]; unfold d; rw [← P.walk_rig D.s n j _ D.F,← D.card_price P j]; rfl -- walk args
 let C:= P.shifts j (D.zoom P n j) (D.full P n); let B:=P.atSide j D.s (d+d) (add_pos (D.pos j) (D.pos j)) z
 have he':∀ v:ℕ,w=v → ∀ p:0<v, ∃ u: P.Card j n v,P.voxTest j n u.val=C ∧ B=P.atSide j n v p u:=by
   intro i p hi; have h:i=(Λ).R.L.val^(n-D.s)*(d+d):=p.symm.trans hz
   clear p; subst i -- perhaps not rhs bust
   exact ⟨x',hp.symm,P.upper_tab j D.s (d+d) (add_pos (D.pos j) (D.pos j)) z n e⟩
 exact he' w rfl _
lemma throughMark (R:P.Register) : (full P D n)∈ keep Λ P.width n (κ) true (scenery P D 0):=by
  unfold full
  generalize h:n-D.s=i
  have he (i:ℕ) : P.conveying D.s i D.F∈ keep Λ P.width (D.s+i) (κ) true (scenery P D 0):=by
    induction i with
    | zero=> exact ticket P D
    | succ i ih=>
      rw [show P.conveying D.s (i+1) D.F=P.promote (D.s+i) R (P.conveying D.s i D.F) from Subtype.ext (P.promotes_to (D.s+i) R (P.conveying D.s i D.F)).symm,← Nat.add_assoc]; exact P.promotes_local (D.s+i) R true _ ih
  exact (show D.s+i=n from (by omega)) ▸ he i
lemma zoom_bell : bell (timeMesh P.par) n (D.zoom P n j)= D.realWidth P j:= congrArg (fun r:Γ=> (r:ℝ)) (D.marks_equal P j n e)
omit e
lemma fullColor : full P D n∈ enclave P.calibration:= P.refine_keeps _ _ D.realM _
lemma zoomP : 0 < D.zoom P n j := mul_pos (pow_pos (Λ).R.L.property _) (D.pos j)
-- size inscription at arbitrary shifts COMPOSE below
end Apron
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
