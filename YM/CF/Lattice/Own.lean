import YM.CF.Lattice.FrameFee

/-! Exponential tariffs for the raw state derivatives-in-distance at base. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.Tenant
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Topology
open Finset Function Fock Filter NormedSpace SU Lat Lattice Branch Cube Tour Enters
attribute [local instance] opCStarAlgebra
abbrev IndexK := Σ N:Side, Site N
def systemK : Tour IndexK where
  Y := fun z => Site (More z.1)
  I := fun z=> Model z.1
  D := fun z=> Own z.1
  G := fun z=> Geometry z.1
  yt z := inferInstance
  ys z := inferInstance
  it z := inferInstance
  is z := inferInstance
  ine z := inferInstance
  dt z := inferInstance
  stageK z := slotK z.1
abbrev weave : systemK.ChartW := fun z=> sigK z.1
abbrev Hon (s t : systemK.ChartW) (f : systemK.MapW) := Enters systemK s t f
def anchor (z : IndexK) (x : Own z.1) := frame matter (rough _ x) z.2
abbrev Kmat : systemK.MapW := fun z (x:Own z.1) => (anchor z x).H
abbrev Pmat : systemK.MapW := fun z (x:Own z.1) => projector (Kmat z x)
abbrev pairF (j : Bool) : systemK.MapW := fun z x=> snow z.1 x j
abbrev VR (z : IndexK) := Model z.1
lemma amp : ample systemK := ⟨quota,by linarith [quota_bound],fun z=>ample_slots z.1⟩
lemma launchC (i : Bool) : Enters systemK weave (partner weave) (pairF i) := make 1 (fee 1 1 0) zero_lt_one fun z=> C_fee 1 zero_le_one i z.1
lemma launchH : Hon weave weave Kmat := by
  let T : Axis→systemK.MapW := fun i z (x:Own z.1)=> (anchor z x).T i
  have he i : Hon weave weave (T i) := make 1 (fee 1 2 2) zero_lt_one fun z=> shift_fee z.2 1 zero_le_one i
  let X : Axis→systemK.MapW := fun i z x=> (anchor z x).gamma i
  let C : systemK.MapW := fun z x=> (anchor z x).chir
  let D : Axis→systemK.MapW := fun i z x=> (anchor z x).inc i
  have hc : Hon weave weave C := make 1 _ zero_lt_one fun z=> static_fee 1 z.1 grading zero_le_one
  have h i : Hon weave weave (X i) := make 1 _ zero_lt_one fun z=> static_fee 1 z.1 (gammaOp i) zero_le_one
  have ht i : Hon weave weave (D i) := (((identity weave).sub (((he i).plus (he i).starL).scaleR (1/2))).plus ((h i).join (((he i).sub (he i).starL).scaleR (1/2))))
  let f : systemK.MapW := fun z x=> ∑ i:Axis,D i z x
  have hg : Hon weave weave f := by
    simp only [f,Axis, Fin.sum_univ_succ,Finset.univ_eq_empty,Finset.sum_empty,add_zero]; exact (ht _).plus ((ht _).plus ((ht _).plus (ht _)))
  exact hc.join ((identity weave).neg.plus hg)
lemma attends z x : Safe (Kmat z x) := band matter (rough z.1 x) z.2 (show _ from (Subtype.property (show Own z.1 from x)).paid) -- tune
lemma unit_each (j : Bool) z x : pairF j z x∈unitary _ := C_unit _ ((Subtype.property (show Own z.1 from x)).unit j)
lemma tight (j : Bool) z x : ‖stage (Pmat z x) (pairF j z x)-pairF j z x‖ ≤ 1/3 := by
  rw [stage_gap (attends z x).projection];
  let t : Own z.1 := x; exact compressible.choose_spec.2 _ _ _ _ t.property.paid (t.property.unit j) (t.property.snug j)
-- relate names to assemblies
abbrev weighX : systemK.MapW := fun z x=> body (Pmat z x) (pairF false z x)*star (body (Pmat z x) (pairF false z x))+(1-Pmat z x) -- uses shrinkV
lemma weighR z x : ‖weighX z x-1‖≤7/9 :=
  -- linear order from z
  sat_gap (n:=Model z.1) (P:=Pmat z x) (attends z x).projection ⟨_,unit_each false z x⟩ (tight false z x)
abbrev tollX : systemK.MapW := fun z x=> pencil (weighX z x-1)
abbrev beamX : systemK.MapW := fun z x=> relay (Pmat z x) (pairF false z x) (pairF true z x)
abbrev billX : systemK.MapW := fun z x=> pencil (beamX z x-1)
lemma billR z x : ‖beamX z x-1‖≤1/2 := by
  have ht := inv_close_le (A:=stage _ _) (⟨_,unit_each false z x⟩ : UNI (systemK.I z)) (tight false z x)
  have he := relay_gap (attends z x).projection ht.1 ht.2 (C:=pairF true z x)
  have hp : ‖pairF true z x-pairF false z x‖≤1/4 := by rw [norm_sub_rev]; exact (Subtype.property (show Own z.1 from x)).gap
  exact he.trans (by linarith)
lemma honored : Hon weave weave tollX := (site amp launchH attends).stageLn (launchC _) (fun z x=>(attends z x).projection) weighR amp
lemma accorded : Hon weave weave billX := (site amp launchH attends).relayLn (launchC _) (launchC _) (tight _) (unit_each _) billR amp
lemma wallet z x : (tollX z x).trace = invoice (weighX z x-1) := (tally_log ((weighR z x).trans_lt (by norm_num))).symm
lemma bille z x : (billX z x).trace = invoice (beamX z x-1) := (tally_log ((billR z x).trans_lt (by norm_num))).symm

def paddle (z : IndexK) (i : ℕ) (x:systemK.D z) := decay (Kmat z x) i
abbrev incomeD (z : IndexK) (i : ℕ) (x:systemK.D z) := Kcc (paddle z i x) (reserve (Pmat z x) (pairF false z x))
abbrev incomeA (z : IndexK) (i : ℕ) (x:systemK.D z) := Kcg (paddle z i x) (driftB (Pmat z x) (pairF false z x))
abbrev incomeW (z : IndexK) (i : ℕ) (x:systemK.D z) := Kgg (paddle z i x) (weldB (Pmat z x) (pairF false z x))
abbrev incomes (a q r : ℝ) := ∀ z n, RootedK (partner weave z) (weave z) a (r*q^n) (incomeD z n) ∧ RootedK (partner weave z) (partner weave z) a (r*q^n) (incomeA z n) ∧ RootedK (weave z) (partner weave z) a (r*q^n) (incomeW z n)
lemma incomes_ok : ∃ a q r : ℝ, 0<a ∧ 0<q ∧ q<1 ∧ 0<r ∧ incomes a q r := tendX amp launchH (launchC _) attends (tight _) (unit_each _)
end YM.CF.Tenant
