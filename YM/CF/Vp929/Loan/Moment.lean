import YM.CF.Vp929.Rails.Field
set_option autoImplicit false
set_option synthInstance.maxSize 20000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Yaw
open Function Filter Metric NormedSpace Finset Fock Lattice Wilson Laurent Lat Rush SU Drapes Fir Peaks Dial Paige Brace Vault Tulip Tenant Phase Broc Scroll Thera Branch Laic Cube Relation
open scoped Matrix.Norms.L2Operator Matrix Topology ContDiff MatrixOrder BigOperators InnerProductSpace Kronecker
attribute [local instance] opCStarAlgebra
open Scree Pastry Stilo Urn Palot Hake
open Scion PetalP Push.AbsoluteSums Push.AbsoluteSums.Trees RG
open scoped Classical
variable {ι J : Type}[Fintype ι][DecidableEq ι][LinearOrder J][Fintype J] {V:Side} {T:Type}
local notation "Lo"=> leaf (Site V)
local notation "X'"=> Finset ι
local notation "Q'"=> Finset J
local notation "Sc"=> X'→ Lo→Raid J

namespace Merit
variable {D:ℕ}{a:ℝ}{C:Raid J}{B:Finset ι→ℝ}
lemma radius {L:ℕ→ℝ}{T: Sc} (v:Merit D a C B L T)(hp:∀ i,0<B i)(ht:∀ i,0<C i)(i:X')(y:Lo)(j:Q'):T i y j ≤ L 0/(B i*C j*Trees.currency D a y.val):= by
 have hx:=hp i; have hy:=ht j; obtain ⟨o,g⟩:= y.prop; refine (le_div_iff₀ (mul_pos (mul_pos hx hy) (Real.exp_pos _))).2 ?_
 have he:0≤ joinV C (T i y):= sum_nonneg fun i _=> mul_nonneg (ht i).le (v.p _ _ _)
 calc
  _ = B i * (C j* T i y j) * Trees.currency D a y.val := by change T i y j*(B i*C j*_)=_; unfold Push.AbsoluteSums.Trees.currency; ring
  _ ≤ B i * joinV C (T i y) * Trees.currency D a y.val:=mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (single_le_sum (fun j _=> mul_nonneg (ht j).le (v.p i y j)) (mem_univ j)) hx.le) (Real.exp_pos _).le
  _ ≤ ∑ y:Lo with o∈y.val, B i * joinV C (T i y)*Trees.currency D a y.val:=single_le_sum (a:=y) (f:=fun y:Lo=> B i * joinV C (T i y)* Trees.currency D a y.val) (fun y _=>mul_nonneg (mul_nonneg hx.le (sum_nonneg fun j _=> mul_nonneg (ht j).le (v.p i y j))) (Real.exp_pos _).le) (mem_filter.mpr ⟨mem_univ _,g⟩)
  _ ≤ tallY D a B C T o 0:= single_le_sum (a:=i) (f:=fun i=> ∑ y:Lo with o∈y.val,B i * joinV C (T i y) * Trees.currency D a y.val) (fun i _=>sum_nonneg fun y _=> mul_nonneg (mul_nonneg (hp i).le (sum_nonneg fun j _=> mul_nonneg (ht j).le (v.p i y j))) (Real.exp_pos _).le) (mem_filter.mpr ⟨mem_univ _,Nat.zero_le _⟩)
  _ ≤ _ := v.earn ..
end Merit
variable {E:Type}[NormedAddCommGroup E][NormedSpace ℝ E]
lemma skim {X:E→ℂ}{g:ℕ}{k:ℝ}{x:E}(f:Pence g X x k):‖X x‖≤k:=by
 let h:= f.earned; refine le_trans ?_ h; convert! Finset.single_le_sum (a:=0) (s:=Finset.range (g+1)) (f:=fun i=> Jet.noble 1 i X x) (fun i _=> Jet.pos_nob zero_le_one i) (by simp); unfold Jet.noble; simp
end YM.CF.Yaw
