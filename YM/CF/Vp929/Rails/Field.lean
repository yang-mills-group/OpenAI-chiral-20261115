import YM.CF.Vp929.Rails.Aster
import YM.CF.Vp929.Rails.Plank
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
abbrev tallY (D:ℕ)(a:ℝ)(B:X'→ℝ)(C:Raid J)(S:Sc)(x:Site V)(n:ℕ) := ∑ i:X' with Palot.outC n i, ∑ y:Lo with x∈y.val,B i * joinV C (S i y) * Trees.currency D a y.val
variable {D:ℕ}{a:ℝ}{C:Raid J}{B:Finset ι→ℝ}
structure Merit (D:ℕ)(a:ℝ)(C:Raid J)(B:X'→ℝ)(L:ℕ→ℝ)(S:Sc) : Prop where
 p : 0≤S
 earn (o:Site V)(m:ℕ) : tallY D a B C S o m≤L m
namespace Merit
lemma basis {u:T→Sc}{s:Filter T}[s.NeBot]{L:ℕ→ℝ} (v:∀ i,Merit D a C B L (u i))(hp:∀ i,0<B i)(ht:∀ i,0<C i):∃ Y:Sc,MapClusterPt Y s u∧ Merit D a C B L Y:=by
 let f (i:X')(y:Lo)(j:Q'):= B i * C j * Trees.currency D a y.val; let M(i:X')(y:Lo)(j:Q'):= L 0/f i y j
 have h(s:T): u s ∈ Set.Icc (0:Sc) M:= by
   refine ⟨(v _).p,?_⟩; intro i y j; change u s i y j ≤ M i y j
   have hx:=hp i; have hy:=ht j; obtain ⟨o,g⟩:= y.prop; refine (le_div_iff₀ (mul_pos (mul_pos hx hy) (Real.exp_pos _))).2 ?_
   have he:0≤ joinV C (u s i y):= sum_nonneg fun i _=> mul_nonneg (ht i).le ((v s).p _ _ _)
   calc
    _ = B i * (C j* u s i y j) * Trees.currency D a y.val := by unfold Push.AbsoluteSums.Trees.currency; ring
    _ ≤ B i * joinV C (u s i y) * Trees.currency D a y.val:=mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (single_le_sum (fun j _=> mul_nonneg (ht j).le ((v s).p i y j)) (mem_univ j)) hx.le) (Real.exp_pos _).le
    _ ≤ ∑ y:Lo with o∈y.val, B i * joinV C (u s i y)*Trees.currency D a y.val:=single_le_sum (a:=y) (f:=fun y:Lo=> B i * joinV C (u s i y)* Trees.currency D a y.val) (fun y _=>mul_nonneg (mul_nonneg hx.le (sum_nonneg fun j _=> mul_nonneg (ht j).le ((v s).p i y j))) (Real.exp_pos _).le) (mem_filter.mpr ⟨mem_univ _,g⟩)
    _ ≤ tallY D a B C (u s) o 0:= single_le_sum (a:=i) (f:=fun i=> ∑ y:Lo with o∈y.val,B i * joinV C (u s i y) * Trees.currency D a y.val) (fun i _=>sum_nonneg fun y _=> mul_nonneg (mul_nonneg (hp i).le (sum_nonneg fun j _=> mul_nonneg (ht j).le ((v s).p i y j))) (Real.exp_pos _).le) (mem_filter.mpr ⟨mem_univ _,Nat.zero_le _⟩)
    _ ≤ _ := (v s).earn ..
 obtain ⟨Y,e,p⟩:= (isCompact_Icc (α:=Sc)).exists_mapClusterPt (Filter.le_principal_iff.mpr (show ∀ᶠ x in s, u x∈ Set.Icc (0:Sc) M from Eventually.of_forall h)); refine ⟨Y,p,e.1,fun o m=> ?_⟩
 have H:Continuous (fun Y:Sc=> tallY D a B C Y o m):= by unfold tallY joinV; fun_prop
 exact (isClosed_Iic.preimage H).mem_of_mapClusterPt p (Eventually.of_forall fun s=> (v s).earn o m)
-- Passage to simultaneous coefficient payment only on the *beam* prices. The stencil tail where a test is paid may depend on that test (price vectors are finite dimensional).
lemma converged {E:Type}[NormedAddCommGroup E][NormedSpace ℝ E] {s:Filter T}[s.NeBot]{Λ:T→Sc}{Y:Sc}{F:E→FC J}{x:E}{k:ℕ} (hc:Sc→ Raid J) (hu: Continuous hc)(p: MapClusterPt Y s Λ)(q:∀ᶠ i in s,Woody k F x (hc (Λ i))): Woody k F x (hc Y):= by
 let H:= q.exists.choose_spec; refine ⟨H.own,fun i=>⟨(H.haveP i).smooth,?_⟩⟩; exact (isClosed_Ici.preimage (Continuous.comp (continuous_apply i) hu)).mem_of_mapClusterPt p (Eventually.mono q (fun y h=>(h.haveP i).earned))
end Merit
end YM.CF.Yaw
