import YM.CF.BPress.Vesper.Ore
import YM.CF.BPress.Lily.Vases
/-! VolumeB-phase. Optional and clamped Force, leave weights outside. Scale at given complex amount (argument for covariance fixes real strength). -/
set_option autoImplicit false
set_option maxHeartbeats 80000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.BPress.Vesper
open Function Filter NormedSpace MeasureTheory Finset Lattice Branch Push.AbsoluteSums Gas Palmer Fock Pastry Pine Pf Leaves EdgeD
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators InnerProductSpace Classical
attribute [local instance] opCStarAlgebra
open Cube Lat SU Spin Spin.Paint Chalk Lily Skye Scree Lute Branch Tenant DoughBag Tulip Dial -- verify shadow
variable {N:Side}
abbrev WantJ(N:Side):= Σ i:Site N, ↥(team i)
abbrev jBand (p:WantJ N):=(Course.string p.2.val).reverse
lemma tune_len (p:WantJ N): (jBand p).length=p.2.val.val.card:=by simp [jBand, Course.string]
def aug (N:Side) : Leaves (Single N) (WantJ N) where
 band:= jBand
 e i:=by rw [tune_len,Nat.even_iff]; exact (mem_filter.mp i.2.property).2
 n i:=by unfold jBand Course.string; exact List.nodup_reverse.mpr (sort_nodup ..)
 rule:= mix (silence _) Sigma.fst
variable (K T: Paint (More N))(Z:Site N→ℂ)(p:MatPlan K)(b:Support N)
def optionW(x:WantJ N):ℂ:= Z x.1 * Lily.quote x.1 (K (node x.1)) (T (node x.1)) (selectP x.1 b) x.2.val
def oceans: PanelA N:= ⟨fun x=>1+ Z x • cardP K T b x,fun x=> Sector.one.add ((joker_even x _ _ _).scale _)⟩
local notation "E_" => sneak (coupling K) (Paint.skew _ p)
include p
lemma coastal(i:WantJ N): (E_).cook (cake (aug N) (optionW K T Z b) i)=(optionW K T Z b i) • Lily.word i.1 (K (node i.1)) i.2.val:=by
 rw [coherence _ _ K rfl,cake,sow]; rfl
omit p
abbrev ncake (x:WantJ N): Dough (Single N):= cake (aug N) (optionW K T Z b) x
abbrev kitcake(x:Site N): Dough (Single N):=∑ g:↥(team x), ncake K T Z b ⟨x,g⟩
lemma kit_snow : box (silence _) (kitcake K T Z b)=(aug N).snow (optionW K T Z b):= release (silence _) _ Sigma.fst (ncake K T Z b) (fun i=>(trib_sigma (ncake K T Z b) i).symm) -- tune
include p
lemma coast_value(i:Site N): Z i • cardP K T b i=(E_).cook (kitcake K T Z b i):=by
 rw [kitcake,map_sum]; change _ = ∑ g:↥(team i), (E_).cook (cake (aug N) (optionW K T Z b) ⟨i,g⟩); simp_rw [coastal K T Z p b]; unfold Lily.cardP Lily.joker; rw [smul_sum]; simp only [optionW, mul_smul]; exact (sum_attach ..).symm
lemma coastal_sum(i:Site N): (oceans K T Z b).val i=(E_).cook (1+kitcake K T Z b i):=by rw [map_add,map_one]; exact congrArg (1+·) (coast_value K T Z p b i) -- tune
lemma shore_full(A:Support N): tomes A (oceans K T Z b)= (E_).cook (∏ i∈A,(1+kitcake K T Z b i)):=by
 induction A using Finset.induction_on with | empty=>simp|@insert i A l ih=> rw [prod_insert l,map_mul,brick _ _ i l, coastal_sum K T Z p b, ih]
lemma vacation : tomes univ (oceans K T Z b)= (E_).cook ((aug N).snow (optionW K T Z b)):=by rw [←kit_snow,wall,shore_full K T Z p b]
end YM.CF.BPress.Vesper
