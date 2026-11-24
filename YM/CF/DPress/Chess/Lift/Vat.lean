import YM.CF.DPress.Chess.Lift.Wings
import YM.CF.BPress.Test
/-! Extensible stencils.E. Lips $T$ budgets at one step. -/
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.DPress.Chess.Lift
open Function Filter Finset Lattice Bloch Laurent Next.Free Fir Rush Scroll Lat Peaks Cube Tulip Dial SU Branch Drapes Wilson Fock Fixed NormedSpace Spire Scree Skye Tap
open scoped Topology BigOperators NNReal ENNReal Kronecker Classical Matrix.Norms.L2Operator YM.CF.BPress
attribute [local instance] opCStarAlgebra
variable {N M L:Side} (G:Ratio N M)(Q:Op Slot){r j:ℕ}{i:Male}{Y:Nom N M}
section
def nodeS (S:Support (More N))(x:Ket (Single N)):Prop:= Upper (cutM (matterRegion N S)) x
abbrev Float {I:Type*}[Fintype I][DecidableEq I] (P:Op I)(x:Ket I):Prop:= acts P x=x -- remove
lemma withinW {A:Support (More N)}{x:Ket (Single N)}: nodeS A x ↔ ∀ i:Single N,node i.1.1∉ A → x.ofLp i=0:=by
 constructor
 · intro p i h; rw [show x.ofLp i=(acts _ x).ofLp i from congrArg (fun q:Ket (Single N)=> q.ofLp i) (Eq.symm p), cut_apply,if_neg (show i∉ Fixed.matterRegion N A from mt ((mem_matterRegion ..).1) h)] -- tune implicit op
 intro p; apply PiLp.ext; intro i; rw [cut_apply]; split; rfl; next t=> exact Eq.symm (p i (mt ((mem_matterRegion ..).2) t))
lemma crestQ {A:Support (More N)}{x:Ket (Single N)}(u:nodeS A x): nodeS A (acts (peak N Q) x) ∧ nodeS A (acts (pit N Q) x):= let H:=careZ Q (cutM _) (peekK Q A); ⟨Upper.acted u H.1, Upper.acted u H.2⟩
variable {Z:Type*}
local notation "X"=> patchQ G
abbrev spreadB (G:Ratio N M)(S:Support (More N))(r:ℕ):= Lattice.halo r (S.image (ratio G).embed)
lemma node_at(i:Iota G): node ((switchG G i).1.1) = touch G true i.1 := Eq.symm (Symbol.Stroke.fine i)
section
variable {I:Type*}[Fintype I][LinearOrder I]
lemma coef_x(Z:Op I)(Y:Ket I)(j:I): (acts Z Y).ofLp j= ∑ i:I, Z j i*Y.ofLp i:=rfl
lemma punch(f:I↪Single N)(x:Ket I)(i:I): (coat f x).ofLp (f i)=x.ofLp i:=by rw [←seamK,trails]
end
-- with support S coarse reading *only Column stencil at nodes*, agents from Stroke tax.
lemma line_p {S:Support (More N)} {x:Single N}(p:node x.1.1∈ S):Symbol.earnS G (X x) r ⊆ spreadB G S r:= by intro z t; unfold Symbol.earnS at t; rw [Symbol.Stroke.coarse] at t; rw [halo_spec] at t; obtain ⟨y,l,u⟩:=t; rw [mem_singleton.mp l] at u; exact halo_spec.mpr ⟨_, mem_image_of_mem _ p,u⟩
lemma phr (h: ∀ i:Male,Symbol.Stroke G (pulse G j i) r) {S:Support (More N)}{x:Ket (Single N)}(p:nodeS S x): nodeS (spreadB G S r) (shine G j i Y x):=by
 apply withinW.2; intro z v; let e:=switchG G; obtain ⟨z,rfl⟩:=e.surjective z; unfold shine; rw [show e z= e.toEmbedding z from rfl,punch,coef_x]; apply Finset.sum_eq_zero; intro y _; by_cases t:y∈ lows X; swap; · rw [basin _ _ _ t,mul_zero]
 obtain ⟨y,-,rfl⟩:= mem_map.mp t; rw [←seamK,trails]; by_cases g:node y.1.1∈S; swap; · rw [withinW.1 p y g,mul_zero]
 rw [(h i).range _ _ _ _ ,zero_mul]; intro p'; apply v; unfold spreadB; rw [show node _=touch _ _ _ from node_at G z]; exact line_p G g p'
lemma pay_x (t:∀ i:Male,Symbol.Stroke G (pulse G j i) r){X' Y:Nom N M}{S:Support (More N)}{x:Ket (Single N)}(p:nodeS S x)(e:Agrees (spreadB G S r) X'.1 Y.1) : shine G j i X' x=shine G j i Y x:=by
 unfold shine; apply congrArg; apply PiLp.ext; intro k; rw [coef_x,coef_x]; refine sum_congr rfl ?_; intro y _; by_cases h:y∈lows X; swap; · rw [basin _ _ _ h, mul_zero,mul_zero]
 obtain ⟨y,-,rfl⟩:= mem_map.mp h; rw [←seamK,trails]; by_cases g:node y.1.1∈ S; swap; · rw [withinW.1 p _ g,mul_zero,mul_zero]
 rw [(t i).read _ _ _ _ (agrees_mono e (Finset.coe_subset.mpr (line_p G g)))]
lemma shineC (p:Continuous (pulse G j i))(x:Ket (Single N)):Continuous (fun y:Nom N M=> shine G j i y x):=by
 have he:Continuous (coat (switchG G).toEmbedding):= LinearMap.continuous_of_finiteDimensional _; exact he.comp ((acts_cont.comp p).clm_apply continuous_const)
end
end YM.CF.DPress.Chess.Lift
