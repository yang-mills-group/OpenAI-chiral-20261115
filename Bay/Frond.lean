import Bay.Porch
import YM.SU5.Interaction.Source.Reduction
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 3000
set_option synthInstance.maxSize 24000
set_option quotPrecheck false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Bay
open Function Filter Topology NormedSpace Lattice Wilson Fock Pastry Scree Sault Sour Stax Skye Jet Scroll Finset Palot Cadre Vow
open RG MeasureTheory Rue
open Metric Drapes Tulip Lat Branch Cube Tenant
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Topology Classical
attribute [local instance] opCStarAlgebra
open Rush SU Tap Levier Thera Oath Font Spire Dial Rill
open Kennel Swell


open Buffered (AtSupport covariant toMark modesIn)
open scoped YM.CF.Buffered
open StressExchange

section
variable {I:Type*} [LinearOrder I][Fintype I]
@[fun_prop] lemma preJ_cont (A:Op I): Continuous (preJ A):=by
 unfold preJ; fun_prop
lemma cork_dg (V:Op I): ‖dg V‖ ≤ cork V:=by
 have h(i:I): ‖put i‖≤1:=by have ht:=Pastry.tag_size ({i}:Finset I);rw [Pastry.poke,Pastry.Poly.tag_once] at ht;exact ht
 refine (norm_sum_le ..).trans (sum_le_sum fun i _=> (norm_sum_le ..).trans (sum_le_sum fun j _=>?_))
 rw [norm_smul];exact mul_le_of_le_one_right (norm_nonneg _) ((norm_mul_le ..).trans (mul_le_one₀ (h i) (norm_nonneg _) (by unfold takeF;rw[norm_star];exact h j)))
lemma cork_cut (V:Op I)(S:Finset I): cork (cutM S*V)≤cork V ∧ cork (V*cutM S)≤cork V:= by
 constructor <;> refine sum_le_sum fun i _=>sum_le_sum fun j _=>?_
 · rw [cutM,Matrix.diagonal_mul];split <;> simp
 rw [cutM, Matrix.mul_diagonal];split <;> simp
lemma cork_pre (S:Finset I)(V:Op I): ‖preJ (cutM S) V‖≤2*cork V:=by
 rw [two_mul]
 refine (norm_add_le ..).trans (add_le_add ?_ ?_)
 · rw[norm_smul,norm_one,mul_one];exact (cork_tc _).trans (cork_cut V S).1
 rw [← dim_cut];exact (cork_dg _).trans ((cork_cut _ _).2.trans (cork_cut _ _).1)

lemma dgLives {V:Op I}{S:Finset I} (p:sparHere V S): Sector S false (dg V):=by
 have H:∀ (G:Finset I)(f:I→ FC I), (∀ i,Sector S false (f i)) → Sector S false (∑i∈G,f i):=by
   intro G;induction G using Finset.induction_on with
   | empty=> intro f _;rw[sum_empty];exact Sector.zero _
   | @insert i G g ih=>intro f q;rw[sum_insert g];exact Sector.add (q i) (ih f q)
 refine H _ _ (fun i=>H _ _ (fun j=>?_));by_cases l:V i j=0
 · rw [l,zero_smul];exact Sector.zero _
 exact ((Sector.up _ (p i j l).1).mul (Sector.down _ (p i j l).2)).scale _
lemma minus_sec {A:FC I}{S:Finset I}(p: Sector S false A):Sector S false (-A):=by simpa using p.scale (-1)
lemma prejZero (A:Op I): preJ A 0=0:=by simp [preJ,dg,dyad]
lemma preMove (C : UNI I) (A V:Op I) :
 twist (quantU C) (preJ A V)=preJ (twist C A) (twist C V):=by
 rw [preJ,preJ,map_add,twist_scalar,map_one,dg_cov,map_mul,map_sub,map_one,map_mul,←map_mul,trace_twist]
end

abbrev Stencil(N:Side):=Pane N → FC (Single N)
abbrev footprint (N:Side):=Sa N
variable {N:Side}
local notation "IΩ" => Single N
structure Fits (S:footprint N)(c:ℝ)(f:Stencil N):Prop where
  basis: AtSupport false S (toMark f)
  paid: covariant (toMark f)
  purse(V):‖f V‖≤ c

namespace Fits
variable {S:footprint N} {c d:ℝ}{f g:Stencil N}
lemma enlarge(p:Fits S c f){T:footprint N}(r:S⊆T): Fits T c f:=⟨p.basis.mono r,p.paid,p.purse⟩
lemma width(p:Fits S c f)(e:c≤d):Fits S d f:=⟨p.basis,p.paid,fun x=>(p.purse x).trans e⟩
lemma plus(p:Fits S c f)(u:Fits S d g): Fits S (c+d) (f+g):=by
 refine ⟨p.basis.addM u.basis,fun t V=> ?_, fun V=>(norm_add_le ..).trans (add_le_add (p.purse V) (u.purse V))⟩
 exact (congrArg₂ (α:=FC IΩ) (β:=FC IΩ) (·+·) (p.paid t V) (u.paid t V)).trans (map_add _ _ _).symm
lemma scalar(p:Fits S c f)(x:ℂ):Fits S (‖x‖*c) (x • f):= by
 refine ⟨p.basis.smulM x,fun t V=> ?_, fun V=>(norm_smul x (f V)).le.trans (mul_le_mul_of_nonneg_left (p.purse V) (norm_nonneg _))⟩

 exact (congrArg (fun a:FC IΩ=>x • a) (p.paid t V)).trans (twist_scalar ..).symm

lemma subR(p:Fits S c f)(u:Fits S d g): Fits S (c+d) (f-g):= by simpa [sub_eq_add_neg] using p.plus (u.scalar (-1))
lemma zeroR : Fits S 0 0:=⟨AtSupport.zeroM,fun _ _=>(map_zero _).symm,fun _=>norm_zero.le⟩

lemma fin {ι:Type*}(U:Finset ι)(f:ι→Stencil N)(a:ι→ℝ)(h:∀i∈U,Fits S (a i) (f i)):Fits S (∑i∈U,a i) (∑i∈U,f i):=by
 induction U using Finset.induction_on with
 | empty=>rw [sum_empty,sum_empty];exact zeroR
 | @insert i U g ih=>rw [sum_insert g,sum_insert g];exact (h i (mem_insert_self ..)).plus (ih fun j h'=>h _ (mem_insert_of_mem h'))
end Fits

def emMark (V:Pane N→Op IΩ):Stencil N:=fun x=>preJ (tickA N) (V x)
def glint (V:Pane N→Op IΩ):Stencil N:=fun x=>Matrix.trace (V x) • 1
variable {V:Pane N→Op (Single N)}{p:BudgetPoint}{k:ℕ}{o:Seat N}{c d:ℝ}
abbrev areaMark (p:BudgetPoint)(o:Seat N):=roost (12+p.B) o
theorem em_fit (g:Awning V p o k c d)(h:k≤p.B):Fits (areaMark p o) (2*c) (emMark V):=by
 let f:=emMark V; let S:=areaMark p o
 have u(x):‖f x‖ ≤2*c:=by unfold f emMark; rw[touchP]; exact (cork_pre _ _).trans (mul_le_mul_of_nonneg_left (g.shadeU _) (by norm_num))
 refine ⟨AtSupport.fromEval _ ⟨(preJ_cont _).measurable.comp g.meas,_,u⟩
      (fun _ _ k=>congrArg (preJ (tickA N)) (g.dep _ _ k)) (fun x=>?_), ?_,u⟩
 · unfold emMark; rw[touchP]; exact inSector _ _ _ (spar_cut (g.light _) (Buffered.modes_monotone (roost_expand (h.trans (Nat.le_add_left ..)))))
 intro t x
 change preJ (tickA N) (V (Lattice.gauge t x.1))=twist _ (preJ _ _)
 rw[preMove,Cascade.tick_g, g.fixed]

theorem glint_fit (g:Awning V p o k c d):Fits (areaMark p o) c (glint V):=by
 have u(x):‖glint V x‖ ≤ c:=by rw [glint,norm_smul,norm_one,mul_one];exact (cork_tc _).trans (g.shadeU _)
 have hp:Continuous (fun x:Op IΩ=> Matrix.trace x • (1:FC IΩ)):=by fun_prop
 refine ⟨AtSupport.fromEval _ ⟨hp.measurable.comp g.meas,_,u⟩
      (fun _ _ k=>congrArg (fun x:Op IΩ=> Matrix.trace x • (1:FC IΩ)) (g.dep _ _ k))
      (fun _=> Reed.Fine.one.scale _), ?_, u⟩
 intro t x
 change glint V (Lattice.gauge t x.1)=twist _ (glint V x.1)
 unfold glint; rw[twist_scalar,map_one,g.fixed,trace_twist]

end YM.CF.Bay

#print axioms YM.CF.Bay.em_fit
