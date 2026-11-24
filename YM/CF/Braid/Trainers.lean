import YM.CF.Braid.Curl
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Braid
open Function Lattice RG Exterior Bloch Laurent Filter Finset Asymptotics Stationary
open Matrix (transpose mulVec of)
open scoped Matrix Topology ContDiff BigOperators
open Work.F06
variable {α ξ:Type}[Fintype α][DecidableEq α][Fintype ξ] {σ τ A C : ℝ}{M N r t:ℕ}
-- affine momentum shear
abbrev X (E:Type) [AddCommGroup E](t:ℕ):= Keys t → E
def twist{E:Type}[AddCommGroup E](v:Axis→ E) (x:X E t):=missing x+v
def glide {E:Type}[AddCommGroup E](v:Axis→ E)(x:X E (t+1)):=extendVar (clipVars x) (twist v x)
lemma glad {E:Type}[AddCommGroup E](v:Axis→ E)(x:X E (t+1)): glide v (glide v x)=x:=by
 unfold glide; rw [extends_drop]; apply Eq.trans _ (extends_back x); congr 1; unfold twist; rw [miss_extend,show missing x=_ from (congr_arg missing (extends_back x)).symm,miss_extend]; abel
lemma tips {E:Type}[AddCommGroup E](v:Axis→ E)(x:X E (t+1)): twist v (glide v x)=x ∘ stick t := funext fun i=>congr_fun (glad v x) (0,i)
lemma axes_add (a b:Corn α):axes (a+b)=axes a+axes b:=by ext1; simp [axes]
lemma glided (v:Axis→ℝ)(x:Corn (Keys (t+1))):glide (axes v) (axes x)=axes (glide v x):=by
 ext1 ⟨i,j⟩; induction i using Fin.cases <;> simp only [axes,glide,extends_zero,extends_other,clipVars]; exact congr_fun (show twist (axes v) (axes x)=axes (twist v x) from by unfold twist; rw [miss_phase,axes_add]) _
def work (v:Axis→ℝ)(f:SheetLeg (Keys (t+1)) ξ r):SheetLeg (Keys (t+1)) ξ r:=f ∘ glide (axes v)
lemma workout(v:Axis→ℝ)(f:SheetLeg (Keys (t+1)) ξ r): work v (work v f)=f:=funext fun p=>congr_fun (rfl: f=f) p ▸ congr_arg f (glad ..)
lemma money(v:Axis→ℝ)(f:SheetLeg (Keys (t+1)) ξ (r+1)): cob r (projected (stick t)) (work v f)= work v (cob r (twist (axes v)) f):=by ext1; funext a b; simp only [work, Function.comp_apply,cob,tips]; rfl
lemma rake {f:SheetLeg (Keys (t+1)) ξ r}{U:Corn (Keys (t+1))→Submodule ℂ (ξ→ℂ)}(v:Axis→ℝ)(h:Uniforms _ _ (stick t) U)(p:wall U f): wall U (work v f):=by
 intro i a; have he:U i=U (glide v i):=h _ _ (fun j hj=>by
    rcases j with ⟨j,b⟩; revert hj; induction j using Fin.cases
    · exact fun hn=> False.elim (hn ⟨b,rfl⟩)
    intro _; simp only [glide,extends_other,clipVars]); rw [he, work,Function.comp_apply,glided]; exact p _ a
lemma jetP(f:SheetLeg (Keys (t+1)) ξ r)(h:JetWall N f):JetWall N (work 0 f):=by
 rw [show work 0 f=swab f from funext fun x=> congr_arg f (congr_arg (extendVar (clipVars x)) (show twist (axes 0) x=missing x from by simp [twist,show axes (0:Axis→ℝ)=0 from funext fun i=>by simp [axes]]))]; exact swab_jets h
private def chop (x:Shift (Keys (t+1)))(a:Axis):=x (0,a)
private def grab (x:Shift (Keys (t+1))):Shift (Keys (t+1)):= x -extendVar (0:X ℤ t) (chop x)-fun z=> chop x z.2
private lemma gets (x:Shift (Keys (t+1)))(v:Axis→ℝ)(p:Phase (Keys (t+1))): mode (glide (axes v) p) x=mode p (grab x)*mode (axes v) (chop x):=by
 rw [mode,mode,mode,←Complex.exp_add,← mul_add]; congr 2
 simp_rw [Fintype.sum_prod_type]; conv_lhs=> rw [Fin.sum_univ_succ]
 conv_rhs => lhs; rw [Fin.sum_univ_succ]
 unfold glide twist missing grab chop; simp only [extends_zero,extends_other,clipVars,Pi.add_apply,Pi.sub_apply,Pi.zero_apply,Pi.neg_apply,Finset.sum_apply,Int.cast_sub,Int.cast_zero,sub_self,zero_sub,sub_zero]
 simp_rw [Function.comp_apply,strand,Embedding.coeFn_mk]
 simp_rw [add_mul,neg_mul,sum_mul,Finset.sum_add_distrib,Finset.sum_neg_distrib]; rw [sum_comm,Fin.sum_univ_succ]; simp only [Int.cast_neg,mul_neg,mul_sub,sum_sub_distrib,sum_neg_distrib]; abel
lemma nams (x:Shift α)(i:α): (x i).natAbs ≤ size x:= Finset.single_le_sum (f:=fun i=>(x i).natAbs) (fun _ _=>Nat.zero_le _) (Finset.mem_univ i)
lemma grab_f (x:Shift (Keys (t+1))): size (grab x) ≤ Fintype.card (Keys (t+1))*(2*size x):=by unfold Laurent.size; refine (sum_le_sum (g:=fun _=>2*size x) fun i _=>?_).trans_eq (by rw [sum_const,card_univ]; rfl); rcases i with ⟨i,a⟩; induction i using Fin.cases with
 | zero=> simp only [grab, chop, Pi.sub_apply, extends_zero, sub_self,zero_sub, Int.natAbs_neg]; exact (nams x _).trans (by omega)
 | succ i=>
    simp only [grab, chop, Pi.sub_apply, extends_other,Pi.zero_apply, sub_zero]; have h:=Int.natAbs_add_le (x (Fin.succ i,a)) (-(x (0,a))); simp only [Int.natAbs_neg] at h; refine le_trans ?_ (le_trans h ?_); · rw [sub_eq_add_neg]
    linarith [nams x (Fin.succ i,a),nams x (0,a)]
lemma toss{f:SheetLeg (Keys (t+1)) ξ r}(v:Axis→ℝ)(h:Board M A f):Board (Fintype.card (Keys (t+1))*(2*M)) A (work v f):=by
 intro i x; apply Pond.travel (glide (axes v)) (h i x); intro y he; simp_rw [gets]; exact ((Pond.modes ..).mono (mode_real _ _ (axes_real v)).le ((grab_f y).trans (by gcongr))) -- tune
end YM.CF.Braid
