import YM.SU5.Exchange.Pipe.Mill
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 24000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Swell
open Function Filter Topology NormedSpace Lattice Wilson Fock Pastry Scree Sault Sour Stax Skye Jet NormedSpace Scroll Finset Palot Cadre Vow
open RG Mew Rive Nor Hake MeasureTheory Bake Rue Salt
open Metric Drapes Tulip Lat Branch Cube Tenant
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Topology Classical
attribute [local instance] opCStarAlgebra
open SU Prism Tap Levier Thera Moto Oath Font Haro
variable {N:Side}{X Y:SOp N}{o:Seat N}{a b c d v:ℝ}
-- centered on matter, convolving independent axes. Asymmetric corner BEFORE projection.
abbrev moveSite(x:Site N)(l:Axis)(j:ℕ): Site N:=x+j • step l
abbrev stripSum {F:Type*}[AddCommMonoid F](G: Site N→ F)(l:Axis)(m:ℕ)(x:Site N):F:=∑ i∈ range (2*m),G (moveSite (x - m • step l) l (i+1))
def squareSum {F:Type*}[AddCommMonoid F] (G:Site N→F)(m:ℕ): List Axis→ Site N→ F
| [],x=>G x
| i::l,x=> stripSum (squareSum G m l) i m x
lemma squareMap {F F':Type*}[AddCommMonoid F][AddCommMonoid F'](g:F→+F')(G:Site N→F)(m:ℕ)(L:List Axis)(x:Site N): g (squareSum G m L x)=squareSum (fun x=>g (G x)) m L x:=by
 induction L generalizing x with
 |nil=> rfl
 |cons i L h=> unfold squareSum stripSum; rw [map_sum]; exact sum_congr rfl fun i _=> h _ -- tune rw both?
lemma square_sum {F I:Type*}[AddCommMonoid F](g:I→ Site N→F)(T:Finset I)(m:ℕ)(L:List Axis)(x:Site N): squareSum (fun x=>∑ i∈ T,g i x) m L x=∑ i∈ T,squareSum (g i) m L x:=by
 induction L generalizing x with
 |nil=>rfl
 |cons i L h=> simp_rw [squareSum,stripSum,h]; rw [sum_comm]
lemma square_move {F:Type*}[AddCommMonoid F](G:Site N→ F)(z:Site N)(m:ℕ)(L:List Axis)(x:Site N): squareSum (fun x=> G (x+z)) m L x=squareSum G m L (x+z):=by
 induction L generalizing x with
 |nil=> rfl
 |cons i l h=> unfold squareSum stripSum; simp_rw [h]; apply sum_congr rfl; intro j _; congr 1; unfold moveSite; abel
lemma strip_exchange {F:Type*}[AddCommMonoid F](G:Site N→ F)(i j:Axis)(m:ℕ)(x:Site N): stripSum (stripSum G j m) i m x=stripSum (stripSum G i m) j m x:=by
 unfold stripSum; rw [sum_comm]; refine sum_congr rfl fun a _=>sum_congr rfl fun b _=>?_ ; congr 1; unfold moveSite; abel
lemma square_peel {F:Type*}[AddCommMonoid F](G:Site N→ F)(i:Axis)(m:ℕ)(L:List Axis)(x:Site N)(p:i∈L): squareSum G m L x=stripSum (squareSum G m (L.erase i)) i m x:=by
 induction L generalizing x with
 |nil=>contradiction
 |cons j l h=>
    by_cases t:j=i; · subst j; rw [List.erase_cons_head,squareSum]
    rw [List.erase_cons_tail (show (j == i) ≠ true by simp [t]),squareSum]; unfold stripSum -- RHS now maybe doesn't unfold list recursion?
    have hp := (fun (x:Site N)=> h x ((List.mem_cons.mp p).resolve_left (Ne.symm t))); -- syntax position?
    simp_rw [hp]; exact strip_exchange _ j i m x
lemma square_sub {F:Type*}[AddCommGroup F](U V:Site N→ F)(m:ℕ)(L:List Axis)(x:Site N): squareSum (fun x=>U x - V x) m L x=squareSum U m L x-squareSum V m L x:=by
 induction L generalizing x with |nil=>rfl|cons i l h=>unfold squareSum stripSum; simp_rw [h,sum_sub_distrib]
lemma strip_tel {F:Type*}[AddCommGroup F](G:Site N→ F)(x:Site N)(l:Axis)(m:ℕ): stripSum (fun x=>G x-G (x-step l)) l m x= G (x+m • step l)-G (x-m • step l):=by
 let U:=x-m • step l; let f(i):=G (moveSite U l i)
 have hx:(∑ i∈range (2*m),(f (i+1)-f i))=f (2*m)-f 0:= sum_range_sub ..
 have he(y:Site N)(n:ℕ): moveSite y l (n+1)-step l=moveSite y l n:=by unfold moveSite; rw [add_smul,one_smul]; abel
 unfold stripSum; simp_rw [he]; rw [show (∑ i∈ range (2*m), _)= _ from hx]; unfold f moveSite U; rw [two_mul, add_smul, show x-m • step l+(m • step l+m • step l) = (x+m • step l:Site N) from ?_]; simp; abel -- syntax
local notation "Axes"=> List.ofFn (id: Axis→Axis)
abbrev windmill(x:Site N)(m:ℕ):Op (Single N):= squareSum millQ m (List.ofFn (id:Axis→Axis)) x
abbrev spur(O:Site N→ SOp N)(z:Site N)(a:Axis)(m:ℕ)(V:Chin N):= squareSum (fun i=> chute O i a V) m ((Axes).erase a) z
lemma millEquation(O:Site N → SOp N)(V:Chin N)(p: (∑ i:Site N,O i V)=0)(x:Site N)(m:ℕ) : squareSum (fun i=>O i V) m Axes x=∑ i:Axis,(spur O (moveSite x i m) i m V-spur O (x-m • step i) i m V):=by
 simp_rw [pipeEquation O V p]; rw [square_sum]; refine sum_congr rfl fun i _=>?_ ; let T:= Axes; have hp:i∈Axes:=by fin_cases i <;> simp
 rw [square_peel _ i m Axes x hp]
 let G:=squareSum (fun x=> chute O x i V) m (T.erase i); have hu(x:Site N): squareSum (fun x=> chute O x i V - chute O (x-step i) i V) m (T.erase i) x= G x-G (x-step i):=by
    rw [square_sub]; congr 1
    simp_rw [sub_eq_add_neg (b:=step i)]; exact square_move (fun x=> chute O x i V) (-(step i):Site N) m _ _
 rw [funext hu]; exact strip_tel G x i m

-- budgets for these RAW unmasked square-stencils, with exponential kernels. 
lemma leap_strip (x:Site N)(l:Axis)(m:ℕ)(k:ℕ)(p:k<2*m): separation x (moveSite (x-m • step l) l (k+1))≤3*m:=by
 have he(x:Site N)(k:ℕ):separation x (moveSite x l k) ≤ k:=by
    induction k with
    |zero=>simpa [moveSite] using Nat.zero_le (separation x x) -- may rewrite
    |succ k h=> exact (separation_triangle x (moveSite x l k) _).trans (Nat.add_le_add h (show separation _ _ ≤ 1 from (by rw [show moveSite x l (k+1) =moveSite x l k + step l from (by unfold moveSite; rw [add_smul,one_smul]; abel)]; exact Font.small (moveSite x l k) (posDir l))))
 let y:=x-m • step l; have hp:separation x y ≤ m:=by rw [separation_comm]; nth_rw 1 [show x=moveSite y l m from (by unfold moveSite y; abel)]; exact he y m
 exact (separation_triangle x y _).trans ((Nat.add_le_add hp (he y (k+1))).trans (by omega))
abbrev stripW(a:ℝ)(m:ℕ):ℝ:=(2*m:ℕ) * Real.exp (a * (4*(6*(m:ℝ))+1)) -- Int inference
lemma square_sells (G: Site N→ SOp N)(g:0 ≤ a)(p:∀ x:Site N,Soak (node x) (G x) a v d) (x:Site N)(m:ℕ)(L:List Axis): Soak (node x) (fun U=> squareSum (fun i=> G i U) m L x) a ((stripW a m)^L.length*v) d:=by
 induction L generalizing x with
 |nil=> rw [List.length_nil,pow_zero,one_mul]; exact p _
 |cons i L h=>
    let T:= stripW a m; let A:= T^L.length*v; let Z:=fun k=> moveSite (x-m • step i) i (k+1); let K(k:ℕ):Chin N→Op (Single N):= fun U=> squareSum (fun i=>G i U) m L (Z k)
    let V:= Real.exp (a*(4*(6*(m:ℝ))+1)); let G0:= range (2*m)
    have ht(k:ℕ)(p:k∈ G0): Soak (node x) (K k) a (V*A) d:=by
       let y:=Z k; have hp:Soak (node y) (K k) a A d:= h y; refine lift_U (soak_tr (o':=node x) hp g) (mul_le_mul_of_nonneg_right ?_ (soakCostNN hp)); apply Real.exp_le_exp.mpr; gcongr
       have he:separation y x≤ 3*m:=by rw [separation_comm]; exact leap_strip _ _ _ _ (mem_range.mp p)
       exact_mod_cast (Hove.ζdist y x|>.trans_le (le_trans (Nat.mul_le_mul_left _ he) (by omega)))
    have he: (∑ i∈G0,V*A)=stripW a m ^ (i::L).length * v:=by
       rw [sum_const, List.length_cons,pow_succ']; unfold G0; rw [card_range, nsmul_eq_mul]; change _=(T*T^L.length)*v; unfold T stripW V A; ring
    rw [←he]; exact sun_K G0 K _ ht
lemma spurSells (m:ℕ)(p:0<a)(u:0≤v): ∃ U:ℝ,0<U∧ ∀ {N:Side}(O:Site N→ SOp N), (∀ x,Soak (node x) (O x) (100*a) v d)→∀ (z:Site N)(l:Axis),Soak (node z) (spur O z l m) a U d:=by
 obtain ⟨Z,w,f⟩:=stepOwed (d:=d) p u; let X(l:Axis):= (stripW a m)^((Axes).erase l).length*Z; have hx(l:Axis):0 ≤ X l:=by unfold X stripW; positivity
 refine ⟨1+∑ l:Axis,X l, add_pos_of_pos_of_nonneg zero_lt_one (sum_nonneg fun i _=> hx i), fun {N} O e z l=> lift_U (square_sells (fun i:Site N=> chute O i l) p.le (fun i=> f O e i l) z m ((Axes).erase l)) ((single_le_sum (fun i _=>hx i) (mem_univ l)).trans (le_add_of_nonneg_left zero_le_one))⟩
lemma windmillCost(x:Site N)(m:ℕ)(p:0≤a):Soak (node x) (fun _=>windmill x m) a ((stripW a m)^(Axes).length * oneMill a) d:= square_sells (fun i _=> millQ i) p millBill x m _
end YM.CF.Swell
