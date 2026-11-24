import YM.SU5.Relativistic.Chest
import YM.SU5.Relativistic.Berm
/-! # polynomial pressure aperture. Choosing meter before Pane. -/
set_option autoImplicit false
set_option synthInstance.maxSize 26000
set_option maxHeartbeats 350000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Pannier.Chancel.ScreeV.Chateau
open Function Filter NormedSpace Metric Lattice Wilson Laurent Finset Cube SU Fock Lat Spire Scroll MeasureTheory ProbabilityTheory Peaks Drapes Rush Tulip Dial Pastry
open Buffered Lifted Afterglow Tapestry Branch Tenant Skye Cliplet RG Brace Crest Crest.Sleet Crest.Sleet.UpStart Crest.Sleet.Sorcerer Satin Tower.SlabMark
open scoped Topology BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Matrix.Norms.L2Operator ComplexOrder
attribute [local instance] opCStarAlgebra
variable (a b c:ℝ)(m:ℕ)
lemma bound_heel (S:Side)(L:ℕ) : ∀ A:ℕ, heel S L (4*A) A ≤ heel S L 4 0 *(A+1)^4:=by
 intro A; unfold heel heightB; let f:=16*S.val*12; let k:= A+1
 have he:16*S.val*(12*(A+1))+L≤ (16*S.val*(12*(0+1))+L)*(A+1):= by rw [Nat.add_mul]; simp; exact le_trans (Nat.add_le_add_left (Nat.le_mul_of_pos_right _ (show 0 < A+1 by omega)) _) (Eq.le (by ring)) -- tune
 have hx: 4*A+L≤(4+L)*(A+1):=by
    rw [Nat.add_mul]; gcongr; · omega
    exact Nat.le_mul_of_pos_right _ (by omega)
 exact le_trans (Nat.mul_le_mul (Nat.mul_le_mul_left 4 he) (Nat.pow_le_pow_left (Nat.mul_le_mul_left 4 hx) 3)) (Eq.le (by ring))
lemma ankle {L:ℕ}(p:0<L)(S:Side): ∀ A:ℕ, heels S L 4 0*boxOrder 4 A≤ heels S L (4*A) A:=by
 intro A; unfold heels boxOrder; rw [←mul_inv]; apply inv_anti₀ (by exact_mod_cast (heel_pos (U:=4*A) (A:=A) (S:=S) p)); exact_mod_cast bound_heel S L A
lemma skipExp (k v:ℕ)(p:0<a)(h:k<v):∀ᶠ A:ℕ in atTop,b*boxOrder v A < a*boxOrder k A:=by
 have ht:Tendsto (fun A:ℕ=> (A:ℝ)+1) atTop atTop:= by simpa using tendsto_atTop_add_const_right atTop (1:ℝ) tendsto_natCast_atTop_atTop
 have hc:Tendsto (boxOrder (v-k)) atTop (𝓝 0):= (tendsto_inv_atTop_zero).comp ((tendsto_pow_atTop (by omega : v-k≠0)).comp ht)
 filter_upwards [(hc.const_mul b).eventually (gt_mem_nhds (by simpa using p))] with A q
 have he: boxOrder v A= boxOrder (v-k) A*boxOrder k A:=by unfold boxOrder; rw [← mul_inv,← pow_add, Nat.sub_add_cancel h.le]
 rw [he,←mul_assoc]; exact mul_lt_mul_of_pos_right q (boxOrder_p k A)
lemma boxPow (i j k:ℕ): (boxOrder i k)^j=boxOrder (i*j) k:=by unfold boxOrder; rw [inv_pow, pow_mul]
lemma boxLoam (i j:ℕ):boxOrder i j≤1:= inv_le_one_of_one_le₀ (one_le_pow₀ (by simp)) -- tune
private lemma beamF (g h:ℝ)(e:0<h): Real.exp (-2*(5+g-12* Real.log (h^2)))= Real.exp (-2*(5+g))*h^(48:ℕ):=by
 rw [show -2*(5+g-12*Real.log (h^2))=(-2*(5+g))+(48:ℝ)*Real.log h from (by rw [Real.log_pow]; push_cast; ring),Real.exp_add, ←Real.exp_log (x:=h) e,←Real.exp_nat_mul]; -- tune rw h occurrence
 congr 2; push_cast; rw [Real.log_exp]
structure Fondue (S:Side)(L μ B X:ℕ) (u V R H:ℝ): Prop where
 get : ∃ A d:ℕ,∃ (v:Cover)(e r Z Z' C η ε:ℝ), μ ≤ A ∧ B≤2*A ∧ 0<η ∧ η≤1 ∧ 0< e ∧ e ≤ 1 ∧ (η^2)⁻¹*e⁻¹ ≤ H ∧ V*η +η≤heels S L (4*A) A∧
    0<C∧0≤ Z∧ 5*(e*(C+4)*meridiem C)≤Real.exp (-2*(5+meridiem C-12*Real.log (η^2)))∧ Z'+Z≤C ∧ 0 < ε ∧ ε*C+3*Z +2*R*(ε*C+3*Z)≤e^3 ∧
    v∈ box A ∧ chipPay (damper d) v≠0 ∧ (∀ i:Axis,X+d≤ (v i).natAbs) ∧
    (∀ n: Side,∀ j:SU.Slot, ‖strum n (Seat5 A) A (Lilt v d A) j‖≤Z') ∧
     ∀ᶠ N:ℕ in atTop,∀ (M:Jill.Male),N≤ M.val.val→∀ n:Side,∀ j:SU.Slot, ‖acts (spar 4 M (1:Pane n)) (strum n (Seat5 A) A (Lilt v d A) j)- strum n (Seat5 A) A (Lilt v d A) j‖≤Z
private lemma tasty (j:ℕ)(hy:4<j) (S:Side)(L μ B k:ℕ)(p:0<L)(R V:ℝ)(e:0<R)(u:ℝ) : ∃ H, Fondue S L μ B k u V R H:=by
 -- f exponent 1 step past risk. dynamically. iteration counts after params not large-s. compile
 let s:= j*48+1; let n:= s*3+1; let d:=1+(1+(n+8));
 obtain ⟨v,x,t⟩:= opened d (by unfold d n s; omega) (k+d)
 obtain ⟨D,g,hk,hP⟩:= Crest.Sleet.Sorcerer.muster (k:=n) (show 2*(1+(n+8))+2 ≤ 2*d from (by unfold d; omega)) v
 let C:=D+D; let T:=meridiem C; let a(A):= boxOrder j A; let f(A):=boxOrder s A; let Z(A):=D*boxOrder n A
 have he:0<C:=by unfold C; linarith
 have hp: ∀ᶠ A:ℕ in atTop,V*a A+a A ≤ heels S L (4*A) A:=by
    filter_upwards [skipExp (heels S L 4 0) (V+1) 4 j (inv_pos.mpr (by exact_mod_cast (heel_pos (S:=S) (U:=4) (A:=0) p))) (hy)] with A r
    unfold a; rw [add_mul,one_mul] at r; exact le_trans r.le (ankle p S A)
 have hv : ∀ᶠ A:ℕ in atTop, 5*(f A*(C+4)*T) ≤ Real.exp (-2*(5+T-12*Real.log (a A^2))):=by
    let v:=Real.exp (-2*(5+T))
    filter_upwards [skipExp v (5*(C+4)*T) (j*48) s (Real.exp_pos _) (by unfold s; omega)] with A r
    rw [beamF T (a A) (boxOrder_p ..)]; unfold a; rw [boxPow]; exact le_trans (le_of_eq (show 5*(f A*(C+4)*T)= _ from (show _=5*(C+4)*T* f A from (by ring)))) r.le
 have hx : ∀ᶠ A in atTop, 3*Z A+2*R*(3*Z A)< f A^3:=by
    filter_upwards [skipExp 1 (3*D+2*R*(3*D)) (s*3) n zero_lt_one (by unfold n; omega)] with A r
    unfold f; rw [boxPow]; rw [one_mul] at r; unfold Z;
    calc _=(3*D+2*R*(3*D))*boxOrder n A:=by ring
         _<_:=r
 let l:= Finset.univ.sup fun i:Axis=> (v i).natAbs
 obtain ⟨A,x1,x2,x3,x4⟩:= (hp.and (hv.and (hx.and (eventually_ge_atTop (l+B+μ))))).exists
 let ε:=(f A^3-(3*Z A+2*R*(3*Z A)))/(C+2*R*C)
 have hd:0<C+2*R*C:=by positivity
 refine ⟨_,⟨A,d,v,f A,0,Z A,D,C,a A,ε,?_,?_,boxOrder_p ..,boxLoam ..,boxOrder_p ..,boxLoam ..,le_rfl,x1,he,(mul_pos g (boxOrder_p ..)).le,x2, (add_le_add_right (mul_le_of_le_one_right g.le (boxLoam n A)) _), div_pos (sub_pos.mpr x3) hd, ?_, ?_, t,fun i=>(x i).le,fun _ j=>hk _ _ _ j,(hP A).mono fun _ y M v n u=> y M v n u _⟩⟩
 · omega
 · omega
 · have he: ε*(C+2*R*C)= f A^3-(3*Z A+2*R*(3*Z A)):=div_mul_cancel₀ _ hd.ne'; nlinarith only [he]
 have he(i): (v i).natAbs ≤ l:= le_sup (f:=fun i:Axis=>(v i).natAbs) (mem_univ i); exact box_test.mpr ⟨fun i=>by have h:=he i; omega, fun i=>by have h:=he i; omega⟩
lemma taste (S:Side)(L μ B k:ℕ)(p:0<L)(R V:ℝ)(e:0<R)(u:ℝ) : ∃ H, Fondue S L μ B k u V R H:= tasty 5 (by decide) S L μ B k p R V e u
end YM.CF.Pannier.Chancel.ScreeV.Chateau
#print axioms YM.CF.Pannier.Chancel.ScreeV.Chateau.taste
