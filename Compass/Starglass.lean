import YM.CF.Hove.Cite
import YM.CF.Hove.Canon
import Compass.Match
set_option autoImplicit false
set_option maxHeartbeats 650000
set_option synthInstance.maxSize 24000
noncomputable section
namespace YM.CF.Compass
open Function Filter Metric Fir Lattice Laurent Next.Free Bloch Finset Lat Stationary Rush Cube Scroll SU Drapes Fir Peaks Dial Paige Brace Vault Fock Tulip Font Spire Nacre Ember Pec
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix Matrix.Norms.L2Operator Kronecker
attribute [local instance] opCStarAlgebra
open Tap Hake Levier Hove
-- adapt Mantel. sign.
private lemma neg_K(A:Op SpinIdx)(F:Op Slot): A⊗ₖ (-F)= -(A⊗ₖ F):=by ext; simp
private lemma humming {s:Signed}{U:UNI SpinIdx}(h:JetS s false false U)(A: Pal)(p:Binned A): twist (twoU U false) A=∑ i:Axis,petal i⊗ₖ hush (s.flip i) (spaX A (s.perm i)):=by
 conv_lhs=> rw [←p,←spa_p,map_sum,←Equiv.sum_comp s.perm]
 apply sum_congr rfl; intro i _; let F:=spaX A (s.perm i); rw [show twist _ (petal _⊗ₖ _)= twist U (petal (s.perm i)) ⊗ₖ F from ?_,pet_up h]; swap
 · have he:= Scroll.wingK U (xtra false) (petal (s.perm i)) F; change _= twist U _ ⊗ₖ twist 1 F at he; rwa [one_des] at he
 change hush _ _⊗ₖ F= petal i⊗ₖ hush _ F; cases hv:s.flip i<;>simp [neg_K,op_kron_neg]
lemma rowV {s:Signed}{U:UNI SpinIdx}(h:JetS s false false U)(A B:Pal)(p:Binned A)(q:Binned B)(t:Bool)(e:twist (twoU U false) A=hush t B)(i:Axis): hush (s.flip i) (spaX A (s.perm i))=hush t (spaX B i):=by
 rw [humming h A p,←q,←spa_p] at e
 have he(t:Bool):hush t (∑ i:Axis, petal i⊗ₖ spaX B i)=∑ i:Axis, petal i⊗ₖ hush t (spaX B i):=by cases t <;>simp [neg_K]
 rw [he] at e; exact ((spa_s i (fun j=>hush _ _)).symm.trans (congr_arg (spaX · i) e)).trans (spa_s ..)
private lemma cancelA (X:Op Slot)(h: -X=X): X=0:=by
 have ht : (2:ℝ) • X=0:=by rw [two_smul]; nth_rewrite 1 [←h]; abel
 exact (smul_eq_zero.mp ht).resolve_left (by norm_num)
abbrev stSpin {s:Signed}(hs:detX s=false) := (spinU false s) -- JetS
lemma lookD {s:Signed}(hs:detX s=false) : JetS s false false (stSpin hs):=by simpa only [hs] using spinZ false s
lemma first_s(A:Pal)(p:Binned A)(h:∀ (s:Signed)(l:detX s=false), Anchored s→ twist (twoU (stSpin l) false) A=hush (tariffX s) A): A=0:=by
 have hx(i:Axis):spaX A i=0:=by
    have hk:∀ i:Axis,∃ j:Axis,j≠i:=by decide
    obtain ⟨j,k⟩:=hk i
    let s:=Signed.mirror i *Signed.mirror j; have he:detX s=false:=by unfold s; rw [det_p,det_t,det_t]; rfl
    have hv:=rowV (lookD he) A A p p _ (h s he (allFlips _ rfl)) i; rw [taxes,tax_m,tax_m,show s.flip i=true from (by simp [s,Signed.mirror,k,Ne.symm])] at hv; exact cancelA _ hv
 rw [←p,←spa_p]; simp [hx]
lemma vector_s (D:Axis→Pal)(p:∀ i,Binned (D i))(h:∀ (s:Signed)(l:detX s=false), Anchored s→∀ i,twist (twoU (stSpin l) false) (D (s.perm i))=hush ((tariffX s).xor (s.flip i)) (D i)):∀ i,D i=0:=by
 have hx(i j:Axis)(v:i≠j):spaX (D i) j=0:=by
    have hk:∀ i j:Axis,∃ k:Axis,i≠k∧ j≠k:=by decide
    obtain ⟨k,w,t⟩:=hk i j; let s:=Signed.mirror j * Signed.mirror k; have he:detX s=false:=by unfold s; rw [det_p,det_t,det_t]; rfl
    have hv := rowV (lookD he) _ _ (p (s.perm i)) (p i) _ (h s he (allFlips _ rfl) i) j
    rw [taxes,tax_m,tax_m,show s.flip i=false from (by simp [s,Signed.mirror,w.symm,v.symm]), show s.flip j=true from (by simp [s,Signed.mirror,t.symm])] at hv
    exact cancelA _ hv
 have ht(s:Signed)(q:detX s=false)(u:Anchored s)(i:Axis) : spaX (D (s.perm i)) (s.perm i)=hush (tariffX s) (spaX (D i) i):=by
    have hv:=rowV (lookD q) _ _ (p (s.perm i)) (p i) _ (h s q u i) i; cases f:s.flip i <;> cases l:tariffX s <;> simp [f,l] at hv ⊢ <;> first|exact hv|exact neg_eq_iff_eq_neg.mp hv -- cases true false yields -a=-b -> a=b or -a=b ; simp latter?
 have hr(i:Axis): spaX (D i) i=0:=by
    rcases (show i=0∨i=1∨i=2∨i=3 from by fin_cases i<;> decide) with w|w|w|w <;> subst i
    all_goals let s:=Signed.mirror 0 * X side23; have hS:Anchored s:= Anchored.prod (allFlips _ rfl) deep_anchor; have he:detX s=false:=by unfold s; rw [det_p,det_t,detSwap _ _ (by decide:(2:Axis)≠3)]; rfl
    all_goals let t:=Signed.mirror 0 * X side01; have hT:Anchored t:= Anchored.prod (allFlips _ rfl) quad_anchor; have hp:detX t=false:=by unfold t; rw [det_p,det_t,detSwap _ _ (by decide:(0:Axis)≠1)]; rfl
    all_goals apply cancelA _
    · have k:=ht s he hS 0; rw [taxes,tax_m,tax_s _ _ (by decide:(2:Axis)≠3)] at k; exact k.symm
    · have k:=ht s he hS 1; rw [taxes,tax_m,tax_s _ _ (by decide:(2:Axis)≠3)] at k; exact k.symm
    · have k:=ht t hp hT 2; rw [taxes,tax_m,tax_s _ _ (by decide:(0:Axis)≠1)] at k; exact k.symm
    have k:=ht t hp hT 3; rw [taxes,tax_m,tax_s _ _ (by decide:(0:Axis)≠1)] at k; exact k.symm
 intro i; rw [←p,←spa_p]; apply sum_eq_zero; intro j _; have h0: spaX (D i) j=0:=by by_cases e:i=j; rw [←e]; exact hr i; exact hx i j e
 rw [h0]; simp
end YM.CF.Compass
