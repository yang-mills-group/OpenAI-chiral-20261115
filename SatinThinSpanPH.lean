import SatinThinArch
import YM.CF.Tap.Mantel
set_option autoImplicit false
set_option maxHeartbeats 680000
set_option synthInstance.maxSize 20000
set_option linter.unusedSimpArgs false
noncomputable section
namespace YM.CF.QuadClock
open Function Filter Metric Fir Lattice Laurent Next.Free Bloch Finset Lat Stationary Rush Cube Scroll SU Drapes Peaks Dial Paige Brace Vault Fock Tulip Font Spire Nacre Ember Pec Levier Skye Scree Hove Haro Tap Moto
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix Matrix.Norms.L2Operator Kronecker MatrixOrder Classical
attribute [local instance] opCStarAlgebra
set_option quotPrecheck false
open Ione StressFlux AnalyticBridge.VerifiedReset

variable {n:Side}{c t:Bool}{s:Signed}{U:UNI SpinIdx}(H:JetS s c t U)
lemma pal_sub (A B:Pal) : castPal c t U (A-B)=castPal c t U A-castPal c t U B:=by unfold castPal Thera.jazz; cases t <;> simp <;> abel
lemma dome_zero (s:Sweep n): costDome s 0=0:=by unfold costDome coinArc castPal Thera.jazz; ext<;>simp [win_z]

open Tap
-- next local lemmas from Tap/Mantel
private lemma neg_K(A:Op SpinIdx)(F:Op Slot): A⊗ₖ (-F)= -(A⊗ₖ F):=by ext; simp
private lemma humming {s:Signed}{U:UNI SpinIdx}(h:JetS s false false U)(A: Pal)(p:Binned A): twist (twoU U false) A=∑ i:Axis,petal i⊗ₖ (hush (s.flip i) (spaX A (s.perm i))):=by
 conv_lhs=> rw [←p,←spa_p,map_sum,←Equiv.sum_comp s.perm] -- p abbrev rw needs unfold
 apply sum_congr rfl; intro i _; let F:=spaX A (s.perm i); rw [show twist _ (petal _⊗ₖ _)= twist U (petal (s.perm i)) ⊗ₖ F from ?_,pet_up h]; swap
 · have he:= Scroll.wingK U (xtra false) (petal (s.perm i)) F; change _= twist U _ ⊗ₖ twist 1 F at he; rwa [one_des] at he
 change hush _ _⊗ₖ F= petal i⊗ₖ hush _ F; cases hv:s.flip i<;>simp [neg_K,op_kron_neg]
private lemma spaQ {s:Signed}{U:UNI SpinIdx}(h:JetS s false false U)(A B:Pal)(p:Binned A)(q:Binned B)(t:Bool)(e:twist (twoU U false) A=hush t B)(i:Axis): hush (s.flip i) (spaX A (s.perm i))=hush t (spaX B i):=by
 rw [humming h A p,←q,←spa_p] at e -- RHS error rewrap p? unfold q
 have he(t:Bool):hush t (∑ i:Axis, petal i⊗ₖ spaX B i)=∑ i:Axis, petal i⊗ₖ hush t (spaX B i):=by cases t <;>simp [neg_K]
 rw [he] at e; exact ((spa_s i (fun j=>hush _ _)).symm.trans (congr_arg (spaX · i) e)).trans (spa_s ..)
private lemma cancelA (X:Op Slot)(h: -X=X): X=0:=by
 have ht : (2:ℝ) • X=0:=by rw [two_smul]; nth_rewrite 1 [←h]; abel
 exact (smul_eq_zero.mp ht).resolve_left (by norm_num)
/-! Subgroup affordances: each index is fixed by at least one of the
  proper quarter-turns on the two planes. -/
private lemma otherRotation(a:Axis):∃ s:Signed, Quad s ∧ detX s=false ∧ s.perm a=a ∧ s.flip a=false ∧ tax s= -1:=by
 have hp {i j:Axis}(h:i≠j)(x:a≠i)(y:a≠j)(t:Quad (Pec.X (Equiv.swap i j))) : ∃ s:Signed,Quad s ∧ detX s=false ∧ s.perm a=a ∧ s.flip a=false ∧ tax s= -1:= by
    let s:= Signed.mirror i*Pec.X (Equiv.swap i j); refine ⟨s,(quad_mirror i).mul t,by unfold s; rw [det_p, det_t,detSwap i j h]; rfl,by simp [s,X,Signed.mirror,x,y,Equiv.swap_apply_of_ne_of_ne x y], by simp [s,X,Signed.mirror,x,y,Equiv.swap_apply_of_ne_of_ne x y,x.symm], by unfold s; rw [tax_m,tax_mi,tax_s _ _ h,one_mul]⟩
 by_cases h:a=0∨a=1; · exact hp (i:=2) (j:=3) (by decide) (by rcases h with h|h<;>rw [h]<;>decide) (by rcases h with h|h<;>rw [h]<;>decide) quad_swap_hi
 exact hp (i:=0) (j:=1) (by decide) (mt Or.inl h) (mt Or.inr h) quad_swap_lo
-- Want inverse transform d.L.V. s used with s^-1? Norm shape tested. arbitrary stabilizing array.
lemma scareDome (O:Site n)(D:Dome)(p:seedsP D)
 (w:∀ s:Sweep n,s∈cycleSweep n→ Earlier s O O→ costDome s D=bandSign s • D):D=0:=by
 -- descend condition on ANY proper spinX? h picks arbitrary from pose symmetry, use it with spinU false
 have hx (s:Signed)(v:Quad s)(l:detX s=false) : coinArc s false false (spinU false s) D= tax s • D:=by
    obtain ⟨z,u,p,y⟩:=poseAll s O O; have h:=w z⁻¹ ((cycleSweep n).inv_mem (cycleQ _|>.mpr (u.symm ▸ v))) y.backward; rwa [band_inv, costDome,inv_inv,bandSign,p,u,l] at h -- bandSign reducible
 have hm(b:Bool)(F:Axis→Pal)(p:∀ i,Binned (F i))(W:∀ s:Signed, Quad s → detX s=false→∀ i, sign s i • twist (twoU (spinU false s) false) (F (s.perm i))=tax s • F i): F=0:=by
    have hst(i j:Axis) : spaX (F i) j = 0:=by
       by_cases h:i=j
       · subst j
         obtain ⟨s,q,l,a,w,y⟩:=otherRotation i; let U:=spinU false s; have ht:=W s q l i; rw [y,a,sign,w] at ht; simp only [Bool.false_eq_true,ite_false,one_smul,neg_one_smul] at ht; have H:= spaQ (s:=s) (U:=U) (by simpa only [U,l] using spinZ false s) (F i) (F i) (p i) (p i) true ht i; rw [a,w] at H; exact cancelA _ H.symm
       obtain ⟨k,v,t⟩:=(show ∀ i j:Axis, ∃ k:Axis,i≠k∧j≠k from by decide) i j; let s:=Signed.mirror j*Signed.mirror k; have u:detX s=false:=by unfold s; rw [det_p,det_t,det_t]; rfl
       have he: s.flip i=false:=by simp [s,Ne.symm h,v.symm,Signed.mirror];
       let U:=spinU false s; have ht:= W s ((quad_mirror _).mul (quad_mirror _)) u i; rw [show tax s=1 from (by unfold s; rw [tax_m,tax_mi,tax_mi,one_mul]),sign,he] at ht; simp only [Bool.false_eq_true,ite_false,one_smul] at ht
       have hp:= spaQ (s:=s) (U:=U) (by simpa only [U,u] using spinZ false s) (F i) (F i) (p i) (p i) false ht j; rw [show s.flip j=true from by simp [s,t.symm,Signed.mirror]] at hp; exact cancelA _ hp
    funext i; rw [←p,←spa_p]; simp [hst]
 have hp:D.1=0:=by
    have ht (i:Axis): spaX D.1 i=0:=by
       obtain ⟨s,q,l,v,t,a⟩:=otherRotation i; have he:= congrArg Prod.fst (hx s q l); let U:=spinU false s; change twist (twoU U false) D.1 = tax s • D.1 at he; rw [a,neg_one_smul] at he; have hp:= spaQ (s:=s) (U:=U) (by simpa only [U,l] using spinZ false s) D.1 D.1 p.1 p.1 true he i; rw [v,t] at hp; exact cancelA _ hp.symm
    have hv:Binned D.1:= p.1; rw [←hv,←spa_p]; simp [ht]
 refine Prod.ext hp (Prod.ext (hm false D.2.1 p.2.1 ?_) (hm true D.2.2 p.2.2 ?_))
 · intro s q l i; exact congrFun (congrArg (fun x:Dome=>x.2.1) (hx s q l)) i
 intro s q l i; exact congrFun (congrArg (fun x:Dome=>x.2.2) (hx s q l)) i
end YM.CF.QuadClock
