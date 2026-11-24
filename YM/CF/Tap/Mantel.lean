import YM.CF.Tap.Sink
set_option autoImplicit false
noncomputable section
namespace YM.CF.Tap
open Function Filter Metric Fir Lattice Laurent Next.Free Bloch Finset Lat Stationary Rush Cube Scroll SU Drapes Fir Peaks Dial Paige Brace Vault Fock Tulip Font Spire Nacre Ember Pec
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix Matrix.Norms.L2Operator Kronecker
attribute [local instance] opCStarAlgebra
abbrev Pal:= Op (coneA Slot)
abbrev twoU(U: UNI SpinIdx)(b:Bool):UNI (coneA Slot):=spinQ U (xtra b)
def Binned (A:Pal):Prop:=bins Slot*A*(1-bins Slot)=A
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
lemma first_n(A:Pal)(p:Binned A)(h:∀ (s:Signed), detX s=false → twist (twoU (spinX s) false) A=A): A=0:=by
 have hx(i:Axis):spaX A i=0:=by
    have hk:∀ i:Axis,∃ j:Axis,j≠i:=by decide
    obtain ⟨j,k⟩:=hk i
    let s:=Signed.mirror i *Signed.mirror j; have he:detX s=false:=by unfold s; rw [det_p,det_t,det_t]; rfl
    have hv:=spaQ (s:=s) (U:=spinX s) (by simpa only [he] using (bud_s s)) A A p p false (h s he) i; rw [show s.flip i=true from (by simp [s,Signed.mirror,k,Ne.symm])] at hv; exact cancelA _ hv
 rw [←p,←spa_p]; simp [hx]
lemma color_r(D:Axis→Pal)(p:∀ i,Binned (D i))(h:∀ (s:Signed), detX s=false → ∀ i, twist (twoU (spinX s) false) (D (s.perm i))= hush (s.flip i) (D i)) : ∀ i, D i=petal i⊗ₖ spaX (D 0) 0:=by
 have hx(i j)(v:i≠j):spaX (D i) j=0:=by
    have hk:∀ i j:Axis,∃ k:Axis,i≠k∧ j≠k:=by decide
    obtain ⟨k,w,t⟩:=hk i j; let s:=Signed.mirror j * Signed.mirror k; have he:detX s=false:=by unfold s; rw [det_p,det_t,det_t]; rfl
    have hv := spaQ (s:=s) (U:=spinX s) (by simpa only [he] using (bud_s s)) _ _ (p (s.perm i)) (p i) _ (h s he i) j
    rw [show s.flip i=false from (by simp [s,Signed.mirror,w.symm,v.symm]), show s.flip j=true from (by simp [s,Signed.mirror,t.symm])] at hv -- k not def simp
    exact cancelA _ hv
 have he(i j)(v:i≠j) : spaX (D i) i=spaX (D j) j:=by
    let s:=Signed.mirror i * X (Equiv.swap i j); have he:detX s=false:=by unfold s; rw [det_p,det_t,detSwap i j v]; rfl
    have hv:= spaQ (U:=spinX s) (s:=s) (by simpa only [he] using (bud_s s)) _ _ (p (s.perm j)) (p j) _ (h s he j) j
    rw [show s.perm j=i from ?_] at hv; swap; · simp [s,X,Signed.mirror]
    cases f:s.flip j<;> simpa [f] using hv
 intro i; conv_lhs=> rw [←p,←spa_p]
 rw [sum_eq_single i]; by_cases f:i=0; rw [f]; rw [he _ _ f]; intro j _ w; rw [hx i j w.symm]; simp; simp
structure Mind(z:Op Slot):Prop where
 firm :∀ x:SU.E, (matter x).val*z=z*(matter x).val
 adj : star z=z
 realV :cc z=z
lemma color_all(D:Axis→Pal)(p:∀ i,Binned (D i))(h:∀ s:Signed,∀ b : Bool,∀ U:UNI SpinIdx,JetS s b (detX s) U→ ∀ i,sings b (twoU U b) (D (s.perm i))= Thera.jazz (detX s) (hush (b.xor (s.flip i)) (D i)))(e:∀ i,∀ x:SU.E, Commute (D i) ((1:Op SpinIdx)⊗ₖ (matter x).val)) : Mind (spaX (D 0) 0) ∧∀ i, D i=petal i⊗ₖ spaX (D 0) 0:=by
 have hx := color_r D p (fun s hv i=>by have ht:= h s false (spinX s) (bud_s _) i; rw [hv,Bool.false_xor] at ht; exact ht); refine ⟨⟨?_,?_,?_⟩,hx⟩
 · intro x; apply spa_i 0; let F:=spaX (D 0) 0; have he:=(e 0 x).symm.eq; rw [hx,op_kron_mul,op_kron_mul,one_mul,mul_one] at he; exact he
 · let s:=Signed.mirror 0; let V:=spinX s; set F:=spaX (D 0) 0; have he:= h s false V (bud_s _) 0; have hp : detX s=true:=det_t 0
   rw [show s.perm 0=0 from rfl, hx, hp, show s.flip 0=true by simp [s,Signed.mirror],Scroll.wingK] at he
   have hk: twist V (petal (s.perm 0))=star (petal 0):=by rw [pet_down (s:=s) (U:=V) (hp ▸ (bud_s _)),show s.flip 0=true from by simp [s,Signed.mirror]]; simp
   change twist V (petal 0)⊗ₖ twist 1 F= -star (-(petal 0⊗ₖ F)) at he; rw [show twist V (petal 0)=star (petal 0) from hk,one_des,star_neg,op_star_kron,neg_neg] at he; have hm:= congrArg star he; rw [op_star_kron,op_star_kron,star_star,star_star] at hm; exact spa_i 0 hm
 let V:=Reef.axS; let F:=spaX (D 0) 0
 have he:= h 1 true V (det_i.symm ▸ cloneSX) 0; rw [show (1:Signed).perm 0=0 from rfl,hx, Scroll.wingK,det_i] at he
 change twist V (cc _)⊗ₖ (twist 1 (cc F))= -(petal 0 ⊗ₖ F) at he
 have hv:twist V (cc (petal 0))= -petal 0:=by
   conv_lhs=> rw [petal,cc_smul,cc_mul,twist_scalar,map_mul, show twist V (cc Aop)= Aop from angleX cloneSX true, show twist V (cc (gammaOp 0))=gammaOp 0 from cloneSX.cliff 0]
   unfold petal; simp; module
 rw [hv,one_des,op_kron_neg] at he; exact spa_i 0 (neg_inj.mp he)
end YM.CF.Tap
