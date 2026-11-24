import YM.SU5.FiniteGaugeData.ArchiveK.Bricks
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
namespace YM.CF.Window.ArchiveK
open Function Filter Lattice Metric Complex Finset Laurent Next.Free Bloch Fir Lat MeasureTheory Fock Rush Largo WithLp
open scoped Topology BigOperators Pointwise ENNReal Matrix Matrix.Norms.L2Operator MatrixOrder InnerProductSpace ComplexOrder Kronecker
attribute [local instance] opCStarAlgebra
attribute [local instance] opCStarAlgebra
set_option linter.unusedSectionVars false
set_option quotPrecheck false
namespace Midway
open Waltz Violas
variable {X:Type*}[Fintype X][DecidableEq X]{S T:Finset Cover}{N:Side}(A B:Finset Cover)(M:Ruler (Beam B) X)(p:A⊆ S)(v:B⊆ S)(P:S⊆T)(H: Waltz N T)
def wall(S:Finset Cover) : Ruler (Beam T) X:=torso T (reset S (fleece B M))
def city (P:A ⊆ T): Beam A→ Beam T := fun i=> (⟨i.1.val, P i.1.property⟩,i.2)
abbrev cradle (P:A⊆T):= grip (city A P) (fun _=>1)
def specW(T A:Finset Cover)(V:Finset SpinIdx) := (Finset.univ:Finset (Beam T)).filter fun i=> i.1.val∈ A ∧ i.2∈ V
abbrev Dense:= plusHalf
local notation "U"=> Beam A
local notation "Ψ"=> inp N T
local notation "F"=> wall (T:=T) B M S
local notation "W"=> (inp N T*wall (T:=T) B M S)
local notation "Q"=> cutM (specW T A Dense)
local notation "O"=> cradle A (p.trans P)
lemma city_c (P:A⊆T):Injective (city A P):= fun i j h=> Prod.ext (Subtype.ext (congrArg (fun x:Beam T=>x.1.val) h)) (congrArg (fun x:Beam T=>x.2) h)
lemma city_is (P:A⊆T): (cradle A P)ᴴ*cradle A P=1:= grip_clean _ _ (city_c A P) (fun i=>by simp)
-- city expansion. upper cover. cut output.Cred.
include p P
lemma hull_K (i:U)(Y:Finset SpinIdx): city A (p.trans P) i ∈ specW T A Y↔ i.2∈Y:=by simp [city,specW]
lemma top_orbit : cutM (specW T A Dense)*cradle A (p.trans P) = O *cutM (Xx A):= by
 apply Matrix.ext; intro i j; rw [compass,compass']; by_cases h:i=city A (p.trans P) j; swap; · simp [cradle,grip,h]
 subst i; simp [hull_K A p P,Xx]
lemma tyreW(i:U)(j:X)(t:i.2∈plusHalf) : wall B M S (city A (p.trans P) i) j=(Pick A B*M) i j:=by
 have hv:i.1.val∈S:=p i.1.property; unfold wall torso reset; rw [Matrix.of_apply]; simp only [city]; rw [if_pos hv]; unfold fleece; rw [Matrix.mul_apply,Matrix.mul_apply]; refine Finset.sum_congr rfl fun v h=>?_ ; rw [show fuelR B _ _ v=(Pick A B i v) from fp_true (i.1.val-v.1.val) i.2 v.2 t]
lemma wall_u : cutM (specW T A Dense)*(F)= cradle A (p.trans P)*Pick A B*M:=by
 let f:=city A (p.trans P); let L:= Pick A B*M; have he:Q*O*L = (O)*L:=by rw [top_orbit A p P]; unfold L; rw [Matrix.mul_assoc,←Matrix.mul_assoc (cutM (Xx A)),pick_feather]; -- tune
 rw [Matrix.mul_assoc _ (Pick A B)]; change _=(O)*L; rw [←he,Matrix.mul_assoc Q]; apply Matrix.ext; intro i j; rw [compass,compass]; by_cases h:i∈specW T A Dense; swap; · rw [if_neg h,if_neg h]
 rw [if_pos h,if_pos h]; obtain ⟨x,b0⟩:∃ x:Beam A,city A (p.trans P) x=i:= ⟨(⟨i.1.val,((mem_filter.mp h).2).1⟩,i.2),rfl⟩; subst i
 rw [tyreW A B M p P x j ((hull_K A p P x Dense).mp h)]; rw [Matrix.mul_apply (N:=L),Finset.sum_eq_single x]; simp [cradle,grip,L]; intro b _ hb; have he:city A (p.trans P) x≠ city A (p.trans P) b:= (city_c A _).ne (Ne.symm hb); simp [cradle,grip,he]; simp
include H
lemma home_v : cutM (WalU N A)*(Ψ*F)=(Ψ)*O*(Pick A B*M):=by
 rw [←Matrix.mul_assoc, inp_inc H (p.trans P) Dense]; change Ψ*(Q)*(F)= _; rw [Matrix.mul_assoc Ψ, wall_u A B M p P]; simp_rw [Matrix.mul_assoc]
-- q norm & Asset
omit H P p in
lemma orth_q {X Y Z:Type*}[Fintype X][Fintype Y][Fintype Z][DecidableEq Y][DecidableEq Z] (A:Ruler X Y)(B:Ruler Y Z)(h:Aᴴ*A=1)(p:Bᴴ*B=1): (A*B)ᴴ*(A*B)=1:=by rw [Matrix.conjTranspose_mul,Matrix.mul_assoc, ←Matrix.mul_assoc Aᴴ A, h, Matrix.one_mul,p]
lemma wall_abs (h:(Pick A B*M)ᴴ*(Pick A B*M)=1) : let Wχ:=cutM (WalU N A)*(W); Wχᴴ*Wχ=1∧ Wχᴴ*W=1:=by -- local notation ambiguity U
 intro U'; let I' := cutM (WalU N A); have hx:I'*U'=U':=by unfold U'; rw [←Matrix.mul_assoc, show cutM (WalU N A)*cutM (WalU N A)=_ from (cutM_idp _).1]
 have he:U'ᴴ*U'=1:=by unfold U'; rw [home_v A B M p P H]; exact orth_q _ _ (orth_q _ _ H.theta_t (city_is _ _)) h
 refine ⟨he,?_⟩; nth_rw 1 [← hx]; rw [Matrix.conjTranspose_mul, Matrix.mul_assoc,show I'ᴴ=I' from cutM_adj _, he] -- not defeq.U.
#print axioms wall_abs
omit p
lemma wall_house: cutM (wal N S)*(inp N T* wall (T:=T) B M S)=inp N T* wall (T:=T) B M S:=by rw [←Matrix.mul_assoc, inp_inc H P univ,Matrix.mul_assoc]; unfold wall; rw [torso_bill' (T:=T) (reset S (fleece B M)) (fun _ h=> if_neg h)]
include v
lemma wall_back : cutM (WalL N B)*((cutM (scel N))*(inp N T*wall (T:=T) B M S))=cutM (scel N)*(inp N T* wall (T:=T) B M S):= by
 rw [←Matrix.mul_assoc,cutM_hold,inter_eq_left.mpr ?_]; swap; · rw [pickWal]; exact inter_subset_right
 let Y:= (cutM ((univ:Finset (↑T)) ×ˢ (plusHalf)ᶜ)); let X' :=specW T B plusHalfᶜ; have he:cutM (scel N)* Ψ= Ψ * Y:=by rw [show scel N=(univ ×ˢ plusHalfᶜ) from ?_ ,spinCommT]; ext; simp [scel,ruddy]
 rw [←Matrix.mul_assoc, inp_inc H (v.trans P) plusHalfᶜ,←Matrix.mul_assoc, he, Matrix.mul_assoc,Matrix.mul_assoc]; refine congrArg _ ?_; apply Matrix.ext; intro i j; rw [compass]; unfold Y; rw [compass]; split; next e=> rw [if_pos (mem_product.mpr ⟨mem_univ _, ((mem_filter.mp e).2).2⟩)]
 next e=>
    split; next w=>
        have he:i.2∈ plusHalfᶜ:= (mem_product.mp w).2; have hp:i.1.val∉ B:=fun t=> e (mem_filter.mpr ⟨mem_univ _,t, he⟩)
        unfold wall torso; rw [Matrix.of_apply]; unfold reset; split; swap; · rfl
        symm; unfold fleece; rw [Matrix.mul_apply]; exact sum_eq_zero fun a _=>by rw [show fuelR B i.1.val i.2 a=0 from fp_zz _ _ _ he (sub_ne_zero.mpr (by intro v; exact hp (v ▸ a.1.property))),zero_mul]
    next w=> rfl
#print axioms wall_back
end Midway
end YM.CF.Window.ArchiveK
