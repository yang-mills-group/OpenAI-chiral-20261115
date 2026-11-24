import YM.SU5.Relativistic.Upsy
import YM.SU5.FiniteGaugeData.Pannier.Blizzard
/-! # Permit through any rotation B→complement. Signs ONLY enter original mark factor. Keep sum in Zone. -/
set_option autoImplicit false
set_option synthInstance.maxSize 12000
set_option maxHeartbeats 300000
noncomputable section
namespace YM.CF.Papyrus.Franc
open Function Filter NormedSpace Fock Finset Thera Pea
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators
attribute [local instance] opCStarAlgebra
variable {I:Type*}[LinearOrder I][Fintype I]
namespace Pea
lemma vending (A:Pea I)(X:FC I): A.tagH*X*A.hat=A.mint.glow X:=by
 rw [tagH,hat,Algebra.mul_smul_comm,Algebra.smul_mul_assoc,Algebra.smul_mul_assoc,smul_smul,inv_mul_cancel₀ (Complex.ofReal_ne_zero.mpr A.duty.ne'),one_smul]; rfl
def slept (I:Type*)[LinearOrder I][Fintype I]:Pea I:=⟨0,0,⟨mul_zero _,star_zero _⟩,⟨mul_zero _,star_zero _⟩,mul_zero _⟩
lemma slept_r : (slept I).robe=0:=add_zero _
lemma slept_b : (slept I).hat=1 ∧ (slept I).tagH=1 ∧∀ (P:Op I), (slept I).leak P=0:=by
 simp [hat, tagH,mint,Φ,candy,nodes,slept,leak,frost,quant_one]
-- face travel
lemma Zones.turnP {A B:Pea I}(h:A.Zones B) (U:UNI I): (A.face U).Zones (B.face U):=by constructor; rw [←A.face_robe,←B.face_robe,←map_mul,h.fares,map_zero]
end Pea
abbrev Shell (A:Pea I)(S:Finset I): Prop:= cutM S*A.robe=A.robe
variable {A C:Pea I}{U: UNI I}{s t S:Finset I}{P Q B:Op I}(p:IsStarProjection P)(h:IsStarProjection Q)(b:IsStarProjection B){k:ℕ}
lemma Shell.turn (g:Shell A s)(u:twist U (cutM s) =cutM t): Shell (A.face U) t:=by unfold Shell; rw [←u,←A.face_robe,←map_mul,g]
include b in
lemma twistEpoch (T:Pea I)(u: twist U P= 1-Q)(v:twist U B=1-B)(m:ℕ): twist U ((T.mint.foldC (Saber (B:=B) p m)).sell)=star (((T.face U).mint.foldC (Saber (B:=B) h m)).buy):=by
 unfold Shaft.foldC; simp only; rw [map_mul, glow_fits U, mounted U p h b u v,star_mul]
structure Nought (P: Shaft I) (F:FC I)(Y:Op I)(k δx:ℝ)(S:Finset I): Prop where
 slips : ∃ (A:Pea I), Shell A S ∧ A.leak Y≤ k ∧ ∀ (T:Pea I),T.Zones A → ‖(T.mint.foldC P).glow F * A.hat‖≤ Real.exp δx
include b in
lemma Nought.race {U: UNI I}(H:twist U (cutM S)=cutM s)(u:twist U P= 1-Q)(w:twist U B=1-B){F:FC I}{Λ r:ℝ}(g:Nought (Saber (B:=B) p k) F P Λ r S)(v:Sector t false F): Nought (Saber (B:=B) h k) (theta U F) Q Λ r s:=by
 obtain ⟨A,j,a,e⟩:=g.slips; constructor; refine ⟨A.face U,j.turn H,?_,fun T z=>?_⟩
 · have he:= A.posture U P; rw [u,sub_sub_cancel] at he; rwa [he]
 let Y:=T.face (star U)
 have hh: Y.face U=T:=by nth_rw 1 [←star_star U]; exact T.face_step ..

 have hb: twist (star U) (A.face U).robe=A.robe:=by rw [←face_robe U A,twist_inv]
 have hz:Y.Zones A:=by have he:= z.turnP (star U); rw [A.face_step] at he; exact he
 let Z:= Y.mint.foldC (Saber (B:=B) p k)
 have hx:=e Y hz; have hy:= glow_theta U Z (((Y.face U).mint).foldC (Saber (B:=B) h k)) (twistEpoch p h b Y u w k) v; rw [hh] at hy
 rw [← hy,←theta_hat, ←theta_mul]; unfold theta; rw [twist_norm, Scroll.norm_cc]; exact hx
variable [Nonempty I]
lemma Shell.trim {A:Pea I}(p:Shell A S)(e:S⊆t): Shell A t:=by unfold Shell; nth_rw 1 [←p]; rw [←mul_assoc, Pannier.Chancel.cut_from_right S t e,p] -- imports
lemma Shell.separate (a:Shell A S)(e:Shell C t)(v:Disjoint S t): Zones A C:=by
 constructor; have he: A.robe*cutM S=A.robe:=by simpa only [star_mul, A.robe_p.isSelfAdjoint.star_eq,(cutM_idp _).isSelfAdjoint.star_eq] using congrArg star (show cutM _*_= _ from a)
 nth_rw 1 [←he,←e]; simp only [mul_assoc]; rw [←mul_assoc (cutM S),show cutM S*cutM t= 0 from ?_,zero_mul,mul_zero]; unfold cutM; rw [Matrix.diagonal_mul_diagonal]; ext i j; by_cases h:i=j; subst j; by_cases w:i∈S; have hp:i∉t:=disjoint_left.mp v w; simp [w,hp]; simp [w]; simp [h]
lemma Shell.double (h:Zones A C)(g:Shell A S)(e:Shell C t):Shell h.fuse (S∪t):=by unfold Shell; rw [h.fuse_robe,mul_add,g.trim (subset_union_left ..),e.trim (subset_union_right ..)]
-- supplier symbolic batching list. Preserve per-slot K variable. Keep head.
variable {ι:Type*}{P:Op I}{m:ℕ}{μ:ℝ}{S:Shaft I}
lemma victoryS (Y:Op I) (F:ι→FC I)(x:ι→Finset I)(δx:ι→ℝ)(L:List ι) (p:L.Pairwise fun i j=>Disjoint (x i) (x j)) (g:∀ i∈L,Nought S (F i) Y μ (δx i) (x i)) (A:Pea I) (D:Finset I) (h:Shell A D) (z:∀ i∈ L,Disjoint D (x i)):
    ∃ (P:Pea I), P.leak Y≤ A.leak Y+L.length * μ ∧ ‖A.tagH*S.glow (L.map F).prod * P.hat‖≤Real.exp ((L.map δx).sum):=by
 induction L generalizing A D with
 | nil=> refine ⟨A,by simp,?_⟩; simp [S.glow_nil, A.receive]
 | cons i l ih=>
    obtain ⟨T,a,b,k⟩:= (g i List.mem_cons_self).slips
    let W:=h.separate a (z i List.mem_cons_self); let T':= W.fuse
    obtain ⟨R,r,v⟩:= ih (List.pairwise_cons.mp p).2 (fun i v=>g i (List.mem_cons_of_mem _ v)) T' (D∪x i) (Shell.double W h a) (fun j v=> Finset.disjoint_union_left.mpr ⟨z j (List.mem_cons_of_mem _ v),(List.pairwise_cons.mp p).1 j v⟩)
    refine ⟨R,?_ ,?_⟩
    · change _≤T'.leak Y+_ at r; apply r.trans; unfold T'; rw [added,List.length_cons]; push_cast; linarith
    simp only [List.map_cons,List.prod_cons,List.sum_cons, Real.exp_add,S.glow_mult]; let X:=(A.mint.foldC S).glow (F i); let K:=S.glow (l.map F).prod; have hh:A.tagH*S.glow (F i)=X*A.tagH:=by unfold X; rw [Shaft.fold_use,←vending,mul_assoc _ A.hat,A.intake,mul_one]; -- foil
    rw [←mul_assoc A.tagH,hh, show X*A.tagH*K*R.hat=X*T.hat*(T'.tagH*K*R.hat) from ?_]; exact (norm_mul_le ..).trans (mul_le_mul (k A W) v (norm_nonneg _) (Real.exp_pos _).le)
    have hf:T'.tagH=T.tagH*A.tagH:=by unfold T'; rw [show W.fuse=W.partner.fuse from ?_, co_tag]; unfold Zones.fuse; congr 1; abel; abel
    rw [hf]; simp only [mul_assoc]; rw [←mul_assoc T.hat, T.intake, one_mul]
end YM.CF.Papyrus.Franc
#print axioms YM.CF.Papyrus.Franc.victoryS
