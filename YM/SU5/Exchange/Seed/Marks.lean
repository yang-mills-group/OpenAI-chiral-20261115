import YM.SU5.Exchange.Seed.Mono
import YM.CF.Liss.Cut
/-! Hypothesis of contour perturbation only on distinct footprint *orders* in list,
    unlike `ΘXtip`. Frame covariance not yet imposed. -/
set_option autoImplicit false
set_option synthInstance.maxSize 24000
noncomputable section
namespace YM.CF.Liss
set_option maxHeartbeats 620000
open Mew Function Filter NormedSpace Finset MeasureTheory Fock
open scoped Topology Classical BigOperators Matrix.Norms.L2Operator
variable {N I E:Type*}[Fintype N][LinearOrder N][Fintype I][LinearOrder I]
variable (Z:I→ FC N)
lemma calm_rub {T A: FC N} (h:Commute T A)(k:ℕ):
 HasDerivAt (fun x:ℂ=> (x • T + A)^k) ((k:ℂ) • (T*A^(k-1))) 0:=by
 induction k with
 |zero=> simpa using (hasDerivAt_const (x:=(0:ℂ)) (1:FC N)) -- arguments?
 |succ k ih=>
    let Y(x:ℂ):= x • T +A; have p:HasDerivAt Y T 0:=by simpa [Y] using ((hasDerivAt_id' (0:ℂ)).smul_const T).add_const A
    let w:= ih.mul p; simp_rw [pow_succ] -- also exponents
    refine w.congr_deriv ?_
    change _ * Y 0+(0 • T + A)^k*T=_; rw [show Y 0=A from (by unfold Y; simp)]
    rw [zero_smul,zero_add,← (h.pow_right k).eq]; cases k
    · simp
    rename_i k; rw [Algebra.smul_mul_assoc, Nat.add_sub_cancel, Nat.add_sub_cancel, mul_assoc T, ←pow_succ]; push_cast; rw [add_smul,one_smul]; simp [add_smul]
def paper (n:ℕ)(v:Key I): FC N:= ((n.factorial:ℂ)⁻¹) • ((waveΦ Z v)^n)
lemma paperH (n:ℕ): Solvent n (paper Z n):=by
 have h: Solvent 1 (waveΦ Z):=Solvent.sum univ _ (fun i _=> Solvent.map (LinearMap.ringLmapEquivSelf ℂ ℂ (FC N)|>.symm (Z i)) (Solvent.bill i)) -- tune
 apply Solvent.smul
 induction n with
 |zero=> simp_rw [pow_zero]; exact Solvent.still _
 |succ n ih=> simp_rw [pow_succ]; exact ih.times h
private lemma commuteTag (h:∀ i j, Commute (Z i) (Z j))(i:I)(x:Key I)(w:x∈ hill I)(n:ℕ):
 cutI (paper Z (n+1)) i x= Z i*paper Z n (dune i x):=by
 let Q:=waveΦ Z (dune i x); have he : Commute (Z i) Q:= Commute.sum_right _ _ _ fun j _=> (h i j).smul_right _
 let k:ℂ:= ((n+1).factorial:ℂ)⁻¹
 rw [← (mitt (paperH Z (n+1)|>.riv) w i).deriv, show (fun y:ℂ=> paper Z (n+1) (update x i y))=fun y=>k • ((y • Z i +Q)^(n+1)) from funext fun y=>by unfold paper; rw [penX]]; change deriv (k • (fun x:ℂ=> (x • Z i + Q)^(n+1))) 0 = _; rw [((calm_rub he (n+1)).const_smul k).deriv,smul_smul,Nat.add_sub_cancel]
 unfold paper k; rw [Algebra.mul_smul_comm,Nat.factorial_succ]; push_cast; congr 1; field_simp
lemma paperTip_v (h:∀ i j, Commute (Z i) (Z j))(l:List I)(p:l.Nodup) : tipI (paper Z l.length) l=(l.map Z).prod:=by
 induction l with
 |nil=> change (((0:ℕ).factorial:ℂ)⁻¹) • (waveΦ Z 0)^0=1; simp
 |cons i l ih=>
    obtain ⟨v,p⟩:= List.nodup_cons.mp p; let L:=ContinuousLinearMap.mul ℂ (FC N) (Z i); let F:=paper Z l.length ∘ dune i
    calc _ = tipI (L ∘ F) l := lace_C _ (fun z w=>commuteTag Z h i z w l.length) roots
         _ = Z i*tipI F l:= (sim_H (((paperH Z l.length).riv).stay i) L l roots)
         _ = _ :=by unfold F; rw [tip_V _ _ v,ih p]; try rfl
variable [NormedAddCommGroup E][NormedSpace ℂ E][CompleteSpace E]
lemma laceOn (S: Finset I)(l:List I)(p:∀ i∈l,i∈ S) {f g:Key I→E}(v:∀ z∈hill I,(∀ i∉S,z i=0)→ f z=g z):∀ z∈hill I,(∀ i∉S,z i=0)→ lance f l z=lance g l z:=by
 induction l generalizing f g with
 | nil=> exact v
 | cons i l ih=>
    apply ih (fun i t=> p i (List.mem_cons_of_mem _ t))
    intro z w a; unfold cutI; apply integral_congr_ae; apply ae_of_all; intro t; dsimp only; rw [v]; exact fill_I w _ (homeC _)
    intro j u; rw [update_of_ne (fun (p' : j = i)=>u (p'.symm ▸ p i List.mem_cons_self))]; exact a j u -- syntax tune
lemma paperTip (l:List I)(p:l.Nodup) (h:l.Pairwise fun i j=> Commute (Z i) (Z j)) : tipI (paper Z l.length) l=(l.map Z).prod:=by
 let s:=l.toFinset; let Y(i:I):= if i∈s then Z i else 0; have hp(i:I)(p:i∈l):Y i=Z i:=if_pos (List.mem_toFinset.mpr p)
 have hs(i j:I)(p:i∈l)(q:j∈l): Commute (Z i) (Z j):=by
    clear hp Y s; induction l with
    |nil=> simp at p -- shadow p nodup
    |cons k l ih=>
       obtain ⟨t,u⟩:=List.pairwise_cons.mp h; rcases List.mem_cons.mp p with P|p <;> rcases List.mem_cons.mp q with Q|q; · rw [P,Q]
       · rw [P]; exact t j q
       · rw [Q]; exact (t i p).symm
       exact ih ((List.nodup_cons.mp ‹(k::l).Nodup›).2) u p q -- motive contains s and hp; tune
 have he(i j:I):Commute (Y i) (Y j):=by unfold Y; split_ifs with a b c; exact hs _ _ (List.mem_toFinset.mp a) (List.mem_toFinset.mp b); exact Commute.zero_right _; exact Commute.zero_left _; exact Commute.zero_left _
 rw [show l.map Z=l.map Y from List.map_congr_left (fun i v=>(hp i v).symm),←paperTip_v Y he l p]
 apply laceOn s l (fun i w=>List.mem_toFinset.mpr w) _ _ roots (fun _ _=>rfl)
 intro z w v; unfold paper; rw [show waveΦ Z z=waveΦ Y z from Finset.sum_congr rfl (fun i t=>?_)]
 unfold Y; split; rfl
 next h=>rw [v _ h,zero_smul, zero_smul]
lemma ketTip (l:List I)(p:l.Nodup)(h:l.Pairwise fun i j=> Commute (Z i) (Z j))(x:Wave N):
 tipI (fun z=> acts (paper Z l.length z) x) l=acts (l.map Z).prod x:=by
 let A:FC N→ₗ[ℂ] Wave N:= {toFun:=fun P=>acts P x, map_add':=fun _ _=>act_add .., map_smul':=fun _ _=>act_smul ..}
 change tipI (A.toContinuousLinearMap ∘ paper Z l.length) l=A ((l.map Z).prod); rw [← paperTip Z l p h]; exact sim_H (paperH Z l.length|>.riv) A.toContinuousLinearMap l roots
end YM.CF.Liss
