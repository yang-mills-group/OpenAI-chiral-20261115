import Anomaly.Ship.Cast
import YM.SU5.Exchange.Seed.Ticket
import YM.CF.Roots.Coal
import YM.CF.Roots.Coal
import YM.CF.Roots.Coal
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 16000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Roots
open Function Finset Filter Metric MeasureTheory Lattice Lattice.Corona Wilson Precision Pressure RG
open Jet Fock Cube Lat Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
variable {n:Side}
-- enumeration of sample paths (Mark circle scripts pay steep mixed bond). R0 fixed root.
-- 
variable {t X:ℕ}{q z:ℝ}
variable {L B:ℕ} {J I:Type}[DecidableEq J][Fintype J][LinearOrder I][Fintype I]
variable {s:Support n}{σ:I→ Site n}
open Vow.TreasuryFog
open Vow TreasuryFog
variable (Q:ℝ)(W:Finset (Finset I))(Θ:J→ Support n)(Ξ:Site n)(F:Finset I→ J→ℝ)(U:∀ i∈W,0≤F i)(a:ℝ)(u:8≤ B)(p:∀ i∈W,∀ j:J,F i j≠0→ Ξ∈Θ j ∧ poke_F σ (Θ j) i)
local notation "Yq"=> dra_k B a
local notation "Yr"=> dra_k B (a+(B:ℝ)⁻¹)
variable (H:∀ i∈W,∑ j,dra_k B (a+(B:ℝ)⁻¹) (Θ j)*(F i j) ≤ Q)
variable (T:packF q B t)(P:Force_M B σ t)(uQ:0 ≤ Q)(h:1≤ q)
local notation "Λ"=> TallT Θ B
include u
private lemma sat_cap(x:Support n)(i j:Site n)(v:i∈x)(g:j∈x)(t: ¬ B^2≤20*coverNumber B x): separation i j≤B+cape_B B:=by
 refine (extent _ B v g).trans ?_
 have hx: 20*coverNumber B x < B^2:=lt_of_not_ge t
 have hu: (coverNumber B x)*(4*B+2) ≤ (coverNumber B x)*(6*B):=Nat.mul_le_mul_left _ (by omega)
 have hk: (coverNumber B x)*(20*B) < B^2*B:=by rw [← mul_assoc,mul_comm (coverNumber B x)]; exact Nat.mul_lt_mul_of_pos_right hx (by omega)
 unfold cape_B; nlinarith
-- omit extras from sat_cap (placed above include)
include Q W F U a p H u T P uQ h
lemma set_tags (v:∀ i∈W,(i:Finset I).card=1): (∑ i∈ W,q^i.card* ∑ j,Yq (Θ j)*F i j) ≤ (t*q*Q+chillCash B*Q):=by
 let V:= univ\Λ; let f(i j):=Yq (Θ j)*F i j; let U'(i:I): Finset I:={i}
 have ht(i):∑ j,F i j=∑ j,F i j:=rfl -- remove
 have hv(i:Finset I):q^i.card*∑ j,f i j=q^i.card*(∑ j∈V,f i j)+q^i.card*∑ j∈ Λ,f i j:=by rw [←mul_add,sum_sdiff (subset_univ _)]
 change ∑ i∈ W,q^i.card*∑ j,f i j≤ _
 simp_rw [hv,sum_add_distrib]; refine add_le_add ?_ (tag_restore Θ Ξ Q W F U a u p H T P uQ h)
 let S:= W∩(reach_B (cape_B B) B σ Ξ).image U'; have hS:S.card≤t:=(card_le_card inter_subset_right).trans (le_trans card_image_le (P.2 Ξ))
 let z(i:Finset I):= q^i.card*∑ j∈V,f i j
 have he: (∑ i∈ S,z i)=(∑ i∈ W,z i):=by
    refine sum_subset inter_subset_left (fun i w s=>?_); unfold z; rw [sum_eq_zero,mul_zero]; obtain ⟨x,v'⟩:= card_eq_one.mp (v i w)
    intro j y; unfold f; suffices h:F i j=0 by rw [h,mul_zero]
    by_contra g; obtain ⟨qz,U'⟩:= p i w j g; exact s (mem_inter.mpr ⟨w,mem_image.mpr ⟨x,mem_filter.mpr ⟨mem_univ _,sat_cap u (Θ j) _ _ qz (U' x (by simp [v'])) (fun t=>(mem_sdiff.mp y).2 (mem_filter.mpr ⟨mem_univ _,t⟩))⟩,v'.symm⟩⟩)
 change ∑ i∈W,z i ≤ _; rw [←he]; have hx:0≤ q:=zero_le_one.trans h
 refine (sum_le_sum (g:=fun _=> q*Q) (fun i w=>?_ )).trans ?_
 · let g:=(mem_inter.mp w).1; unfold z; rw [v i g,pow_one]; refine mul_le_mul_of_nonneg_left ?_ hx
   refine (sum_le_sum (s:=V) (g:=fun j=>Yr (Θ j)*F i j) (fun j _=>?_)).trans ((sum_le_sum_of_subset_of_nonneg (subset_univ _) fun j _ _=>mul_nonneg (Real.exp_pos _).le (U i g _)).trans (H i g))
   unfold f; exact mul_le_mul_of_nonneg_right (Real.exp_monotone (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right (by positivity)) (Nat.cast_nonneg _))) (U i g j)
 rw [sum_const,nsmul_eq_mul,←mul_assoc]; gcongr
lemma mixed_tags (v:∀ i∈W,(i:Finset I).Nonempty∧1 < i.card∧Set.InjOn σ i): (∑ i∈ W,q^i.card* ∑ j,Yq (Θ j)*F i j) ≤ chillCash B*Q:=by
 apply le_trans ?_ (tag_restore Θ Ξ Q W F U a u p H T P uQ h); apply le_of_eq; refine sum_congr rfl fun i w=> congrArg (_*·) (sum_subset (subset_univ _) ?_).symm
 intro j _ t; suffices h:F i j=0 by rw [h,mul_zero]
 by_contra s; obtain ⟨g,uS⟩:= p i w j s; let V:=Θ j; have hV:¬ B^2≤20*coverNumber B V:=fun v=>t (mem_filter.mpr ⟨mem_univ _,v⟩)
 obtain ⟨k,x,l,z,r⟩:= one_lt_card.mp (v i w).2.1
 have ht:= P.1 k l (fun y=> r ((v i w).2.2 x z y)); have hu:=sat_cap u _ _ _ (uS k x) (uS l z) hV
 omega
end YM.CF.Roots
