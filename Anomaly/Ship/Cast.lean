import Anomaly.Ship.Port
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
lemma tags_cost (T:packF q B t)(p:lamp_B (cape_B B) B t σ)(y:Site n)(u:0<B)(h:1 ≤ q)(g:B^2≤20*L): (∑ i∈Knot_B (cape_B B) B L σ y, q^i.card) ≤Real.exp ((L:ℝ)/B/4):=by
 let m:= L; let C:= q; let K:= Knot_B (cape_B B) B m σ y; let q':=(chip_B B m / cape_B B +1)*t; obtain ⟨hf,hR⟩:= energy_E _ m B t y σ (by unfold cape_B; positivity) p
 let A:= cape_B B; let U:=pearl (chip_B B m+B); let D:= pearl A; let k:= (chip_B B m)/A; have hc:0 ≤ C:=zero_le_one.trans h
 change ∑ i∈K,_≤_; refine (sum_le_sum (g:=fun _=>C^q') (fun i w=> pow_le_pow_right₀ h (hR i w))).trans ?_; simp only [sum_const,nsmul_eq_mul]; have hp:(K.card:ℝ) ≤ U*(D:ℝ)^k * (2:ℝ)^q':=by exact_mod_cast hf
 exact (mul_le_mul_of_nonneg_right hp (by positivity)).trans ((by dsimp only [rentP]; rw [mul_pow,mul_assoc] : _ = rentP C B m t).trans_le (T L g))
variable (Θ:J→Support n)(Ξ:Site n)
local notation "Gq"=> (fun x:ℕ=>univ.filter fun j:J=>coverNumber B (Θ j)=x)
open Vow Mew
-- Cash.Ap mileage in S(P+δ) relative to Output.P, and old fits M+. A slate k test.
-- cut at say k≥B²/20. small K terms per label at most k0 through hunch.
variable (Q:ℝ)(W:Finset (Finset I))(F:Finset I→ J→ℝ)(U:∀ i∈W,0≤F i)(a:ℝ)(u:8≤ B)(p:∀ i∈W,∀ j:J,F i j≠0→ Ξ∈Θ j ∧ poke_F σ (Θ j) i)
variable (H:∀ i∈W,∑ j,dra_k B (a+(B:ℝ)⁻¹) (Θ j)*(F i j) ≤ Q)
variable (T:packF q B t)(P:Force_M B σ t)(uQ:0 ≤ Q)(h:1≤ q)
local notation "Ξs" m:max=> (Gq m)
include U H p T P uQ u h
lemma outer_tags(m:ℕ)(v:B^2≤20*m): (∑ i∈W,q^i.card*(∑ j∈Ξs m,dra_k B a (Θ j)*(F i j))) ≤ Real.exp (- (B:ℝ)/40) * Real.exp (-(m:ℝ)/B/4) * Q:=by
 let S:=Ξs m; let d(i j):= dra_k B a (Θ j)*F i j; let X(i):=q^(i: Finset I).card*(∑ j∈ S,d i j); let Y:=Knot_B (cape_B B) B m σ Ξ; let V:= W∩Y
 have hv:(∑ i∈ V,X i)= ∑ i∈ W,X i:=sum_subset inter_subset_left fun i v' t=>by unfold X; rw [sum_eq_zero,mul_zero]; intro j s; unfold d; rw [show F i j=0 from ?_,mul_zero]; by_contra w; exact t (mem_inter.mpr ⟨v',mem_filter.mpr ⟨mem_univ _,Θ j,(p i v' j w).1,(p i v' j w).2,(mem_filter.mp s).2.le ⟩⟩)
 let β:=(m:ℝ)/ B; have ht(i)(s':i∈V):∑ j∈ S,d i j ≤ Real.exp (-β)*Q:=by
    let t:= H i (mem_inter.mp s').1; let V' (j:J):= dra_k B (a+(B:ℝ)⁻¹) (Θ j)* F i j
    have hu:∑ j∈S,V' j ≤ Q := (sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun k _ _=>mul_nonneg (Real.exp_pos _).le (U i (mem_inter.mp s').1 _))).trans t
    apply le_trans _ (mul_le_mul_of_nonneg_left hu (Real.exp_pos _).le); rw [mul_sum]; apply le_of_eq; apply sum_congr rfl; intro j q; unfold d V'; rw [←mul_assoc, dra_k, dra_k, (mem_filter.mp q).2, ←Real.exp_add]; refine congrArg (fun x=>Real.exp x*F i j) ?_; unfold β; ring
 change (∑ i∈W,X i) ≤ _; rw [← hv]; have hx:0 ≤ q:=zero_le_one.trans h
 refine (sum_le_sum (g:=fun i=>q^i.card*(Real.exp (-β)*Q)) (fun i v'=> mul_le_mul_of_nonneg_left (ht i v') (by positivity))).trans ?_
 rw [←sum_mul]; have hb:0<B:=by omega
 have hv':∑ i∈V,q^i.card ≤ Real.exp (β/4):=(sum_le_sum_of_subset_of_nonneg inter_subset_right (fun _ _ _=>by positivity)).trans (tags_cost T P.2 Ξ hb h v)
 refine (mul_le_mul_of_nonneg_right hv' (by positivity)).trans ?_; rw [←mul_assoc]; apply mul_le_mul_of_nonneg_right _ uQ; rw [←Real.exp_add,←Real.exp_add]; apply Real.exp_monotone
 have hu:(B:ℝ) ≤ 20*β:=by unfold β; rw [←mul_div_assoc,le_div_iff₀]; rw [←pow_two]; exact_mod_cast v; positivity
 change β/4+ -β ≤ -(B:ℝ)/40+_
 rw [neg_div (B:ℝ) (m:ℝ)]; linarith only [hu]
-- restore the geometric series. uniform
abbrev chillCash (B:ℕ):ℝ:=Real.exp (-(B:ℝ)/40)*(1-Real.exp (-1/(B:ℝ)/4))⁻¹
local notation "World"=> Ωb B Θ -- obsolete threshold B
abbrev TallT (Θ:J→ Support n)(B:ℕ):= univ.filter fun j:J=> B^2≤ 20*coverNumber B (Θ j)
lemma tag_restore : (∑ i∈W,q^i.card* ∑ j∈TallT Θ B,dra_k B a (Θ j)*F i j) ≤ chillCash B*Q:=by
 let V:= TallT Θ B; let S:= V.image fun x=> coverNumber B (Θ x); let G(i j):= dra_k B a (Θ j)*(F i j); have ht(i):∑ m∈ S,(∑ j∈Ξs m,G i j)= ∑ j∈ V,G i j:=by
    rw [←Finset.sum_fiberwise_of_maps_to (s:=V) (t:=S) (g:=fun x=>coverNumber B (Θ x)) (fun i h=> mem_image_of_mem _ h)]; apply sum_congr rfl; intro m v; obtain ⟨x,u,rfl⟩:=mem_image.mp v; congr 1; ext t; simp only [TallT,V,mem_filter,mem_univ,true_and]; exact ⟨fun z=>⟨z ▸ (mem_filter.mp u).2,z⟩,And.right⟩
 change ∑ i∈W,q^i.card* ∑ j∈V,G i j ≤_
 simp_rw [← ht]; -- looping?
 have he(i):q^(i: Finset I).card* ∑ m∈S,(∑ j∈Ξs m,G i j)= ∑ m∈S,q^i.card*(∑ j∈Ξs m,G i j):= mul_sum ..
 let E:=Real.exp (-(B:ℝ)/40); let K(m:ℕ):=Real.exp (-(m:ℝ)/(B:ℝ)/4)
 simp_rw [he]; rw [sum_comm]; refine (sum_le_sum (g:=fun m=> E*K m*Q) (fun m hP=>?_)).trans ?_
 · obtain ⟨j,v,rfl⟩:= mem_image.mp hP; exact outer_tags Θ Ξ Q W F U a u p H T P uQ h _ (mem_filter.mp v).2
 rw [←sum_mul,←mul_sum]; refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le) uQ
 let Kq:= Real.exp (-1/(B:ℝ)/4); have hp:(0:ℝ) < B:=Nat.cast_pos.mpr (by omega)
 have hh: ‖Kq‖ < 1:=by unfold Kq; rw [Real.norm_eq_abs,abs_of_pos (Real.exp_pos _),Real.exp_lt_one_iff]; exact div_neg_of_neg_of_pos (div_neg_of_neg_of_pos (by norm_num) hp) (by norm_num)
 have hv:∑' i:ℕ,Kq^i=(1-Kq)⁻¹:=tsum_geometric_of_norm_lt_one hh
 change _≤ (1-Kq)⁻¹; rw [←hv]; apply le_trans _ (Summable.sum_le_tsum S (fun i _=>pow_nonneg (Real.exp_pos _).le _) (summable_geometric_of_norm_lt_one hh))
 refine sum_le_sum (fun i _=>le_of_eq ?_); unfold K; rw [←Real.exp_nat_mul]; congr 1; ring
end YM.CF.Roots
