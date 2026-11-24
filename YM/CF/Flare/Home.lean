import YM.CF.Flare.Split
set_option autoImplicit false
noncomputable section
namespace YM.CF.Flare
open Function Filter Metric Finset NormedSpace Lattice Laurent Kea Lat Fir Tulip Rush Cube Jill Ember SU Dial Thera Fock Peaks Cascade
open scoped Topology BigOperators Matrix MatrixOrder ContDiff Matrix.Norms.L2Operator InnerProductSpace
attribute [local instance] opCStarAlgebra
variable {N:Side}{b:Candle}
def risky (S:Slide N b)(j:ℕ)(M:Jill.Male)(r:ℝ):Finset (Stag N):= univ.filter fun i=> high_d M S i j≤ r*pinch N^2
variable {r s a:ℝ} -- tune
variable (T:Finset (Stag N))
def shake : Stag N→Op SpinIdx:=fun i=> if i∈T then warpF else 0
def openW (a:ℝ):Stag N→Op SpinIdx:= 1+a • shake T
def mateV (a:ℝ):Stag N→Op SpinIdx:=star (openW T (-a))
def heave (r:ℝ):ℝ:=16*(1+Real.sqrt r)
lemma heave_p(r:ℝ):0<heave r:=by unfold heave; positivity
lemma twang(x:ℝ):star (mateV T x)*openW T x=1:=by
 unfold mateV; rw [star_star]; funext i; by_cases h:i∈T
 · simp only [openW,shake,Pi.mul_apply,Pi.smul_apply,Pi.add_apply,h,ite_true,Pi.one_apply,Pi.neg_apply]; rw [add_mul,mul_add,mul_add,one_mul,one_mul,mul_one,Matrix.smul_mul,Matrix.mul_smul, warp_sq,smul_zero,smul_zero,add_zero]; rw [neg_smul]; abel
 simp [openW,shake,h]
-- finite
lemma risky_card(j:ℕ)(p:1 ≤ j)(r:ℝ)(h:0<r):∃ A:ℕ,∀ N:Side,Even N.val →∀ b:Candle,∀ S:Slide N b,∀ M:Jill.Male, (risky S j M r).card≤ A:=by
 obtain ⟨c,C,hc,hC,H⟩:=zip p; let d:=Real.sqrt (r/c); have hd:0<d:= Real.sqrt_pos.2 (by positivity)
 obtain ⟨A,v,V⟩:= orb_p (d+1) (by positivity); obtain ⟨K,b⟩:=exists_nat_gt A
 refine ⟨45*K,fun n q d0 S M=>?_⟩; let X:= univ.filter fun l:Site n=> tall l≤d+1; let f(i:Stag n):= (i.1+ wrap n (S.z i.2),i.2); let Y:= risky S j M r
 have ht:Set.MapsTo f (↑Y) ↑(X×ˢ (univ:Finset Slot)):=by
   intro i p; obtain ⟨k,l⟩:=i; have hx:= (mem_filter.mp (show _∈ risky _ _ _ _ from p)).2; let K:= k+wrap n (S.z l); let P:=angle S (k,l); have hp: c*‖P‖^2 ≤ r*pinch n^2:= le_trans (H M _ (up_p S q (k,l))).1 hx; have hA:= (crest K (S.u l)).1; have hy:d^2=r/c:= Real.sq_sqrt (by positivity); have hv:‖P‖≤d*pinch n:=by
     apply (pow_le_pow_iff_left₀ (norm_nonneg _) (mul_nonneg hd.le (pinch_pos _).le) (by decide : 2≠0)).1; rw [mul_pow,hy]; apply le_of_mul_le_mul_left (a:=c) _ hc; exact hp.trans_eq (by field_simp)
   change (K,l)∈ X×ˢ _; refine mem_product.mpr ⟨mem_filter.mpr ⟨mem_univ _,?_⟩,mem_univ _⟩; have he: tall K-1≤d:=le_of_mul_le_mul_right (hA.trans hv) (pinch_pos _); linarith
 have he:(Y.image f).card ≤ 45*K:=by apply le_trans (card_le_card (show Y.image f⊆_ from Finset.image_subset_iff.mpr ht)); rw [card_product, card_univ,slots,mul_comm]; exact Nat.mul_le_mul_left _ (by exact_mod_cast ((V n).trans b.le)) -- tune
 rw [card_image_of_injective _ (show Injective f from by intro (i,l) (j,k) h; simp [f] at h; obtain ⟨u,rfl⟩:=h; congr 1; exact add_right_cancel u)] at he; exact he

lemma acre(J:ℕ)(S:Slide N b)(g: Even N.val)(M:Jill.Male)(t:0<r)(w:r*pinch N^2≤1/8)(u:s≥heave r):let T:=risky S J M r; let a:=s*pinch N; ∃ U:Stag N→Op SpinIdx,∀ i,Clad (field S J M i) Aop (openW T a i) (mateV T a i) (U i)∧ ‖U i‖ ≤ (4/(heave r)+ (Real.sqrt r)⁻¹)/pinch N:=by
 intro T A; let V(i:Stag N):=openW T A i; let F(i: Stag N):=field S J M i; let W:= mateV T A; have hs:= lt_of_lt_of_le (heave_p _) u; have hv:=pinch_pos N; have ha:0<A:=mul_pos hs hv; have ht:= Real.sqrt_pos.mpr t
 suffices h:∀ i:Stag N, ∃ K:Op SpinIdx,Clad (F i) Aop (V i) (W i) K∧ ‖K‖≤(4/(heave r)+(Real.sqrt r)⁻¹)/pinch N by choose K H using h; exact ⟨K,H⟩
 intro i; let d:= high_d M S i J; have hp:0≤d:=norm_nonneg _; obtain ⟨h,k,z,l⟩:= crestQ J M S g i; let N' (t:ℝ):= t⁻¹ • (Aop * V i * F i); have he:star (W i)* V i=1:= congr_fun (twang T A) i
 by_cases o:i∈T
 · have hm:d≤r*pinch N^2:=(mem_filter.mp o).2; have hx:Real.sqrt d ≤ A/16:=by
      have hh:Real.sqrt d ≤ Real.sqrt (r* pinch N^2):= Real.sqrt_le_sqrt hm; rw [Real.sqrt_mul t.le,Real.sqrt_sq hv.le] at hh; unfold A heave at *; nlinarith
   have hy:V i=1+A • warpF:=by unfold V openW; simp [shake,o]
   obtain ⟨hg,C⟩:=Low.serv h hp z l ha hx (hm.trans w)
   rw [←hy] at hg C; obtain ⟨Y,D,E⟩:= port_inv _ C
   refine ⟨_,bridge h A_id k.symm he ha (show N' A=_ from rfl) D,?_⟩; rw [norm_smul]; rw [Real.norm_of_nonneg (by positivity : 0 ≤ A⁻¹)]; refine (mul_le_mul_of_nonneg_left  (show ‖star (N' A)*Y*Aop‖≤4 from ((norm_mul_le ..).trans ((mul_le_mul ((norm_mul_le ..).trans (show _≤2*2 from mul_le_mul ((norm_star _).trans_le hg) E (norm_nonneg _) (by norm_num))) (IsStarProjection.norm_le _ A_id) (norm_nonneg _) (by norm_num)).trans (by norm_num)))) (by positivity : 0 ≤ A⁻¹)).trans ?_; unfold A
   have hh:= heave_p r; rw [mul_comm (_⁻¹),←div_eq_mul_inv,← div_div]; gcongr; apply le_trans _ (le_add_of_nonneg_right (inv_nonneg.mpr ht.le)); gcongr
 have hm:r*pinch N^2<d:=lt_of_not_ge (fun x=>o (mem_filter.mpr ⟨mem_univ _,x⟩)); let B:=Real.sqrt d; have hp:0<d:=lt_trans (by positivity) hm; have hB:0<B:=Real.sqrt_pos.mpr hp
 have hK: V i=1:=by simp [V,openW,shake,o]
 have hy:N' B=B⁻¹ • (Aop * F i):=by unfold N'; rw [hK,mul_one]
 have hb:N' B *star (N' B)=Aop:=by
   have hk(F':Op SpinIdx)(p:IsStarProjection F')(v:Aop*F'*Aop=d • Aop):Aop*F'*star (Aop*F')=d • Aop:=by rw [star_mul,p.2,Aadj,←mul_assoc,mul_assoc _ F' F',p.1,v]
   rw [hy,star_smul,Matrix.smul_mul,Matrix.mul_smul,hk (F i) h z,star_trivial, smul_smul,smul_smul,mul_assoc,show B⁻¹ * (B⁻¹ * d)=1 by
     nth_rw 1 [show d=B*B from (by rw [← sq]; exact (Real.sq_sqrt hp.le).symm)] -- tune notation
     field_simp
    ,one_smul]
 refine ⟨_,bridge h A_id k.symm he hB (show N' B=_ from rfl) (Y:=1) (by rw [hb,mul_one]; abel),?_⟩; rw [norm_smul,Real.norm_of_nonneg (by positivity : 0 ≤ B⁻¹), mul_one]; have hh:‖N' B‖≤1:=by
    rw [hy,norm_smul,Real.norm_of_nonneg (by positivity : 0 ≤ B⁻¹)]; exact (mul_le_mul_of_nonneg_left (Low.aster h hp.le z l) (by positivity : 0 ≤ B⁻¹)).trans_eq (inv_mul_cancel₀ hB.ne')
 apply le_trans (mul_le_mul_of_nonneg_left (show ‖star (N' B)*Aop‖≤ 1 from (norm_mul_le ..).trans ((mul_le_mul ((norm_star _).trans_le hh) (IsStarProjection.norm_le _ A_id) (norm_nonneg _) zero_le_one).trans_eq (by simp))) (by positivity : 0 ≤ B⁻¹)); rw [mul_one]
 have hx:Real.sqrt r*pinch N ≤ B:=by unfold B; nth_rw 1 [←Real.sqrt_sq (x:=pinch N) hv.le]; rw [← Real.sqrt_mul t.le]; exact Real.sqrt_le_sqrt hm.le
 calc
    _ ≤ (Real.sqrt r*pinch N)⁻¹:= by gcongr
    _ ≤ _:= by rw [mul_inv, ←div_eq_mul_inv (Real.sqrt r)⁻¹]; gcongr; exact le_add_of_nonneg_left (by have hx:=heave_p r; positivity)
end YM.CF.Flare
