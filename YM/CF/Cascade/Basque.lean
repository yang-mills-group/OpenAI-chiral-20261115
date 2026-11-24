import YM.CF.Cascade.Bice
set_option autoImplicit false
noncomputable section
namespace YM.CF.Cascade
open Function Filter Metric Finset Lattice Wilson Next.Free Bloch Laurent Scroll Precision Exterior Lat Ember Aroma
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate Matrix MatrixOrder Kronecker
variable {j t:ℕ}{n c f:Side}{k a b:ℝ}
open Tree SU Font Cube Extra.Iteration Nacre
open Thera Fock Dial Peaks Tulip Paige NormedSpace
open Spire Vault Laic Kennel Rush Fir Branch Tenant
open scoped Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
variable {n N:Side} {T:Op Slot}{M:Male}{J:InJ Slot n}
lemma twistHub(V:Site n→Op (coneA Slot)): kg (subHub V)=∑ i:Site n,kg (V i):=by unfold kg; rw [subhub_star,show subHub (fun _=> star _)*subHub V=subHub _ from Aroma.lung (Equiv.refl _) _ _, trace_hub]; exact Complex.re_sum ..
lemma priceGreen (p:1≤j):∃ C:ℝ,0<C∧∃ i:ℕ,∀ {N:Side}{T:Op Slot}{J:InJ Slot N}{M: Male},Foot T j M.val J→ i≤ N.val→ Even N.val→ kg ((Met J 0)⁻¹)≤ C*N.val*(Fintype.card (Site N):ℝ):=by
 obtain ⟨D,hD,n,h⟩:= sugar; obtain ⟨R,r,H⟩:=chillY j p; let K:= Fintype.card (coneA Slot); let F:= kg (bins Slot); let Q:= kg ((1:Op (coneA Slot))-bins Slot); have hf:0≤F:= kgN _; have hQ:0≤Q:=kgN _
 let C:=F*R^2*Real.pi⁻¹ *D; have hp:0≤C:=by unfold C; positivity
 refine ⟨1+2*(C+Q),(by positivity),n,fun {N T J M} U e v=>?_⟩
 let B:= fun i:Site N=> edgeH Slot j M.val (mel i); have hx : kg (subHub B)≤ C*N.val*(Fintype.card (Site N):ℝ):=by
    rw [twistHub]; let T:=N.val; let v(i):=‖bark (i:Site N)‖; have ht(i:Site N): kg (B i)≤ (F*R^2 *Real.pi⁻¹*T)*(v i^3)⁻¹:=by
       let Y:= (shell j M.val (mel i))⁻¹; have hy:‖Y‖≤ R*(v i^2)⁻¹:= H M N i; rw [show kg (B i)=F*‖Y‖^2 from ?_]; swap
       · change kg (Y • bins Slot)= _; rw [kg_I]; unfold F; rw [kg_I,sum_mul]; apply sum_congr rfl; intro k _; rw [act_smul,norm_smul,mul_pow,mul_comm]
       have hv:0<v i:=(Ember.pinch_pos _).trans_le (Ember.torch _); apply (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hy _) hf).trans; have hm:(v i)⁻¹≤ Real.pi⁻¹*T:= (inv_anti₀ (pinch_pos N) (Ember.torch i)).trans_eq (by unfold Ember.pinch T; field_simp)
       rw [mul_pow,inv_pow,←pow_mul]; calc
         F*(R^2 * ((v i)^(2*2))⁻¹) = F*R^2 *((v i)⁻¹)*(v i^3)⁻¹:=by ring
         _ ≤ _ := (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hm (by positivity)) (by positivity)).trans_eq (by ring)
    apply le_trans (sum_le_sum (fun i _=>ht i)); rw [←mul_sum]; have he:= h N e ‹Even N.val›; exact (mul_le_mul_of_nonneg_left he (show 0≤ F*R^2 *Real.pi⁻¹*T by positivity)).trans_eq (by rw [site_card]; push_cast; unfold C T; ring)
 let S:= (Fintype.card (Site N):ℝ); have hy:1-flatV Slot N = subHub (fun _=>1-bins Slot):=by
    rw [←unitHub (n:=Slot) (N:=N),← show subHub (fun _ => bins Slot)=flatV Slot N from bin_hub]; exact Aroma.hubgap _ _
 rw [U.census.2,hy]; apply (kgs ..).trans; have hg : kg (subHub (fun _:Site N=>1-bins Slot))≤ Q * N.val* S:=by
    rw [twistHub,sum_const, card_univ,nsmul_eq_mul]; change S*Q≤ _; rw [mul_comm]; apply mul_le_mul_of_nonneg_right _ (Nat.cast_nonneg _); exact le_mul_of_one_le_right hQ (by exact_mod_cast N.property)
 have hu :0≤ (N.val:ℝ)*S:= mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _); refine (mul_le_mul_of_nonneg_left (add_le_add hx hg) (by norm_num)).trans (le_trans (le_add_of_nonneg_left hu) (le_of_eq ?_)); unfold S; ring
lemma walkB(x:Air n)(h:‖x‖≤1)(t:Cover):‖rake t x‖≤1:=(pi_norm_le_iff_of_nonneg zero_le_one).mpr fun i=> (norm_le_pi_norm x _).trans h
lemma bonds(F:Air n→Cab Slot n)(p:∀ t:Cover,∀ x, F (rake t x)=mil t (F x))(R:Site n→ℝ)(h:0≤b)(k:∀ i,∀ r s,∀ x,‖x‖≤1→ ‖F x (0,r) (i,s)‖≤ R i)(v:∑ i:Site n,R i≤ b)(x)(hx:‖x‖≤1):‖F x‖ ≤ (Fintype.card (coneA Slot):ℝ)*b:=by
 let B:=Fintype.card (coneA Slot); let P (i j:Tx n Slot):= R (j.1-i.1)
 have he(i j:Site n)(r s:coneA Slot): ‖F x (i,r) (j,s)‖≤ R (j-i):=by
    let t:= lift i; have ht:wrap n t=i:= wrap_lift _; have hp:= k (j-i) r s _ (walkB x hx t); rw [p,mil_h,Aroma.creep, ht,zero_add,sub_add_cancel, norm_mul, norm_mul] at hp; unfold Rush.wind at hp; simpa [fee_norm] using hp -- tune
 refine Branch.schur P (F x) _ (by positivity) (fun i j=> he ..) (fun i=>?_) (fun i=>?_)
 · unfold Tx; rw [Fintype.sum_prod_type]; change ∑ j: Site n,∑ _ : coneA Slot,R (j-i.1)≤ _; simp_rw [sum_const,card_univ,nsmul_eq_mul,←mul_sum]; apply mul_le_mul_of_nonneg_left _ (by positivity); simpa [sub_eq_add_neg] using (Equiv.sum_comp (Equiv.addRight (-i.1)) R|>.trans_le v)
 unfold Tx; rw [Fintype.sum_prod_type]; change ∑ j: Site n,∑ _ : coneA Slot,R (i.1-j) ≤ _; simp_rw [sum_const,card_univ,nsmul_eq_mul,←mul_sum]; apply mul_le_mul_of_nonneg_left _ (by positivity);  simpa [sub_eq_add_neg] using (Equiv.sum_comp ((Equiv.neg _).trans (Equiv.addLeft (i.1))) R  |>.trans_le v) -- tune
lemma cheap(i:Site n)(p:0≤a):1 ≤ idea a i:= Real.one_le_exp (mul_nonneg p (Finset.sum_nonneg fun j _=> Nat.cast_nonneg _))
lemma pass_p(J:InJ Slot n)(e:ContDiffAt ℝ ω J 0)(l:CurveH J)(p:0≤a)(h:0≤b)(g: Aroma.bill J a≤b)(x:Air n)(hx:‖x‖≤1): ‖JD J x‖ ≤ (Fintype.card (coneA Slot):ℝ)*b:=by
 refine bonds (fun x=>JD J x) (fun i x=> honk i J e l x) _ h ?_ g x hx
 intro i r s x hx; rw [merit1 (JD J) x,Matrix.sum_apply]; apply (norm_sum_le ..).trans; refine sum_le_sum fun j _=>?_ ; rw [Matrix.smul_apply,norm_smul]; apply (mul_le_of_le_one_left (norm_nonneg _) ((norm_le_pi_norm x j).trans hx)).trans; apply (norm_entry (rook (JD J (Aroma.spur j)) i) r s).trans; exact le_mul_of_one_le_left (norm_nonneg _) (one_le_mul_of_one_le_of_one_le (cheap _ p) (cheap _ p))
lemma pass_z(J:InJ Slot n)(e:ContDiffAt ℝ ω J 0)(l:CurveH J)(p:0≤a)(h:0≤b)(g:b2 J a≤b)(x:Air n)(hx:‖x‖≤1): ‖JG J x x‖ ≤ (Fintype.card (coneA Slot):ℝ)*b:=by
 refine bonds (fun x=>JG J x x) (fun i x=> homes i J e l x x) _ h ?_ g x hx
 intro i r s x hx; rw [merit2 (JG J) x x,Matrix.sum_apply]; simp_rw [Matrix.sum_apply]; apply (norm_sum_le ..).trans; refine sum_le_sum fun j _=> (norm_sum_le ..).trans (sum_le_sum fun k _=>?_); rw [Matrix.smul_apply,norm_smul,norm_mul]; apply (mul_le_of_le_one_left (norm_nonneg _) (mul_le_one₀ ((norm_le_pi_norm x j).trans hx) (norm_nonneg _) ((norm_le_pi_norm x k).trans hx))).trans; apply (norm_entry (rook (JG J (Aroma.spur j) (Aroma.spur k)) i) r s).trans; exact le_mul_of_one_le_left (norm_nonneg _) (one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le (cheap _ p) (cheap _ p)) (cheap _ p))
end YM.CF.Cascade
