import YM.CF.Kea.Cool
/-!
Remove *all* log size losses with the fermion root weight as well. Not by
multiplicative perturbation of a Haar estimate after normalization. No claims
on phase signs or any RP. Elementary extensive bound applies for the final base
weight in every RG stage (Pad and projection bound needed, provided later in
construction).
-/
set_option autoImplicit false
set_option synthInstance.maxSize 16000
set_option maxHeartbeats 400000
noncomputable section
namespace YM.CF.Fixed.Extensive
open Function Filter Lattice Next.Free Finset Fock SU Lat Laurent Metric MeasureTheory Cube Scroll Phase Peaks Paige Spire Vault Ember
open Jill Kea
open scoped Topology BigOperators InnerProductSpace Matrix MatrixOrder Matrix.Norms.L2Operator Kronecker
attribute [local instance] opCStarAlgebra
variable {N : Side} {k:ℕ}
private lemma stepAverage(n:ℕ): -(n:ℝ) ≤ ∑ i∈range n,Real.log (((i:ℝ)+1)/n) := by
  induction n with
  | zero=> simp
  | succ n ih=>
    rcases eq_or_ne n 0 with h|h
    · subst n; norm_num
    let A:ℝ:=n; have hp:0<A:=by unfold A; positivity
    let Q:ℝ:= Real.log ((A+1)/A)
    rw [sum_range_succ]; push_cast; rw [show Real.log ((A+1)/(A+1))=0 by rw [div_self (by positivity),Real.log_one]]; rw [add_zero]
    have he(i:ℕ): Real.log (((i:ℝ)+1)/(A+1))= Real.log (((i:ℝ)+1)/n) - Q := by apply eq_sub_of_add_eq; unfold Q; rw [←Real.log_mul (by positivity) (by positivity)]; congr 1; unfold A; field_simp
    change -(A+1)≤∑ i∈range n, Real.log (((i:ℝ)+1)/(A+1)); simp_rw [he]; rw [sum_sub_distrib,sum_const,card_range,nsmul_eq_mul]; change _≤ _-A*Q; have ht: A*Q≤1:=by
      apply le_trans (mul_le_mul_of_nonneg_left (Real.log_le_sub_one_of_pos (by positivity : 0<(A+1)/A)) hp.le); exact le_of_eq (by field_simp; ring)
    dsimp only [A] at *; linarith

def tauL(n i:ℕ):ℝ:= ((i:ℝ)+1)/n
def tauR (n i:ℕ):ℝ:= ((n:ℝ)-i)/n
lemma interval_left(x:Per N) : 0<tauL N.val x.val ∧ tauL N.val x.val≤1:= ⟨div_pos (by positivity) (nPos N),(div_le_one (nPos _)).mpr (by exact_mod_cast ZMod.val_lt x)⟩
lemma interval_right(x:Per N) : 0<tauR N.val x.val∧tauR N.val x.val≤1:= ⟨div_pos (sub_pos.mpr (by exact_mod_cast ZMod.val_lt x)) (nPos N),(div_le_one (nPos _)).mpr (by exact sub_le_self _ (Nat.cast_nonneg _))⟩
lemma mode_lower(x: Per N) : tauL N.val x.val * tauR N.val x.val ≤ |principal x|:=by
  have hp:=interval_left x; have hq:=interval_right x; unfold Lat.principal; have ht:1≤Real.pi:=by linarith [Real.pi_gt_three]
  split_ifs
  · refine ((mul_le_of_le_one_right hp.1.le hq.2).trans ?_).trans (le_abs_self _); unfold winding; refine le_trans ?_ (le_mul_of_one_le_right (by positivity) ht); unfold tauL; gcongr; linarith
  refine ((mul_le_of_le_one_left hq.1.le hp.2).trans ?_).trans (neg_le_abs _); let A:ℝ:=N.val; let k:ℝ:=x.val
  unfold winding; change _ ≤ -((2*k+1)/A*Real.pi-2*Real.pi)
  calc _ ≤ Real.pi *((A-k)/A) := le_mul_of_one_le_left hq.1.le ht
       _ ≤ _ := ?_
  have he:0<A:=nPos N; field_simp; have hy: k+1≤A:=by unfold k A; exact_mod_cast show x.val+1≤ N.val from ZMod.val_lt x
  linarith

lemma period_sum (N:Side)(f:ℕ→ℝ) : ∑ i:Per N,f i.val= ∑ i∈range N.val,f i:=by
  rw [←sum_image (ZMod.val_injective N.val).injOn]; rw [show univ.image (ZMod.val (n:=N.val))=range N.val from ?_]
  ext i; constructor
  · intro g; obtain ⟨a,h,rfl⟩:= mem_image.mp g; exact mem_range.mpr (ZMod.val_lt _)
  intro g; let r:Per N:=i; exact mem_image.mpr ⟨r,mem_univ _, ZMod.val_natCast_of_lt (mem_range.mp g)⟩
lemma translationPrice (N:Side)(f:Per N→ℝ): ∑ i:Site N,f (i 0)=(N.val:ℝ)^3*∑ i:Per N,f i:=by
  let g(t:Per N):Site N:=fun _=>t; let A:= ∑ i: Site N,f (i 0); let s:=∑ i:Per N, f i
  have hp(a:Per N):∑ i:Site N,f ((i 0)+a)=A:= Equiv.sum_comp (Equiv.addRight (g a)) (fun i:Site N=>f (i 0))
  have hh(i:Site N): ∑ a:Per N,f ((i 0)+a)=s := Equiv.sum_comp (Equiv.addLeft (i 0)) f
  have he : (∑ _a:Per N,A)= (∑ _i:Site N,s):=by
    rw [sum_congr (s₁:=univ) (f:=fun a:Per N=>A) (g:=fun a=> ∑ i: Site N, f ((i 0)+a)) rfl (fun i _=> (hp i).symm),sum_comm]; exact sum_congr rfl fun i _=>hh i
  rw [sum_const,sum_const,card_univ,card_univ,site_card,nsmul_eq_mul,nsmul_eq_mul,ZMod.card] at he
  push_cast at he; apply mul_left_cancel₀ (nPos N).ne'; exact he.trans (by ring)
lemma reverseSum (N:Side): ∑ i∈range N.val, Real.log (tauR N.val i)=∑ i∈range N.val,Real.log (tauL N.val i):=by
  let n:= N.val; let f:= fun i=> Real.log (tauL n i)
  rw [←Finset.sum_range_reflect f]; apply sum_congr rfl; intro i hi; apply congrArg Real.log; unfold tauR tauL; congr 1; have hp:=mem_range.mp hi; rw [Nat.cast_sub (by omega : i ≤ N.val-1), Nat.cast_sub (show 1≤N.val from N.property),Nat.cast_one]; ring

lemma supportLower (h:1≤k): ∃ C:ℝ, 0≤ C ∧ ∀ (N:Side), Even N.val→∀ M:Jill.Male,
    -(N.val:ℝ)^4 * C ≤ Real.log (∏ i:Kea.Stag N, disk k M (angle (too N) i)) ∧ 0 < (∏ i:Kea.Stag N,disk k M (angle (too N) i)):=by
  obtain ⟨c,D,hc,hD,P⟩:= Jill.zip h; let C:= 45*(4 + ‖Real.log c‖); refine ⟨C,by unfold C; positivity,fun N h M=>?_⟩
  let p(i:Site N):= P M (pm i); have he(i:Site N): Bound Real.pi (pm i):=(too_u N (i, Classical.arbitrary Slot)) ▸ up_p (too N) h _ -- rewrite
  have hp(i:Site N): 0<disk k M (pm i):=(mul_pos hc (pow_pos (pt_p i) _)).trans_le (p i (he i)).1; simp_rw [too_u]; constructor; swap; · exact prod_pos fun i _=> hp _
  let A(x:Site N):=tauL N.val (x 0).val; let B(x:Site N):=tauR N.val (x 0).val
  have ht(x:Site N):Real.log c +2*(Real.log (A x)+Real.log (B x)) ≤ Real.log (disk k M (pm x)) := by
    have hX:0<A x:= (interval_left _).1; have hy:0<B x:= (interval_right _).1; have hu: c*(A x*B x)^2 ≤ c*‖pm x‖^2:=mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) ((mode_lower (x 0)).trans (b_abs (pm x) 0)) 2) hc.le
    have he':= Real.log_le_log (pow_pos (mul_pos hX hy) 2|>mul_pos hc) (hu.trans ((P M _ (he x)).1)); rw [Real.log_mul (by positivity) (by positivity),Real.log_pow,Real.log_mul hX.ne' hy.ne'] at he'; exact_mod_cast he'
  have hS:= sum_le_sum (f:=fun x:Site N=> Real.log c+ 2*(Real.log (A x)+Real.log (B x))) (s:=univ) (fun i _=> ht i)
  simp only [sum_add_distrib, ←mul_sum, sum_const,card_univ,site_card,nsmul_eq_mul] at hS; unfold A B at hS; rw [translationPrice N (fun x=>Real.log (tauL N.val x.val)),translationPrice N (fun x=>Real.log (tauR N.val x.val)),period_sum N (fun i=>Real.log (tauL N.val i)),period_sum N (fun i=>Real.log (tauR N.val i)),reverseSum] at hS
  rw [Real.log_prod (fun i _=> (hp _).ne'),Fintype.sum_prod_type]; simp only [sum_const,card_univ,slots,nsmul_eq_mul,Nat.cast_ofNat,←mul_sum]; push_cast at hS
  have hp': -(N.val:ℝ)≤ ∑ i ∈ range N.val,Real.log (tauL N.val i):=stepAverage _
  have hx: Real.log c≥ -‖Real.log c‖:= (abs_le.mp (show |Real.log c|≤‖Real.log c‖ from le_rfl)).1; unfold C; linarith [mul_le_mul_of_nonneg_left hp' (show 0≤ (N.val:ℝ)^3 by positivity),mul_le_mul_of_nonneg_left hx (show 0≤(N.val:ℝ)^4 by positivity)]

variable {L B m:Side}{o:Odd L.val}{Y: Pricing k L o (Thread k)}{e:ℝ}(P: Grasp Y B e)
lemma pay_angel (hv:0<e)(h:1≤k):∃ C:ℝ,0≤C∧∀ m:Side,P.roundZ≤(CSide m B).val → Pad k (CSide m B) →∀ M:Jill.Male, Real.exp (-((CSide m B).val:ℝ)^4*C) ≤ angel m P M:=by
  obtain ⟨C,p,H⟩:= supportLower h; refine ⟨C,p,fun m u T M=>?_⟩; unfold angel; rw [rich u hv M T emptyC (too _)]; obtain ⟨A,g⟩:= H _ T.1 M; exact (Real.exp_le_exp.mpr A).trans_eq (Real.exp_log g)
end YM.CF.Fixed.Extensive
