import YM.SU5.Relativistic.Brandy
/-! # multiplier on finite-bin, polynomial tail paid. Full trance.-/
set_option autoImplicit false
set_option maxHeartbeats 440000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Crest.Sleet.Sorcerer
open Function Set Filter Topology NormedSpace MeasureTheory Metric Real Finset Lattice Next.Free Asymptotics
open Laurent Bloch Fir Jill Ember Shore UnitAddTorus
open scoped Topology ContDiff BigOperators Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace
local notation "I"=>Complex.I
local notation "φ"=>2*Real.pi
-- grid signed stencil coefficients. Waxy always with NEGATIVE phase at v/x.
abbrev chipPay (f:Bin→ℂ)(v:Cover):=potter (waffles f) (-v)
private def mintN (v:Cover) := Finset.univ.sup fun i:Axis=>(v i).natAbs
private lemma prominent (v:Cover) : ∃ i:Axis,mintN v=(v i).natAbs ∧ ∀ j,(v j).natAbs ≤ mintN v:=by
 obtain ⟨i,t,p⟩:=Finset.exists_mem_eq_sup Finset.univ Finset.univ_nonempty (f:=fun i:Axis=> (v i).natAbs); exact ⟨i,p,fun j=>Finset.le_sup (f:=fun i=> (v i).natAbs) (Finset.mem_univ j)⟩
abbrev minted (v:Cover) : ℝ:= 1+(mintN v:ℝ)
lemma mintB {v:Cover}:1 ≤ minted v:=le_add_of_nonneg_right (Nat.cast_nonneg _)
private lemma Palme (v:Cover): (minted v)^8 *income v ≥ 1:=by
 obtain ⟨_,_,h⟩:= prominent v
 unfold income; have he:(0:ℝ)< ∏ i:Axis, (1+((v i).natAbs:ℝ)):= Finset.prod_pos (by intros; positivity)
 rw [← div_eq_mul_inv]; apply (le_div_iff₀ (pow_pos he 2)).mpr; rw [one_mul]
 have hp: ∏ i:Axis,(1+ ((v i).natAbs:ℝ)) ≤ ∏ i:Axis,minted v:= Finset.prod_le_prod (by intros; positivity) (by intro i _; unfold minted; gcongr; exact h i)
 exact (pow_le_pow_left₀ he.le hp _).trans_eq (by rw [Finset.prod_const,Finset.card_univ]; exact (pow_mul _ 4 2).symm)
private lemma capital {g:Bin→ℂ}{k:ℕ}(p: Pouch g)(h:ContDiff ℝ (↑(k+8:ℕ)) g): ∃ C:ℝ, 0 ≤ C ∧ ∀ i:Cover,(minted i)^k * ‖chipPay g i‖ ≤ C*income i:=by
 let n:=k+8; let f:=chipPay g; choose A t using ascendCream p h
 let B:=∑ i:Axis,|A i|; have he(i:Axis):A i ≤ B:= (le_abs_self _).trans (Finset.single_le_sum (f:=fun i=>|A i|) (fun i _=> abs_nonneg _) (Finset.mem_univ i))
 let F:= B * 2^n+‖f 0‖; have hP:0 ≤ B:= Finset.sum_nonneg (fun i _=>abs_nonneg _); have hx:0≤F:=by unfold F; positivity
 refine ⟨F,hx,fun i=>?_⟩
 obtain ⟨a,v,u⟩:= prominent i; let M:= (mintN i:ℝ)
 let R:=minted i; have hR:0<R:=by apply zero_lt_one.trans_le mintB
 have hs: R^n*‖f i‖ ≤ F:=by
    have hv:M^n*‖f i‖ ≤ B:= le_trans (le_of_le_of_eq (b:=A a) (by simpa [M,v,f,chipPay,n] using t a (-i)) rfl) (he a) -- tune
    by_cases q:mintN i=0
    · have hf: R=1:=by unfold R minted; rw [q,Nat.cast_zero,add_zero];
      have hg:i=0:=funext (fun j=> by have h:=u j; change _=0; omega)
      rw [hf,hg,one_pow,one_mul]; exact le_add_of_nonneg_left (by positivity)
    have hc:1≤ M:=by unfold M; exact_mod_cast (show 1 ≤ mintN i from Nat.one_le_iff_ne_zero.mpr q)
    have hD:R≤2*M:=by change 1+M≤_; linarith
    apply le_trans (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hR.le hD n) (norm_nonneg _)); rw [mul_pow,mul_assoc]; exact (mul_le_mul_of_nonneg_left hv (by positivity)).trans (by unfold F; rw [mul_comm]; exact le_add_of_nonneg_right (norm_nonneg _))
 let V:=income i; have hV:0<V:=income_2 _; have hp: R^k*‖f i‖ ≤ R^k*‖f i‖*(R^8*V):= le_mul_of_one_le_right (by positivity) (Palme i)
 refine hp.trans (le_trans (le_of_eq ?_) (mul_le_mul_of_nonneg_right hs hV.le)); unfold n; rw [pow_add]; ring
lemma richness {g:Bin→ℂ}{k:ℕ}(p: Pouch g)(h:ContDiff ℝ (↑(k+8:ℕ)) g): Summable (fun v=> (minted v)^k * ‖chipPay g v‖):=by
 obtain ⟨C,h₀,p⟩:=capital p h; exact Summable.of_nonneg_of_le (fun i=> mul_nonneg (pow_nonneg (zero_le_one.trans mintB) _) (norm_nonneg _)) p (wallet.mul_left C)
lemma whippet {g:Bin→ℂ}(p:Pouch g)(h:ContDiff ℝ 8 g) : Summable (mFourierCoeff (E:=ℂ) (waffles g)):=by
 apply (Equiv.neg Cover).summable_iff.mp; exact (show Summable (chipPay g) from (show Summable (fun i=> ‖chipPay g i‖) from by simpa using richness (k:=0) p (by simpa using h)).of_norm)
lemma lived {g:Bin→ℂ}(p:Pouch g)(h:ContDiff ℝ 8 g) (x:Bin):HasSum (fun v:Cover=> chipPay g v * mode (tmap x) (-v)) (g x):=by
 let F:C(Dish,ℂ):=⟨_,toCream p h.continuous⟩
 have he:= hasSum_mFourier_series_apply_of_summable (f:=F) (whippet p h) (ingot x); have hv:= (Equiv.neg Cover).hasSum_iff.mpr he; change HasSum (fun v:Cover=> mFourierCoeff (E:=ℂ) _ (-v) • mFourier (-v) (ingot x)) (waffles g (ingot x)) at hv; simp_rw [flashes,p.wishes, smul_eq_mul] at hv; exact hv
lemma garnet (x:Bin)(v:Cover) : ‖mode (tmap x) v‖=1:=by rw [←flashes]; simp only [mFourier, ContinuousMap.coe_mk, fourier_apply,norm_prod,Circle.norm_coe,prod_const_one] -- tune
abbrev boxOrder (k A:ℕ):= (((A:ℝ)+1)^k)⁻¹
lemma boxOrder_p(k A:ℕ):0 < boxOrder k A:=by unfold boxOrder; positivity
lemma orcas {g:Bin→ℂ}{k:ℕ}(p: Pouch g)(h:ContDiff ℝ (↑(k+8:ℕ)) g):∃ C:ℝ, 0<C∧∀ A:ℕ,∀ x:Bin, ‖g x-∑ v∈ box A, chipPay g v*mode (tmap x) (-v)‖≤ C*boxOrder k A:=by
 let F(v):= chipPay g v; obtain ⟨C,t,u⟩:=capital p h; let W:=∑' i:Cover, income i; have hp:0≤W:=tsum_nonneg (fun i=>(income_2 i).le)
 let T:=C*W; have ht:0≤T:=by unfold T; positivity
 refine ⟨1+T,by positivity,fun A x=>?_⟩; let Z: Set Cover:=(box A:Finset Cover); let L(i:Cover):= chipPay g i*mode (tmap x) (-i)
 have he:HasSum L (g x):= lived p (h.of_le (by exact_mod_cast (show 8≤k+8 by omega))) x
 have hf(y:↑(Zᶜ)):‖L y.val‖≤ boxOrder k A* (C*income y.val):=by
    have hy: A ≤ mintN y.val:=by by_contra! v; apply y.property; have hw:= (prominent y.val).choose_spec.2; exact box_test.mpr ⟨fun i=>by specialize hw i; omega,fun i=>by specialize hw i; omega⟩
    unfold L boxOrder; rw [norm_mul,garnet,mul_one,inv_mul_eq_div]; apply (le_div_iff₀ (by positivity)).mpr; rw [mul_comm]; apply (u _).trans'; apply mul_le_mul_of_nonneg_right _ (norm_nonneg _); apply pow_le_pow_left₀ (by positivity) _ _; unfold minted; rw [add_comm]; gcongr
 have hg: (g x) - ∑ v∈box A,L v= ∑' i:↑(Zᶜ),L i.val:=by rw [← (he.summable.sum_add_tsum_subtype_compl (box A)).trans he.tsum_eq]; abel
 rw [hg]; apply (norm_tsum_le_tsum_norm ((he.summable.norm).subtype (Zᶜ:Set Cover))).trans
 have ht': Summable (fun i:↑(Zᶜ)=> ‖L i.val‖):= (he.summable.norm).subtype _; have hu: Summable (fun i:↑(Zᶜ)=> boxOrder k A * (C*income i.val)):= ((wallet.mul_left C).mul_left _).subtype _
 apply le_trans (ht'.tsum_le_tsum hf hu); rw [tsum_mul_left, tsum_mul_left]
 have hx : (∑' i:↑(Zᶜ),income i.val) ≤ W := Summable.tsum_subtype_le income _ (fun i=>(income_2 i).le) wallet
 apply (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hx t) (boxOrder_p k A).le).trans; change boxOrder k A*T ≤ _; rw [mul_comm]; exact mul_le_mul_of_nonneg_right (le_add_of_nonneg_left zero_le_one) (boxOrder_p ..).le
end YM.CF.Crest.Sleet.Sorcerer
#print axioms YM.CF.Crest.Sleet.Sorcerer.orcas
