import YM.CF.Dial.Haute
/-! Flat intertwining both spins at common pairing. -/
set_option autoImplicit false
set_option synthInstance.maxSize 8000
noncomputable section
namespace YM.CF.Dial
open Function Filter Lattice Laurent Bloch Next.Free Metric Lat Finset Branch Cube Tenant SU Rush Drapes Fir Tulip Fock Peaks
open scoped Topology Matrix MatrixOrder BigOperators Matrix.Norms.L2Operator Kronecker InnerProductSpace
attribute [local instance] opCStarAlgebra
variable {N P:Side}(G: Ratio N P)
def helmC : Op (Iota G):= (plates N fun _=>tJustice G.count) ⊗ₖ SU.Pair.fullM apex.val
lemma helm_eq(u:Bool): squareD G u (vacancyY N P)=helmC G:=by
  rw [helmC,pilesV];
  ext ⟨⟨x,r,b⟩,i⟩ ⟨⟨y,t,c⟩,j⟩; simp only [squareD,readK,Matrix.submatrix_apply, jump_apply, Equiv.refl_apply,tJustice, s_app];
  change (if (x,r)=(y,t) then _ else (0:ℂ))=_; simp only [Matrix.kroneckerMap_apply,jump_apply,Equiv.refl_apply,Fir.s_app]; by_cases h:x=y∧r=t
  · simp only [Prod.mk.injEq,h,and_self,ite_true,h.1,h.2]; cases u <;> rfl
  simp only [Prod.mk.injEq,if_neg h,ite_mul]; split_ifs with l p <;> (first|rfl|exact False.elim (h ⟨l,p⟩)|simp)
lemma crew_c : helmC G = foot G ((plates P fun _=>spinJ)⊗ₖ SU.Pair.fullM apex.val):=by
  rw [helmC,pilesV,pilesV]
  ext ⟨⟨x,r,b⟩,i⟩ ⟨⟨y,t,c⟩,j⟩; simp only [tJustice,Fir.stack,jump_apply, Matrix.kroneckerMap_apply,Equiv.refl_apply]
  change _= (if isle G (x,r)=isle G (y,t) then spinJ b c else 0)* _; simp [ite_and,switchG]
variable (j:ℕ)(L:Side)(ho:Odd L.val)(T:Script Male)(M:Male)(u:Bool)(ht:Use j L T)(hg:G.count=L)
lemma still_u : (vacancyY N P).1= (1:Coil N P):=by unfold vacancyY post unionP; simp; rw [profile_trivial,profile_trivial]; trivial -- tune
lemma cc_foot(A:Op (Single P)): cc (foot G A)=foot G (cc A):=rfl
lemma homeT (hj:1≤j): foal j u M G (vacancyY N P).1 *helmC G= helmC G *cc (foal j u M G (vacancyY N P).1):=by
  rw [still_u,foal]; change foot G (skewE j M u P 1)*_= _*cc (foot G (skewE j M u P 1)); rw [cc_foot,skew_flat j hj, crew_c,←foot_mul,←foot_mul];
  rw [cart_traded (cBar j M.val u hj M.property),op_cc_kron,op_kron_mul,op_kron_mul, cc_one,one_mul,mul_one,pT j u M.property]
lemma cc_angle (u:Bool): angle u * spinJ=spinJ * cc (angle u):=by
  have hp:Aop*spinJ=spinJ*cc Aop:=by rw [Adef,Matrix.smul_mul,add_mul,one_mul,cc_smul, cc_add,cc_one,Matrix.mul_smul,mul_add,mul_one, spinJ_grading]; norm_num
  cases u <;> simp [angle,cc_sub,sub_mul,hp,mul_sub]
lemma stack_cc (L:Side)(f: Site L→ Op SpinIdx): cc (Fir.stack L f)=Fir.stack L (fun i=>cc (f i)):=jump_cc ..
lemma spikes (L:Side)(u:Op SpinIdx): cc (spike L u)=spike L (cc u):=by rw [spike,spike, stack_cc]; congr 1; funext i; split<;>simp
lemma cc_stackA (L:Side)(u:Bool): sA u L*tJustice L=tJustice L*cc (sA u L):=by
  unfold sA slashA tJustice; rw [← stack_mul,stack_cc, ←stack_mul]; congr 1; funext i; exact cc_angle u
lemma ccB {N:Side}(p:Op SpinIdx)(k:Side):cc (plates N (fun _=>sA u k))=plates N (fun _=>cc (sA u k)):= shape _ _ fun i=>rfl
lemma t_s {L:Side}(u:Bool): tall u L*tJustice L=tJustice L*cc (tall u L):=by
  let V:=tJustice L; let P:=peb L; have he:P*V=V*P:=by simp only [V,P,tJustice,peb,mul_spike,spike_mul,one_mul,mul_one]
  have hp:cc P=P:=by unfold P; rw [peb,spikes, cc_one]
  rw [tall]; change _*(1-P)*V=V*_;
  rw [cc_mul,cc_sub,cc_one,hp, mul_assoc _ (1-P),sub_mul,he,one_mul,show V-V*P=V*(1-P) by rw [mul_sub,mul_one],← mul_assoc,cc_stackA,mul_assoc]
lemma v_s (u:Bool)(k j p)(hk: Odd k.val)(M:Male)(h:p∈realCube zone)(hx:p≠0): vine u j k M.val p*tJustice k=tJustice k *cc (vine u j k M.val (-p)):=by
  rw [vine,vine,cc_add,add_mul,mul_add,t_s]; congr 1
  rw [tJustice,Fir.grow,Fir.grow,spikes,mul_spike,spike_mul, barR _ (k*M.val) _ (hk.mul M.property) h hx]
private lemma rid(j:ℕ)(k:Side)(M: Male)(N:Side)(u:Bool)(hk: Odd k.val): plates N (vine u j k M.val)*plates N (fun _=>tJustice k)= plates N (fun _=>tJustice k)*cc (plates N (vine u j k M.val)):=by
  let W :=fun p=> cc (vine u j k M.val (-p)); have hh: cc (plates N (vine u j k M.val))=plates N W:=by
    apply Rush.shape; intro l; obtain ⟨w,he⟩:= dollar l; change mel (backN l)=_ at he
    have hp := base_subset_realCube zone_pos (mel_h (backN l)); rw [he]; unfold W vine Fir.grow bent; rw [bar_overlap _ _ (realCube_neg (base_subset_realCube zone_pos (mel_h l))) w (he ▸ hp)]
  rw [hh,pilesP,pilesP]; exact pilesE _ _ fun p hp hx=> v_s u k j p hk M hp hx
include hg
lemma board_q(hj:1≤j): wh j L ho u M G (vacancyY N P).1*helmC G=helmC G*cc (wh j L ho u M G (vacancyY N P).1):=by
  rw [still_u,wh_base j L ho hj G hg]; unfold helmC
  rw [op_cc_kron,cc_one,op_kron_mul,op_kron_mul,one_mul,mul_one,rid j G.count M N u (hg.symm ▸ ho)]
omit hg
lemma plus_r : lobe G u*helmC G= helmC G*cc (lobe G u):=by rw [lobe,helmC,op_kron_mul,op_cc_kron,op_kron_mul, cc_one,one_mul,mul_one,ccB u 0 G.count,pilesP, pilesP, cc_stackA]
section
variable {n:Type*}[DecidableEq n][Fintype n]{K A:Op n}
lemma re_inv (h:IsUnit A)(e:A*K=K*cc A): A⁻¹*K=K*cc (A⁻¹):=by
  apply h.mul_left_cancel; rw [←mul_assoc,(live h).1, one_mul, ←mul_assoc,e,mul_assoc, ←cc_mul,(live h).1,cc_one,mul_one]
lemma dock (h:K∈unitary _)(e:A*K=K*cc A): star A * K= K*cc (star A):=by
  have he: star K * star A=star (cc A)*star K:=by rw [←star_mul,e,star_mul]
  have ht: star K*K=1:=h.1; apply (live_of ht).mul_left_cancel; rw [←mul_assoc,he,mul_assoc,ht,mul_one,←mul_assoc (star K) K,ht,one_mul,cc_star]
end
include ht hg ho
lemma proffer (hj:Even j):ticketT T u M G (vacancyY N P).1*helmC G=helmC G*cc (ticketT T u M G (vacancyY N P).1):=by
  let V:= (vacancyY N P).1; let S:=helmC G; let A:=T M G 1; let Q:=lobe G u
  have hm:Odd G.count.val:=hg.symm ▸ ho
  have hc:A*S=S*cc A:=by unfold A S; rw [ht.fixed M G hg,cart_traded (cBrix j _ hm),helmC,op_kron_mul,op_cc_kron,op_kron_mul,cc_one,one_mul,mul_one,posed j hm,(bT j).eq]
  have hu:IsUnit A:=by unfold A; rw [ht.fixed M G hg]; let T:=cart N (tub (brix j G.count)); exact live_of (show (T⊗ₖ (1:Op Slot))*(T⁻¹⊗ₖ 1)=1 by rw [op_kron_mul,(live (brix_inv G j hj hm)).1,one_mul, Matrix.one_kronecker_one])
  rw [still_u,ticketT,ice_one]; change (A⁻¹*Q+star A*(1-Q))*S=S*cc (A⁻¹*Q+star A*(1-Q));
  have he:S∈ unitary _ := by unfold S; rw [←helm_eq G true]; exact unit_square G true _ -- tune
  rw [add_mul,cc_add,cc_mul,cc_mul,mul_add]; congr 1
  · rw [mul_assoc A⁻¹, plus_r,← mul_assoc,re_inv hu hc, mul_assoc]
  rw [mul_assoc (star A),show (1-Q)*S=S*cc (1-Q) by rw [cc_sub,cc_one,mul_sub,mul_one,sub_mul,plus_r,one_mul], ←mul_assoc,dock he hc,mul_assoc]
end YM.CF.Dial
