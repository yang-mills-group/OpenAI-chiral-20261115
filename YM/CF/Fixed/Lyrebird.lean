import YM.CF.Fixed.RootTransport

/-! Quantitative obstruction in the dimensions of the actual heat. Stitching
inequality on every mode (budget not yet uses it). -/
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
namespace YM.CF.Fixed.Rift
open Function NormedSpace Matrix Lattice Finset Filter Fock BZ Mir Lat Scroll Bulk
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators ComplexOrder
attribute [local instance] opCStarAlgebra

variable {N:Side} {p:Side} (H:N.val=2*p.val)
abbrev endL(p:Side):= Fin p.val
abbrev room(N:Side)(x:endL p) : Per N := ↑x.val
def flight_b(N:Side)(x:endL p) : Per N:= -(room N x)-1
include H
lemma cast_f(x:endL p): flight_b N x=↑(N.val- (x.val+1)):=by rw [Nat.cast_sub (by omega),ZMod.natCast_self]; push_cast; unfold flight_b room; ring
lemma pre_val(x:endL p) : (room N x).val=x.val:=ZMod.val_natCast_of_lt (by omega)
lemma past_val(x:endL p) : (flight_b N x).val=N.val-(x.val+1):=by rw [cast_f H,ZMod.val_natCast_of_lt (by omega)]
lemma room_inj: Injective (room N (p:=p)):= by intro i j h; apply Fin.ext; rw [←pre_val H i,h,pre_val H j]
lemma flight_inj: Injective (flight_b N (p:=p)):=fun _ _ p=> room_inj H ((neg_inj).mp (sub_left_inj.mp p)) -- sub_right?
lemma stamp(x:endL p): (room N x).val+1 < N.val ∧ p.val ≤ (flight_b N x).val:=by rw [pre_val H, past_val H]; have h:=x.isLt; have hx:=p.property; omega
lemma apart_room(x y:endL p) : room N x≠ flight_b N y:=fun h=>by have hq:= (stamp H y).2; rw [←h,pre_val H] at hq; exact (not_le.mpr x.isLt) hq
omit H in
lemma peal: (-1:Per N)=↑(N.val-1):=by rw [Nat.cast_pred (show 0<N.val from N.property), ZMod.natCast_self,zero_sub]
lemma room_good (x:endL p): room N x≠ -1:=by
  intro h; have he:= (stamp H x).1; rw [h,peal, ZMod.val_natCast_of_lt] at he; all_goals have hx:=N.property; omega
abbrev Half (p:Side):= endL p × SpinIdx
lemma room_sides : Bijective (Sum.elim (room N (p:=p)) (flight_b N (p:=p))) := by
  constructor
  · rintro (x|x) (y|y) h; exact congrArg _ (room_inj H h); exact (apart_room H x y h).elim; exact (apart_room H y x h.symm).elim; exact congrArg _ (flight_inj H h)
  intro i; by_cases h:i.val<p.val; · exact ⟨Sum.inl ⟨_,h⟩,ZMod.natCast_zmod_val i⟩
  have he:=ZMod.val_lt i
  let x:endL p:=⟨N.val-(i.val+1),by omega⟩; refine ⟨Sum.inr x, (ZMod.val_injective N.val) ?_⟩
  change (flight_b N x).val=i.val; rw [past_val H,show x.val=N.val-(i.val+1) from rfl]; omega
noncomputable def rooms : (Half p⊕ Half p)≃ Stage N:= (Equiv.sumProdDistrib _ _ _).symm.trans (Equiv.prodCongr (Equiv.ofBijective _ (room_sides H)) (Equiv.refl SpinIdx))
omit H in
lemma nxt_room (x:endL p) : room N x +1= (↑(x.val+1) : Per N):=by rw [Nat.cast_add,Nat.cast_one]
lemma lower_gate(x:endL p): room N x=0↔ x.val=0:=by rw [← (ZMod.val_injective N.val).eq_iff,pre_val H, ZMod.val_zero]
lemma angel_gate(x:endL p): flight_b N x= -1 ↔ x.val=0:=by rw [←lower_gate H,flight_b,sub_eq_add_neg,add_eq_right]; simp
lemma root_beam(x y:endL p): (room N x +1=room N y)↔ y.val=x.val+1:=by rw [← (ZMod.val_injective N.val).eq_iff,nxt_room, ZMod.val_natCast_of_lt (by omega),pre_val H, eq_comm]
lemma mix_gate(x y:endL p): (room N x +1= flight_b N y) ↔ x.val+1=p.val ∧ y=x := by
  rw [← (ZMod.val_injective N.val).eq_iff, nxt_room, ZMod.val_natCast_of_lt (by omega), past_val H, Fin.ext_iff]; omega
lemma rev_gate(x y:endL p): flight_b N y+1= room N x ↔ x.val=0 ∧ y=x := by
  by_cases h:y.val=0
  · rw [(angel_gate H y).mpr h,neg_add_cancel, eq_comm,lower_gate H]; constructor; exact fun a=>⟨a,Fin.ext (h.trans a.symm)⟩; exact fun a=>a.1
  have he:¬(x.val=0 ∧ y=x):=fun ⟨g,e⟩=> h (by rw [e,g]); refine ⟨fun p=>?_ ,fun a=> (he a).elim⟩
  exfalso; have hP:=congrArg ZMod.val p; rw [cast_f H, show ((↑(N.val-(y.val+1)) : Per N)+1)=↑(N.val-(y.val+1)+1) from by push_cast; rfl, ZMod.val_natCast_of_lt (by omega),pre_val H] at hP; omega
omit H in
lemma map_gate(x y:endL p): flight_b N x+1=flight_b N y ↔ room N y+1=room N x:=by unfold flight_b; constructor<;>intro h <;>linear_combination (norm:=abel) h
-- block transform cup
omit H
abbrev hostV (p:Side)(x:Per N): Spin:=if x.val < p.val then 1 else Mir.pin 0
def ductU (p:Side)(N:Side) : UNI (Stage N):= ⟨diagonalS (hostV p),jump_unitary _ _ (fun i=> by unfold hostV; split_ifs; exact one_mem (unitary _); exact pin_U 0)⟩
abbrev funnel (p:Side)(X:Op (Stage N)) : Op (Stage N):= twist (ductU p N) X
include H
omit H in
lemma duct_b(x y: Per N)(A:Op (Stage N)):blockE x y (funnel p A)=hostV p x* blockE x y A * star (hostV p y):=by
  unfold funnel; rw [twist_formula,block_mul]; change (∑ j,blockE x j (diagonalS (hostV p) * A)*blockE j y (star (diagonalS _)))=_
  simp_rw [block_mul,Rift.block_star,diagonalS,block_jump,Equiv.refl_apply]; simp [apply_ite (Star.star),ite_mul,mul_ite]
lemma polar_room(x:endL p) : hostV p (room N x)=1:=by unfold hostV; rw [pre_val H, if_pos x.isLt]
lemma polar_f(x:endL p) : hostV p (flight_b N x)=pin 0:=if_neg (not_lt.mpr (stamp H x).2)
lemma portal_left(x y:endL p)(t:Three)(u v:ℝ): blockE (room N x) (room N y) (funnel p (timed (spread N u v t)))= blockE (room N x) (room N y) (timed (spread N u u t)) := by
  rw [duct_b,polar_room H,polar_room H]; simp only [one_mul,star_one,mul_one]; rw [time_block,time_block]; unfold spread ages; simp_rw [if_neg (room_good H x)];
lemma portal_seam (q:1<p.val)(x y:endL p)(w:Per N→Three): blockE (room N x) (flight_b N y) (funnel p (timed w)) = if x=y then (if x.val=0 then -minusS else if x.val+1=p.val then -plusS else 0) else 0:=by
  rw [duct_b,polar_f H,polar_room H,time_block, if_neg (apart_room H x y),add_zero,one_mul,pinS]; by_cases u:x=y
  · subst y; rw [if_pos rfl]; by_cases z:x.val=0
    · rw [if_pos z, if_pos ((rev_gate H x x).mpr ⟨z,rfl⟩),if_neg (by rw [mix_gate H x x]; omega),trunkZ,if_pos ((angel_gate H x).mpr z),zero_add,neg_one_smul,in_base]
    have hy:=iff_false_intro z; rw [if_neg z,if_neg (show ¬ flight_b N x+1 = room N x from by rw [rev_gate H x x]; simp [z]),add_zero]; by_cases t:x.val+1=p.val
    · rw [if_pos ((mix_gate H x x).mpr ⟨t,rfl⟩),if_pos t,trunkZ,if_neg (room_good H x),one_smul,in_top]
    rw [if_neg t,if_neg (by rw [mix_gate H x x]; simp [t]),zero_mul]
  rw [if_neg u,if_neg (by rw [mix_gate H]; simp [Ne.symm u]), if_neg (by rw [rev_gate H]; simp [Ne.symm u]),add_zero,zero_mul]
lemma neg_stamp(x:endL p): flight_b N x≠0:=by intro h; have he:= (stamp H x).2; rw [h,ZMod.val_zero] at he; exact (not_le.mpr p.property) he
lemma light_out(x y:endL p)(h: flight_b N x+1=flight_b N y): trunkZ (flight_b N x)=1:=by apply if_neg; intro hx; rw [hx,neg_add_cancel] at h; exact neg_stamp H y h.symm
lemma portal_right(x y:endL p) (t:Three)(u v:ℝ):blockE (flight_b N x) (flight_b N y) (funnel p (timed (spread N u v t)))= -(blockE (room N x) (room N y) (timed (spread N v v t))):=by
  rw [duct_b, polar_f H,polar_f H,pinS,time_block,time_block]; have hz(k): trunkZ (room N k)=1:= if_neg (room_good H k)
  have he:spread N u v t (flight_b N x)=spread N v v t (room N x):=by unfold spread ages; simp [neg_stamp H,angel_gate H,lower_gate H,room_good H]
  have hf: (if (flight_b N x+1=flight_b N y) then trunkZ (flight_b N x) • incoming else 0)= if room N y+1=room N x then incoming else 0:= by by_cases h:flight_b N x+1=flight_b N y<;> simp [ ← map_gate,h]; rw [light_out H _ _ h,one_smul]
  have hb: (if (flight_b N y+1=flight_b N x) then trunkZ (flight_b N y) • star incoming else 0)= if room N x+1=room N y then star incoming else 0:= by by_cases h:flight_b N y+1=flight_b N x<;> simp [ ← map_gate,h]; rw [light_out H _ _ h,one_smul]
  rw [hf,hb,hz,hz,mul_add,mul_add,add_mul,add_mul]; simp only [mul_ite,ite_mul,mul_zero,zero_mul,flip_fw,flip_bw,flip_spin,he,(flight_inj H).eq_iff,(room_inj H).eq_iff,one_smul]; split_ifs <;> abel
abbrev earth (u:ℝ)(t:Three):Op (Half p) := (timed (spread N u u t)).submatrix (fun x=> (room N x.1,x.2)) (fun x=> (room N x.1,x.2))
omit H
abbrev chargePort(p:Side)(x:endL p):Spin:= if x.val=0 then minusS else if x.val+1=p.val then plusS else 0
def pastT(p:Side):Op (Half p):=jump (Equiv.refl _) (chargePort p)
lemma charged(p:Side): pastT p*star (pastT p)=pastT p:=by
  unfold pastT; rw [jump_star,jump_mul,Equiv.refl_symm,Equiv.refl_trans]; congr 1; funext i; simp only [Equiv.refl_apply]; unfold chargePort; split_ifs
  · rw [minus_ok.isSelfAdjoint.star_eq, minus_ok.isIdempotentElem]
  · rw [plus_ok.isSelfAdjoint.star_eq,plus_ok.isIdempotentElem]
  simp
include H
lemma heart_coef (h:1<p.val)(u v:ℝ)(t:Three) : linkOp (earth (N:=N) u t) (earth (N:=N) v t) (pastT p) (pastT p) = ingot (rooms H) (funnel p (timed (spread N u v t))) := by
  let V:=timed (spread N u v t); let A:=pastT p; let X:=funnel p V; let R:=ingot (rooms H) X
  have hu(x y:endL p)(i j:SpinIdx) : R (Sum.inl (x,i)) (Sum.inr (y,j)) = (-(A*star A)) (x,i) (y,j) := by
    change blockE (room N x) (flight_b N y) (funnel p V) i j=_; rw [portal_seam H h x y]; unfold A; rw [charged]; unfold pastT chargePort; split_ifs <;> simp_all [jump_apply]
  have hsV : IsSelfAdjoint V:= time_self.add (diagonal_self _ (fun i=> phase_self _)); have hr:star R=R:=by unfold R X funnel; rw [← ingot_star,← map_star,hsV.star_eq]
  have hT:star (-(A*star A))= -(A*star A):=by rw [star_neg,star_mul,star_star]
  apply Eq.symm; ext (⟨x,i⟩|⟨x,i⟩) (⟨y,j⟩|⟨y,j⟩); -- tune
  · exact Matrix.ext_iff.mpr (portal_left H x y t u v) i j
  · exact hu x y i j
  · let X':=Sum.inl (β:=Half p) (y,j); let Y':=Sum.inr (α:=Half p) (x,i); change R Y' X'=(-(A*star A)) (x,i) (y,j); nth_rw 1 [←hr,←hT]; change star (R X' Y')=_; rw [show R X' Y'=_ from hu y x j i]; rfl
  exact Matrix.ext_iff.mpr (portal_right H x y t u v) i j
lemma sustain (h:1<p.val)(u v:ℝ)(t:Three)(h1:Safe (timed (spread N u v t)))(h2:Safe (timed (spread N u u t)))(h3:Safe (timed (spread N v u t)))(h4:Safe (timed (spread N v v t))): 0≤ energy (timed (spread N u u t))+energy (timed (spread N v v t))-energy (timed (spread N u v t))-energy (timed (spread N v u t)):= by
  let V(q v:ℝ):= linkOp (earth (N:=N) q t) (earth (N:=N) v t) (pastT p) (pastT p); let T(u v:ℝ):= timed (spread N u v t)
  have he(u v:ℝ)(y:Safe (T u v)): Safe (V u v) ∧ energy (V u v)=energy (T u v):=by unfold V; rw [heart_coef H h]; have ht:= y.twisted (ductU p N); refine ⟨safe_reindex _ _ ht,(energy_ingot _ _ ht).trans (energy_turn _ _ y)⟩
  let k:=he u v h1; have hr:=he v u h3; have hu:=he u u h2; have hv:=he v v h4
  change 0≤ energy (T u u)+energy (T v v)-energy (T u v)-energy (T v u); rw [←hu.2, ← hv.2, ←k.2,←hr.2]; linarith only [seam_ineq _ _ _ _ k.1 hu.1 hv.1,seam_ineq _ _ _ _ hr.1 hv.1 hu.1]
end YM.CF.Fixed.Rift
