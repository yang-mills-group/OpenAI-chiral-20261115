import YM.CF.DPress.FD.Tile.Curt
/-
 Frame : rows Nonnegative θ_a ≤ 1 times Group matrix; one row unscaled. equivalent to unit
 frame from fd-proof by 1/ℓ²(θ) rescaling. Max-normalization and sup HS give Lipschitz bounds
 independent of number of rows. Representatives are modulo right action. Need freeness to lift
 compatible face maps. -/
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.DPress.FD
open Function Set Metric Filter SU MeasureTheory
open scoped Topology BigOperators NNReal ENNReal Matrix.Norms.Frobenius Classical
attribute [local instance] Gauge.frobInner
abbrev Key := Op F
variable {I:Type*}[Fintype I]
namespace Row
abbrev rad:ℝ:= ‖(1:Key)‖
abbrev budget:= Set.Icc (0:ℝ) 1
def tilt:= (fun i:ℝ×E=> i.1 • fund i.2) '' (budget ×ˢ Set.univ)
def whole:= Set.range fund
lemma plant(U:E):fund U∈tilt:= ⟨(1,U),⟨⟨zero_le_one,le_rfl⟩,mem_univ _⟩,one_smul ℝ (fund U)⟩
lemma nil:(0:Key)∈ tilt:=⟨(0,1),⟨⟨le_rfl,zero_le_one⟩,mem_univ _⟩,zero_smul ..⟩
lemma bloom(U:E):‖fund U‖ = rad:=by rw [←mul_one (fund U),Gauge.mul_frob_eq _ _ (fund_U U).1] -- orient norm?
lemma spin_cost(U V:E):dist (fund U) (fund V)=dist U V:=rfl
lemma age {v:Key}(p:v∈tilt):‖v‖≤rad:=by obtain ⟨⟨x,f⟩,⟨⟨t,u⟩,l⟩,rfl⟩:=p; refine (norm_smul x (fund f)).trans_le ?_; change |x| *‖fund f‖ ≤ _; rw [bloom,abs_of_nonneg t]; exact mul_le_of_le_one_left (norm_nonneg _) u
lemma alive : 0 <rad:= norm_pos_iff.mpr one_ne_zero
lemma rise{g h:E} : dist g h ≤2*rad:=by rw [←spin_cost,dist_eq_norm]; exact (norm_sub_le ..).trans (le_of_eq (by rw [bloom,bloom,two_mul]))
@[fun_prop] lemma steady : Continuous fund:=SU.group.continuous_mat -- find
lemma closed_t:IsCompact tilt:= (isCompact_Icc.prod isCompact_univ).image (continuous_fst.smul (steady.comp continuous_snd))
lemma sap:IsCompact whole:=isCompact_range steady
lemma field {A B:Key}(p : A∈ tilt)(q:B∈ tilt):dist A B ≤2*rad:=by rw [dist_eq_norm]; exact (norm_sub_le ..).trans ((add_le_add (age p) (age q)).trans_eq (two_mul _).symm)
lemma acts_in {A:Key}(p:A∈ tilt)(u:E):A*fund u∈ tilt:=by obtain ⟨⟨x,v⟩,p,rfl⟩:=p; exact ⟨(x,v*u),⟨p.1,mem_univ _⟩,by rw [show (((fun i:ℝ×E=> i.1 • fund i.2) ((x,v*u):ℝ×E)))=x • (fund v*fund u) from rfl,Algebra.smul_mul_assoc] -- tune rew orientation
                                                ⟩
lemma dist_right (A B:Key)(u:E):dist (A*fund u) (B*fund u)=dist A B:=by rw [dist_eq_norm, ←sub_mul,Gauge.frob_mul_eq _ _ (fund_U u).2, dist_eq_norm]
lemma dist_left (A B:Key)(u:E):dist (fund u*A) (fund u*B)=dist A B:=by rw [dist_eq_norm, ←mul_sub,Gauge.mul_frob_eq _ _ (fund_U u).1, dist_eq_norm]
lemma nu {A:Key}(h:A∈tilt)(u v:E) : dist (A*fund u) (A*fund v) ≤ dist u v:=by
 obtain ⟨⟨x,w⟩,⟨⟨p,t⟩,_⟩,rfl⟩:=h; change dist ((x • fund w)*fund u) ((x • fund w)*fund v) ≤ _; rw [Algebra.smul_mul_assoc,Algebra.smul_mul_assoc,dist_smul₀,Real.norm_of_nonneg p,dist_left]; exact mul_le_of_le_one_left dist_nonneg t
lemma swell {A:Key}(u:A∈tilt){x:ℝ}(t:x∈budget) : x • A ∈ tilt:=by
 obtain ⟨⟨a,v⟩,⟨⟨p,q⟩,_⟩,rfl⟩:=u; exact ⟨(x*a,v),⟨⟨mul_nonneg t.1 p,mul_le_one₀ t.2 p q⟩,mem_univ _⟩,(smul_smul x a (fund v)).symm⟩
end Row
abbrev ArrayF(I:Type*):= I → Key
def sail(A:ArrayF I)(u:E):ArrayF I:= fun i=> A i*fund u
abbrev Frame (I:Type*): Set (ArrayF I):= {x| (∀ i,x i∈ Row.tilt) ∧ ∃ i,x i ∈ Row.whole}
namespace Frame
variable {A B C:ArrayF I} {u v:E}
open Row
lemma pact (I:Type*)[Fintype I] : IsCompact (Frame I):=by
 change IsCompact ({x:ArrayF I|∀ i,x i ∈ Row.tilt} ∩ {x|∃ i, x i∈ Row.whole}); refine (isCompact_pi_infinite (fun _:I=> closed_t)).inter_right ?_; simp_rw [setOf_exists]; exact isClosed_iUnion_of_finite fun i=> sap.isClosed.preimage (continuous_apply i)
lemma fog (p:A∈Frame I):‖A‖≤ rad:=(pi_norm_le_iff_of_nonneg alive.le).mpr fun i=> age (p.1 i)
lemma uniform (p:A∈Frame I)(g:B∈Frame I):dist A B≤2*rad:=(dist_pi_le_iff (mul_nonneg (by norm_num) alive.le)).mpr fun i=> field (p.1 i) (g.1 i)
lemma stays(p:A∈Frame I)(u:E):sail A u∈ Frame I:=⟨fun i=> acts_in (p.1 i) u,by obtain ⟨i,v,q⟩:= p.2; exact ⟨i,v*u,by rw [fund_mul,q,sail]⟩⟩
lemma sail_id (A:ArrayF I):sail A 1=A:=funext fun i=>mul_one (A i)
lemma sail_mul (A:ArrayF I)(u v:E):sail (sail A u) v=sail A (u*v):= funext fun i=> mul_assoc (A i) _ _
lemma sail_L(A B:ArrayF I)(u:E):dist (sail A u) (sail B u)=dist A B:=by
 apply le_antisymm; · exact (dist_pi_le_iff dist_nonneg).mpr fun i=> (dist_right ..).trans_le (dist_le_pi_dist A B i)
 exact (dist_pi_le_iff dist_nonneg).mpr fun i=> (dist_right (A i) (B i) u).symm.trans_le (dist_le_pi_dist (sail A u) (sail B u) i)
lemma sail_R(p:A∈Frame I)(u v:E):dist (sail A u) (sail A v)=dist u v:=by
 refine le_antisymm ((dist_pi_le_iff dist_nonneg).mpr fun i=> nu (p.1 i) u v) ?_; obtain ⟨i,w,h⟩:=p.2; exact le_of_eq_of_le (show dist u v=dist (sail A u i) (sail A v i) from (by unfold sail; rw [←h,dist_left]; rfl)) (dist_le_pi_dist ..)
-- puzzle.P choose.W. All
lemma piece (p:A∈Frame I)(t:sail A u=sail A v):u=v:= dist_eq_zero.mp (by rw [←sail_R p,t,dist_self])
lemma move_cost (q:B∈Frame I)(u v:E):dist (sail A u) (sail B v) ≤ dist A B+dist u v:= (dist_triangle _ (sail B u) _).trans_eq (by rw [sail_L,sail_R q])
abbrev Fits(p:ℝ)(A B:ArrayF I):Prop:=∃ u:E,dist (sail A u) B≤p
lemma transpose {p:ℝ}(u:Fits p A B):Fits p B A:=by obtain ⟨v,t⟩:=u; refine ⟨v⁻¹,?_⟩; rw [← sail_L (sail B _) A v,sail_mul,inv_mul_cancel,sail_id, dist_comm]; exact t
lemma triangle {p q:ℝ}(u:Fits p A B)(t:Fits q B C): Fits (p+q) A C:=by obtain ⟨a,h⟩:=u; obtain ⟨b,g⟩:= t; refine ⟨a*b,?_⟩; rw [←sail_mul]; refine (dist_triangle _ (sail B b) _).trans ((add_le_add ?_ g)); rw [sail_L]; exact h
lemma aloof (u:ℝ) : IsClosed {x:ArrayF I× ArrayF I| Fits u x.1 x.2}:=by
 let S : Set ((ArrayF I × ArrayF I) × E):= {v|dist (sail v.1.1 v.2) v.1.2 ≤ u}; have hp:IsClosed S:=isClosed_le (by unfold sail; fun_prop) continuous_const
 have he: {x:ArrayF I× ArrayF I| Fits u x.1 x.2}= Prod.fst '' S:=by
    ext i; simp [S,Fits]
 rw [he]; exact isClosedMap_fst_of_compactSpace _ hp
end Frame
end YM.CF.DPress.FD
