import YM.CF.Gloss.Spin
set_option autoImplicit false
set_option synthInstance.maxSize 22000
noncomputable section
namespace YM.CF.Gloss
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Topology
open Function Fock Filter NormedSpace SU Lat Lattice Branch Cube Tenant MeasureTheory Phase Finset Mir Scroll Spire
attribute [local instance] opCStarAlgebra
variable {m B N:Side}
variable(B)(x:Era m)
lemma d1(a b:Site N)(s:Signed)(t:Site N)(i:Axis): delta1 N ((affine s t a) (s.perm i)) ((affine s t b) (s.perm i))=delta1 N (a i) (b i):=by
 unfold delta1 affine; simp only [Pi.add_apply, Signed.act_at,add_sub_add_right_eq_sub]; split; next h=> rw [show -(a i)- -(b i)= -(a i-b i) by abel,ZMod.natAbs_valMinAbs_neg]
 rfl
lemma oi(i:Axis)(p:Index m):OddAxis m (ρx x p (x.s.perm i))↔ OddAxis m (p i):=by
 let F(y:Index m):=(assembly (More m)).residue y; have he (q:Index m) (j:Axis) : OddAxis m (q j)↔ F q j=1:= Iff.rfl
 rw [he,he]; change (assembly (More m)).residue (x.s.act p+_) _=_ ↔_; rw [map_add,Ratio.root_embed,Ratio.residue_embed,add_zero]; cases l:x.s.flip i
 · change F (x.s.act p) _=_↔_; exact Eq.to_iff (congrArg (fun x=>x=1) ((congrArg (fun y:Per (GridN m)=>F (fun _=> y) i) (show x.s.act p (x.s.perm i)=p i by rw [Signed.act_at,l,if_neg (by decide)]))))
 have hp:x.s.act p (x.s.perm i)= -(p i):=by rw [Signed.act_at,l,if_pos rfl]
 have hg:F (x.s.act p) (x.s.perm i)=F (-p) i:=congrArg (fun y:Per (GridN m)=> F (fun _=>y) i) hp
 change F _ _=_ ↔_; rw [hg,show F (-p)= -F p from map_neg ..]; exact (show ∀ i: ZMod 2, -i=1↔i=1 by decide) _
lemma tx (a b:Index m): Fits m (ρx x a) (ρx x b) ↔ Fits m a b:=by
 have h(i:Axis): ρx x a (x.s.perm i)= ρx x b (x.s.perm i) ↔ a i=b i:=by change x.s.act a (x.s.perm i)+_ = x.s.act b (x.s.perm i)+_ ↔_; rw [add_left_inj,Signed.act_at,Signed.act_at]; split<;> simp
 unfold Fits; nth_rw 1 [x.s.perm.surjective.forall]; refine forall_congr' (fun i=> ?_); rw [h i,oi,oi,show delta1 _ (ρx x b (x.s.perm i)) (ρx x a (x.s.perm i))= _ from d1 b a x.s _ i]
lemma matB(a:Index m)(z:Site (Domain m B)): ψx B x z∈ room m B (ρx x a)↔ z∈room m B a:=by
 have ht(y:Index m)(v:Site (Domain m B))(i): roomX m B (y i) (v i) ↔ delta1 _ (v i) ((address m B y) i)≤broadface m B (y i):=by rw [address, high_here]; rfl
 simp_rw [room_mem,ht]; nth_rw 1 [x.s.perm.surjective.forall]; refine forall_congr' fun i=>?_ ; rw [tag_h,show delta1 _ (ψx B x z (x.s.perm i)) (ψx B x (address m B a) (x.s.perm i))=delta1 _ (z i) ((address m B a) i) from d1 z (address m B a) x.s _ i]
 simp [broadface,oi] -- field name
lemma pace_v (a:Index m)(z:Site (Domain m B))(t): ballot m B (ψx B x z) (ρx x a) t↔ ballot m B z a t:=by
 have hk (x:Index m) (z:Site (Domain m B)) (i) : elect m B (z i) t (x i) ↔ delta1 _ (z i) (address m B x i) ≤ radius m B (x i) t:=by rw [address,high_here]; rfl
 unfold ballot; simp_rw [hk]; nth_rw 1 [x.s.perm.surjective.forall]; refine forall_congr' fun i=>?_ ; rw [tag_h, show delta1 _ (ψx B x z (x.s.perm i)) (ψx B x (address m B a) (x.s.perm i))=delta1 _ (z i) ((address m B a) i) from d1 z (address m B a) x.s _ i]; simp [radius,oi]
lemma active_b(a:Index m)(z:Site (Domain m B)): ρx x a∈ active m B (ψx B x z) ↔ a∈active m B z:=by simp_rw [active_iff,pace_v]
lemma ηseq (a b:Site N)(s: Signed)(c: Site N):affine s c a-affine s c b=s.act a-s.act b:= by simp [affine]
lemma ξS(a b:Site (Domain m B)) (g: separation a b≤ B.val): lift (ψx B x a-ψx B x b)=x.s.act (lift (a-b)):=by
 rw [lift_eq_iff]
 constructor
 · rw [←wrap_signed,wrap_lift,Signed.act_sub,show ψx B x a-ψx B x b=x.s.act a-x.s.act b from ηseq a b x.s _]
 intro i; obtain ⟨i,rfl⟩:= x.s.perm.surjective i; rw [Signed.act_at]; have hu:=(component_le (a-b) i).trans g; have hm:= enough m B; have hB:= B.property; change ((lift (a-b) i).natAbs:ℕ)≤ B.val at hu; have hx:1≤B.val:=hB; split<;> omega
lemma armP(a b: Site (Domain m B))(g:separation b a ≤ B.val)(o:Lattice.Order)(U:Skin m B): travel (turnV B x U) a (march a b o)= (polarT x.charge) (travel U (ψx B x a) (march (ψx B x a) (ψx B x b) (orderEquiv x.s o))):=by
 rw [turnV,flashA,levity,ψX B x a]; change (polarT _) _ = _
 have he: List.map (·.rotate x.s) (march a b o)=march (ψx B x a) (ψx B x b) (orderEquiv x.s o):=by unfold march; rw [ξS B x b a g,send_route _ _ _ _ 0]; simp [affine]
 rw [ψX B x a] at he; rw [←he]; rfl
end YM.CF.Gloss
