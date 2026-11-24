import YM.CF.Gloss.Aid
set_option autoImplicit false
set_option synthInstance.maxSize 22000
noncomputable section
namespace YM.CF.Gloss
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Topology
open Function Fock Filter NormedSpace SU Lat Lattice Branch Cube Tenant MeasureTheory Phase Finset Mir Scroll Spire
attribute [local instance] opCStarAlgebra
variable {m B N:Side}
variable(B)(x:Era m)
def doveL(b:Bool): Vect →ₗᵢ[ℝ] Vect:={
 toFun:=dove b,
 map_add':= fun x y=> by
   have ht:dove b (0:Vect)=0:= norm_le_zero_iff.mp (by rw [doveN,norm_zero]); have hp:dove b (-y)= -dove b y:=by have hf:= dove_sub (0:Vect) y b; rwa [zero_sub,ht,zero_sub] at hf
   have he:=dove_sub x (-y) b; rwa [hp,sub_neg_eq_add,sub_neg_eq_add] at he
 map_smul':=fun c p=>by rw [RCLike.real_smul_eq_coe_smul (K:=ℂ),dove_scale]; change cSignX b (c:ℂ) • _ = _; rw [show cSignX b (c:ℂ)=(c:ℂ) by cases b <;> simp [cSignX]]; exact (RCLike.real_smul_eq_coe_smul ..).symm
 norm_map':= fun v=> doveN .. }
lemma feval(u:Bool)(x y:Vect):inner ℝ (dove u x) (dove u y)=inner ℝ x y:=(doveL u).inner_map_map _ _
lemma lamp_p(n:ℝ)(b:Bool)(L:List Vect)(w:Vect): restrain n (L.map (dove b)) (dove b w)=dove b (restrain n L w):=by
 induction L generalizing w with
 | nil=>rfl
 | cons a c ih=> simp only [restrain,List.map_cons,ih,shave,dove_sub,feval,doveN]; rw [show ∀ r:ℝ, ∀ x:Vect,dove b (r • x)=r • dove b x from fun r x=> (doveL b).map_smul r x]
abbrev ρi(x:Era m):Equiv.Perm (Spot m):=(ρx x).prodCongr (Equiv.refl _)
abbrev ρr(x:Era m):Equiv.Perm (Ramp m):=(ρi x).prodCongr (orderEquiv x.s)
def αRow (x:Era m)(s: ArrayF m):ArrayF m:=fun i=>doveV x.charge (s (ρi x i))
lemma px_p (a c:Spot m): Prev m (ρi x a) (ρi x c) ↔ Prev m a c:=by change Fits _ (ρx _ _) (ρx _ _)∧ a.2≤c.2 ∧ _ ↔ _; unfold Prev; rw [tx,show ρi _ _≠ρi _ _ ↔ a≠c from (ρi x).injective.ne_iff]
lemma sail (b:Spot m)(Q: Phase.Zone)(L:List (Ramp m)): L.map (ρr x)∈ permits m (ρi x b) Q ↔ L∈ permits m b Q:=by
 have ht(L)(b:Spot m): Moves m (ρi x b) (List.map (ρr x) L)↔Moves m b L:=by induction L generalizing b with| nil=>rfl | cons a c ih=> rw [List.map_cons,Moves]; change Prev _ (ρi x _) _ ∧ _↔ _; rw [px_p]; exact and_congr_right fun h=> ih a.1
 simp only [permits_iff,ht,InRows,List.forall_mem_map]; rfl
lemma dove_runV(b:Bool)(x:E)(w:Vect): turn (polarT b x) (dove b w)= dove b (turn x w):=by unfold turn; rw [dove_acts, show fund (polarT _ _) = _ from polar_val b x]
lemma prep_w (U:Skin m B)(t:ArrayF m)(b:Spot m)(L:List (Ramp m))(p:Moves m b L): train m B (turnV B x U) (αRow x t) b.1 L=(train m B U t (ρx x b.1) (L.map (ρr x))).map (dove x.charge):=by
 induction L generalizing b with
 | nil=>rfl
 | cons i L ih=>
    obtain ⟨a,q⟩:=i; rw [train,List.map_cons,List.map_cons,show ρr x (a,q)=(ρi x a, orderEquiv x.s q) from rfl,train,ih a p.2]; let y:= parcel m B U (ρx x b.1) (ρx x a.1) (orderEquiv x.s q); have hk: parcel m B (turnV B x U) b.1 a.1 q=polarT x.charge y:=by unfold parcel y; rw [armP B x _ _ ((separation_comm ..).trans_le (chain_near p.1.1 B)),←tag_h,←tag_h]; rfl
    rw [hk]; simp only [List.map_cons,List.map_map]; apply congrArg₂; · exact dove_runV ..
    apply List.map_congr_left; intro _ _; exact dove_runV ..
lemma cashF (U:Skin m B)(t:ArrayF m)(b:Spot m)(L:List (Ramp m))(p:Moves m b L): rateF m B (turnV B x U) (αRow x t) b L=rateF m B U t (ρi x b) (L.map (ρr x)):=by unfold rateF; rw [prep_w B x U t b L p,show (αRow x t b).val=dove x.charge _ from rfl,lamp_p,doveN]; rfl -- tune αRow
lemma permitx (a:Spot m)(r: Phase.Zone): (permits m a r).image (List.map (ρr x))=permits m (ρi x a) r:=by
 ext i; rw [mem_image]; constructor; rintro ⟨a,p,rfl⟩; exact (sail ..).mpr p
 intro g; have hp : List.map (ρr x) (i.map (ρr x).symm)=i:=by rw [List.map_map, Equiv.self_comp_symm,List.map_id]
 exact ⟨_,(sail x a r _).mp (hp.symm ▸ g),hp⟩
lemma ν_k(U:Skin m B)(t:ArrayF m)(b:Spot m)(r: Phase.Zone):fundF m B (turnV B x U) (αRow x t) r b=fundF m B U t r (ρi x b):=by
 unfold fundF; rw [←permitx,prod_image]; exact prod_congr rfl (fun i u=> by rw [cashF B x U t b i (permits_iff.mp u).1]); exact fun _ _ _ _ p=> (List.map_injective_iff.mpr (ρr x).injective) p -- tune
lemma β(U:Skin m B)(t:ArrayF m)(r: Phase.Zone): Verified m B margin (turnV B x U) (αRow x t) r ↔ Verified m B margin U t r:=by
 have he(b:Spot m) : Check m B margin (turnV B x U) (αRow x t) r b↔ Check m B margin U t r (ρi x b):=by
    unfold Check; rw [←permitx,Finset.forall_mem_image]; apply forall₂_congr fun L u=> by change margin < rateF _ _ _ _ _ _ ↔ margin < rateF _ _ _ _ _ _; rw [cashF B x U t b L (permits_iff.mp u).1]
 unfold Verified; simp_rw [he]; nth_rw 2 [(ρi x).surjective.forall]; rfl
lemma voxel(e:ℝ)(u:Pack m B)(p:u∈payer m B e): vest B x u∈payer m B e:=⟨ζx_o B x _ u.1 p.1,(β B x u.1 (slot m u.2) _).mpr p.2⟩
end YM.CF.Gloss
