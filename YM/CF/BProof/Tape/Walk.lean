import YM.CF.BProof.Tape.Arc
/-! construction of Ride/c-bra for given fields, before geometry substitutions; including
all gauge hypotheses on any such arguments, including Book. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BProof.Tape
open Function Filter Fock Finset Branch Stint Align Wick Hearth Spin Tenant Lat Lattice Tulip Cube Fig
open scoped Topology BigOperators InnerProductSpace Matrix MatrixOrder Matrix.Norms.L2Operator Classical Hearth
attribute [local instance] opCStarAlgebra
variable {j:ℕ}{a b l r δ c v η:ℝ}{N:Side}{P: Ready j a b l r}{F:Core j a b l r N} (h: Age P F δ)
def Honor (P:Ready j a b l r)(F:Core j a b l r N)(d:ℝ) : Prop := Age P F d ∧∀ U:Counter (More N) d, ‖F.wind U.val‖≤ 1/2
abbrev Shed (F:Core j a b l r N)(d c v:ℝ):= InRoad F d c × Skein N v
def path (x:Shed F δ c v)(k:Key):=week x.2.val k
def dream (F:Core j a b l r N)(δ c v η:ℝ)(x:Shed F δ c v):Prop := let U:=x.1.val.1.val; let S:=x.1.val.2; Ride (F.upright U) (F.wind U) (path x (true,false)) (path x (false,false)) (path x (true,true)) (path x (false,true)) (bandCut S true) (bandCut S false) c η
abbrev Loft (F:Core j a b l r N)(δ c v η:ℝ):= {x:Shed F δ c v // dream F δ c v η x}
-- control all terms of Dream at transformed locales
private lemma shelf_t (g:UNI (Single N)){A C:Op (Single N)}(p:Shelf A C η): Shelf (twist g A) (congrC g C) η:=by
 let X:= twist g A; have hp:IsStarProjection X:= ⟨(by change X*X=X; unfold X; rw [←map_mul,p.proj.isIdempotentElem]),(by change star _=_; unfold X; rw [←map_star,p.proj.isSelfAdjoint])⟩
 have hf:congrC g ((1-A)*C*cc A)=(1-X)*congrC g C*cc X:= by
    unfold X; rw [show 1-twist g A= twist g (1-A) from (by rw [map_sub,map_one]),cc_twist]
    rw [congr_form,congr_form,twist_formula,twist_formula]; let h:star g.val*g.val=1:=g.property.1; let u:star (ccU g).val*(ccU g).val=1:=(ccU g).property.1; simp only [mul_assoc]; rw [←mul_assoc (star g.val),h,one_mul,←mul_assoc (star (ccU g).val),u,one_mul]
 refine ⟨hp,val_con _ ⟨_,p.unit⟩,skew_form p.sym,?_,p.lid⟩; change ‖(1-X)*_ *cc X‖≤_; rw [← hf, congr_norm]; exact p.fee
private lemma inv_tw (g:UNI (Single N))(A:Op (Single N)): (twist g A)⁻¹=twist g A⁻¹:=by
 by_cases h:IsUnit A
 · exact Matrix.inv_eq_right_inv (by rw [←map_mul,(live h).1,map_one])
 have hx:¬IsUnit (twist g A):= fun p=> h ((twist_inv g A) ▸ (p.map (twist (star g)).toRingEquiv)) -- tune
 simp_rw [Matrix.nonsing_inv_eq_ringInverse,Ring.inverse_non_unit _ hx,Ring.inverse_non_unit _ h,map_zero]
private lemma land_t (g:UNI (Single N))(A P:Op (Single N)): twist g (land A P)= land (twist g A) (twist g P):=by unfold land send entered; simp only [map_add,map_sub, map_mul,map_one,map_star, ← inv_tw]
private lemma floor_t (g:UNI (Single N))(A P Q:Op (Single N))(s:ℝ): twist g (floorH A P Q s)= floorH (twist g A) (twist g P) (twist g Q) s:=by unfold floorH house wedgeQ wedgeP space; simp only [land_t,map_add,map_mul, map_sub,map_one,map_smul]
def vacuum (h: Age P F δ)(v c:ℝ) := Skein.hall (h.beam c) v
lemma dream_t (g:Geometry N){x:Shed F δ c v}(p:dream F δ c v η x):dream F δ c v η ((vacuum h v c).st.drive g x):=by
 let s:=vacuum h v c; let U:=tradew N g; let y:=s.st.drive g x; let f:= x.1.val.1; let Y:=y.1.val.1; let A:=F.upright f.val; let T:= F.wind f.val; let hp: Ride A T _ _ _ _ _ _ c η:=p
 have hA:F.upright Y.val=twist U A:= (P.mat N h.minN F.M δ h.shelter).cov.frame g f
 have hT:F.wind Y.val=twist U T:=(F.earnsWind P h.minN h.shelter).cov.frame g f
 let P (s: Bool):=bandCut x.1.val.2 s; have hs(s:Bool):P s=twist U (P s):=by rw [twist_formula, (blockG x.1.val.2 g s).symm.eq,mul_assoc,U.property.2,mul_one]
 have hl(u:ℝ): rug (F.upright Y.val) (F.wind Y.val) u= twist U (rug A T u):=by rw [hA,hT]; unfold rug; simp only [land_t,slit,Align.bend,map_mul,map_add,map_smul,map_one]
 have he(u): floorH (F.θ Y.val 1) (P true) (P false) u= twist U (floorH (crownP A T) (P true) (P false) u):=by rw [floor_t,←hs,←hs,show F.θ Y.val 1=_ from (hl 1)] -- tune
 have hw (k:Key)(u:ℝ): path y k u=congrC U (path x k u):= Skein.weekSpin ..
 have hb:BoardH F Y.val x.1.val.2 c:= y.1.property; have hg: F.θ Y.val 1=crownP (F.upright Y.val) (F.wind Y.val):=rfl
 have hk(u:ℝ)(t:u∈walking):Shelf (floorH (F.θ Y.val 1) (P true) (P false) 0) (path y (false,false) u) η:=by rw [hw,he]; exact shelf_t U (hp.pores u t)
 refine ⟨F.leaning _ _ h.minN h.shelter Y.property, hb,?_,?_,?_,hk,?_,?_, (Eq.trans (congrArg (‖·‖) hT) (twist_norm U T)).trans_le hp.small⟩ -- small mismatch
 · intro t p; change Shelf (rug (F.upright Y.val) (F.wind Y.val) t) (path y (true,false) 0) η; rw [hl,hw]; exact shelf_t U (hp.rails t p)
 · intro t p; change Shelf (rug (F.upright Y.val) (F.wind Y.val) 1) (path y (true,false) t) η; rw [hl,hw]; exact shelf_t U (hp.fires t p)
 · intro u z; change Shelf (floorH (F.θ Y.val 1) (P true) (P false) u) (path y (true,false) 1) η; rw [hw,he]; exact shelf_t U (hp.sails u z)
 · change path y (true,false) 1=path y (false,false) 0; rw [hw,hw,hp.grips]
 exact ⟨hb,cut_real _, cut_real _, pairCom ..,pairCom .., hk _ walk1⟩ -- tune
end YM.CF.BProof.Tape
