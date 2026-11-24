import YM.CF.Dial.Snow
set_option autoImplicit false
set_option synthInstance.maxSize 8000
noncomputable section
namespace YM.CF.Dial
open Function Filter Lattice Laurent Bloch Next.Free Metric Lat Finset Branch Cube Tenant SU Rush Drapes Fir Tulip Fock Peaks
open scoped Topology Matrix MatrixOrder BigOperators Matrix.Norms.L2Operator Kronecker InnerProductSpace
attribute [local instance] opCStarAlgebra
variable {ι:Type*}{L:Side}{ho:Odd L.val}{P A K:Chop ι}
-- generic occupied on output B, know exact compression on real charts
structure  Land (L: Side)(P A K:Chop ι) : Prop where
 lay : BoxD L (false,true) (false,true) P
 deck : BoxD L (false,true) (true,true) A
 treasury : BoxD L (true,true) (false,true) K
 jet : ∀ i {N F: Side}(G: Ratio N F),G.count=L→ P i G (vacancyY N F)*helmC G=helmC G *cc (P i G (vacancyY N F)) ∧ A i G (vacancyY N F)*helmC G=helmC G *cc (A i G (vacancyY N F))
 sky : Still L fun G U=>∀ i,
    let B:=P i G (post U); let H:=A i G (post U); IsStarProjection B∧ B*H=H ∧ H*K i G (post U)=B
namespace BoxD
lemma corner {P S:Chop ι}{u:AxisT}(h:BoxD L u u P)(p:BoxD L u (upright u) S): BoxD L u (upright u) (fun i _ _ G x=> P i G x*S i G x*cc (P i G (chargeB x))):=(h.chain p).chain h.abrade
lemma strangle {P S:Chop ι}{u:AxisT}(h:BoxD L u u P)(p:BoxD L u (upright u) S): BoxD L u (upright u) (fun i _ _ G x=> P i G x*S i G x*cc (P i G (chargeB x))+(1-P i G x)*S i G x*(1-cc (P i G (chargeB x)))):=by
  have he:= (BoxD.one.sub h).corner p
  simp only [cc_sub,cc_one] at he; exact (h.corner p).add he
end BoxD
def soar (P A:Chop ι):Chop ι:=fun i _ _ G x=> A i G x*squareD G true x*(A i G x)ᵀ+(1-P i G x)*squareD G false x*cc (1-P i G (chargeB x))
abbrev TickZ := ↥(Set.Icc (0:ℝ) 1)
def laneC (P A:Chop ι): Chop (ι× TickZ):=fun i _ _ G x=> (1-(i.2.val:ℂ)) • squareD G false x+ (i.2.val:ℂ) • soar P A i.1 G x
def zL (P A:Chop ι) : Chop (ι × TickZ):=fun i _ _ G x=>
 let S:=P i.1 G x; let V:=P i.1 G (chargeB x); let Y:=laneC P A i G x
 S*Y*cc V + (1-S)*Y*(1-cc V)
lemma lane_at (P A:Chop ι)(i:ι){N F:Side}(G:Ratio N F)(x:Sew N F)(t:TickZ):
 laneC P A (i,t) G (post x)=straightC (P i G (post x)) (squareD G true (post x)) (squareD G false (post x)) (A i G (post x)) t.val:=by rw [laneC,straightC,victory,soar,charge_p]; rfl
lemma zL_at (P A: Chop ι)(i:ι){N F:Side}(G:Ratio N F)(x:Sew N F)(t:TickZ): zL P A (i,t) G (post x)= stage (P i G (post x)) (laneC P A (i,t) G (post x)):=by unfold zL stage body; simp only [charge_p,cc_sub,cc_one]
namespace Land
variable (h: Land L P A K)
include h
lemma loft (ho:Odd L.val): BoxD L (false,true) (false,false) (soar P A):= by
  have ht:= ((h.deck.chain (tablesB _ true L ho)).chain h.deck.tail); exact ht.add ((BoxD.one.sub h.lay).corner (tablesB _ false L ho))
lemma crown (ho:Odd L.val): BoxD L (false,true) (false,false) (laneC P A):=by
  have ht:= tablesB (ι×TickZ) false L ho; have hx: ∀ i:ι × TickZ, ‖1-(i.2.val:ℂ)‖ ≤1 :=by intro i; rw [← Complex.ofReal_one, ←Complex.ofReal_sub, Complex.norm_real,Real.norm_of_nonneg (sub_nonneg.mpr i.2.property.2)]; exact sub_le_self _ i.2.property.1
  have hv: ∀ i:ι × TickZ, ‖(i.2.val:ℂ)‖≤1:=by intro i; rw [Complex.norm_real,Real.norm_of_nonneg i.2.property.1]; exact i.2.property.2
  exact (ht.scale _ _ hx).add (((h.loft ho).reindex (fun x:ι×TickZ=>x.1)).scale _ _ hv)
lemma zL_budget(ho:Odd L.val): BoxD L (false,true) (false,false) (zL P A):=( (h.lay.reindex (fun x:ι×TickZ=>x.1)).strangle (h.crown ho))
lemma helper(ho:Odd L.val): BoxD L (false,false) (false,true) (fun (i:ι×TickZ) _ _ G x=> (zL P A i G x)⁻¹) ∧ Interest L (zL P A):=by
  obtain ⟨M,g,T⟩:=h.treasury.assets; obtain ⟨k,H⟩:= (h.sky.plus T.gilded).stamp
  apply ocean (h.zL_budget ho) ((max M 1)*(max M 1)) (k:=k); rintro ⟨i,t⟩ N F G hG hv
  let B:=vacancyY N F; let Z:Sew N F:=(1,vacuumW F,vacuumW N)
  obtain ⟨hY,q⟩:= H G hG hv; have ⟨hc,hQ,hb⟩:= hY i; have ⟨hl,hA⟩:= h.jet i G hG
  have ht: zL P A (i,t) G B=stage (P i G B) (straightC (P i G B) (squareD G true B) (squareD G false B) (A i G B) t.val):=by unfold B vacancyY; rw [zL_at,lane_at]
  rw [ht]; exact win (N:=A i G B) (P:=P i G B) (K:=K i G B) hc hQ hb ((q i).trans (le_max_left ..)) (le_max_right ..) (unit_square G false Z) (by rw [helm_eq]; exact hl) (by rw [helm_eq,helm_eq]; exact hA) (unit_square G true Z) t.property.1 t.property.2
end Land
end YM.CF.Dial
