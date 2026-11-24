import YM.CF.BProof.Wick.Bits
import YM.CF.Fock.Glacier
import YM.CF.Pastry.Works
/-! Graded CAR site algebra. Compare transfers out of the site vacuum; this
fixes all signs in the tensor prescriptions even on vectors not in site-grade zero. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BProof.Garden
open Function Filter Fock NormedSpace Finset Align Wick
open scoped Topology Matrix MatrixOrder InnerProductSpace Kronecker BigOperators Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
variable {I:Type*}[Fintype I][LinearOrder I]{A B: FC I} {a:Bool}{S T p q: Finset I}
lemma scope (x: Sector S a A)(h:S⊆T): Sector T a A:=by
 induction x with
 | zero=> apply Sector.zero
 | one=> exact Sector.one
 | up _ hh=> exact Sector.up _ (h hh)
 | down _ hh=> exact Sector.down _ (h hh)
 | add _ _ i j=> exact i.add j
 | mul _ _ i j=> exact i.mul j
 | scale _ _ i=> exact i.scale _
lemma council (x:Sector S false A)(y:Sector T a B)(h:Disjoint S T): Commute A B:= by simpa [Commute,SemiconjBy,Sector.grainB] using Sector.apart x y h
abbrev berth (S:Finset I): FC I:= cabin ∅ S
lemma berth_idp : berth S * berth S = berth S := (cabin_proj ..).isIdempotentElem
@[simp] lemma berth_self : star (berth S)=berth S:=(cabin_proj ..).isSelfAdjoint
lemma berth_stays : Sector S false (berth S):= tagged (empty_subset _) Subset.rfl
lemma berth_basis (S T:Finset I): acts (berth S) (basisKet T)=if Disjoint S T then basisKet T else 0:=by simp only [berth,cabin_basis,permit_rule,empty_subset,true_and]
@[simp] lemma berth_vac :acts (berth S) (vacuum I)=vacuum I:=by simp [vacuum,berth_basis]
theorem berth_test (x:Sector S false A)(y:Sector S false B) (u:acts A (vacuum I)=acts B (vacuum I)): A*berth S = B*berth S:=by
 have he(t:Finset I)(g:Disjoint S t) : acts A (basisKet t)=acts B (basisKet t):=by
   induction t using Finset.induction_on with
   | empty=> exact u
   | insert i t k ih=>
     rw [←singleton_union] at g; have ht:= (disjoint_union_right ..).1 g -- tune
     apply smul_right_injective (Wave I) (show parity i t≠0 from by unfold parity; exact pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)); dsimp only; rw [← map_smul,←map_smul, ←(put_act i t|>.trans (if_neg k)),←act_mul, ←act_mul,(council x (Sector.up i (mem_singleton_self i)) ht.1).eq,(council y (Sector.up i (mem_singleton_self i)) ht.1).eq,act_mul,act_mul,ih ht.2]
 apply op_columns; intro i; rw [act_mul,act_mul,berth_basis]; split; exact he _ ‹_›; simp only [map_zero]
def zone (S:Finset I) (x:Wave I):Prop:=∀ i: Finset I, ¬ i⊆ S → x.ofLp i=0
lemma homeZone (h:Sector S a A): zone S (acts A (vacuum I)):=by
 intro i hi; rw [vacuum,basis_act]; contrapose! hi; exact fun j hj=> by_contra fun v=> notMem_empty j ((h.dotGrade i ∅ hi j v).2 hj)
lemma sideSlot (d:Disjoint p q){x:Wave I}(v:zone (p∪q) x) : acts (cabin p q) x = x.ofLp p • basisKet p:=by
 apply PiLp.ext; intro i; rw [cabin,cut_apply]; by_cases h:i=p
 · subst i; simp [d.symm]
 by_cases g:i∈permit p q; · obtain ⟨a,b⟩:= (permit_rule ..).mp g; rw [if_pos g,v]; simp [h]; intro k; apply h; apply Subset.antisymm _ a; exact fun j he=> (mem_union.mp (k he)).resolve_right (fun l=>disjoint_left.mp b l he)
 rw [if_neg g]; simp [h]
lemma berth_iso (h:Sector S false A)(x:A*berth S=A)(p:‖acts A (vacuum I)‖=1) : star A*A=berth S:=by
 have he: acts (star A*A) (vacuum I)=(1:ℂ) • vacuum I:=by
   let k:=vacuum I; let Q:=star A*A; let v:=acts Q k; have hl:acts (berth S) v=v:=by unfold v Q; rw [←act_mul, ←mul_assoc,←berth_self,←star_mul,x]
   have h': zone S v:=homeZone (show Sector S false Q from h.contr.mul h); have hy:=sideSlot (p:=∅) (q:=S) (Finset.disjoint_empty_left S) (show zone (∅∪S) v from by rwa [empty_union]); change v=_
   have h1:v.ofLp ∅=1:=by
     rw [← basis_inner]; change inner ℂ k v=_; unfold v Q k; rw [act_mul]; rw [← act_inner]; rw [star_star,inner_self_eq_norm_sq_to_K,p]; simp
   exact (hl.symm.trans hy).trans (by rw [h1])
 have hm: Sector S false (star A*A):= h.contr.mul h; have hh:= berth_test hm (B:=1) Sector.one (by rw [he,one_smul,act_one]); rwa [mul_assoc,x,one_mul] at hh
lemma stampCost (h:IsStarProjection A): ‖A‖≤1:=by
 have he:star A*A=A:=by rw [h.isSelfAdjoint.star_eq,h.isIdempotentElem]
 have hf:‖A‖= ‖A‖*‖A‖ := (congrArg norm he.symm).trans CStarRing.norm_star_mul_self
 nlinarith
lemma payPut (i:I):‖put i‖≤1:=by have ht:= Pastry.tag_size ({i}:Finset I); rw [Pastry.poke,Pastry.Poly.tag_once] at ht; exact ht
lemma cabin_spin {U: UNI I}(h:Disjoint p q)(g:Commute U.val (cutM p))(e:Commute U.val (cutM q)) : twist (quantU U) (cabin p q)=cabin p q:=by
 let k:= quantU U; have hd(t:ℂ)(ht:t≠0) : twist k (grab p q t)=grab p q t:=by
   have hc:U.val*offerP p q t=offerP p q t*U.val:=by unfold offerP space; simp only [mul_add,add_mul,mul_sub,sub_mul,mul_one,one_mul,Algebra.mul_smul_comm, Algebra.smul_mul_assoc,g.eq,e.eq]
   have hp:twist U (offerP p q t)=offerP p q t:=by rw [twist_formula,hc,mul_assoc,U.property.2,mul_one]
   rw [← contracts ht h,twist_scalar,← quant_twist,hp] -- tune k
 have hx:twist k (grab p q 0)=grab p q 0:= tendsto_nhds_unique_of_eventuallyEq (((breeze k).comp (coals p q)).continuousWithinAt (x:=0) (s:={0}ᶜ)) ((coals p q).continuousWithinAt (x:=0)) (by filter_upwards [self_mem_nhdsWithin] with u hu; exact hd _ hu)
 rw [permit_spec] at hx; exact hx
end YM.CF.BProof.Garden
