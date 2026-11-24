import YM.CF.BProof.Bias.Stack
/-! Exercise forced separation at any gap i. Only even micro distances between chosen
 slices; no rounding escape. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BProof.Bias
open Function Filter Fock Finset Branch Tenant Cube SU Tulip Lat Lattice Dial Spin Fig Align Stint Wick Hearth
open Fir Laurent Rush Bloch Next.Free BZ Real Mapping Angular Hero Dream Trek
open scoped Topology BigOperators Matrix MatrixOrder InnerProductSpace Kronecker Matrix.Norms.L2Operator Classical
attribute [local instance] opCStarAlgebra
variable {N:Side}(Y:Yard (More N))(i:Y.Index) {a m t x:ℕ}
abbrev pairsZ (a b:ℕ) := 2*a+2*b+2
lemma port_sheet (m t:ℕ)(e:2*m<Y.long)(x:ℕ)(hx:Y.short<x)(v:x≤m): ∃ d∈StackS Y,(d+x:Per N)∈StackS Y ∧ (d∈bright Y ↔ (d+x: Per N)∉bright Y) ∧ cent d t⊆area Y i (pairsZ m t) ∧ cent (d+(x:Per N)) t ⊆area Y i (pairsZ m t):=by
 let u:= Y.v i; let V:=Y.long; let Z:=Y.short; obtain ⟨w,l,g,H⟩:=nearest u; have ht:=Y.long_pos; have hl:l≤V:=g.trans ht; have h2:Z+l≤2*x:=by unfold Z; omega
 let a:=V-l; let b:=2*x-(Z+l); have hv:a<V+1:=Nat.lt_succ_of_le (Nat.sub_le ..); have hb:b≤ V:=by unfold b V; omega
 have hu:instant w= Y.u i+(a:ℕ):=by
    apply add_right_cancel (b:=(l:Per (More N))); rw [H,add_assoc,← Nat.cast_add,Nat.sub_add_cancel hl,Y.last_pole] -- tune
 let p:Per N:=w+x; have he: instant p=Y.u (i+1)+(b:Per (More N)):= by
    unfold p; rw [instant_add, ←Nat.sub_add_cancel h2, Nat.cast_add,show ↑(Z+l)=(Z:Per (More N))+(l:Per (More N)) from Nat.cast_add _ _, show Y.u (i+1)=u+Z from (Y.last_edge i).symm]; unfold b; rewrite [← H]; abel -- tune
 let Q:=Y.lL; have hx:along (Y.u i) (instant w)=a:= hu ▸ along_add _ (lt_trans hv Q); have hp:along (instant w) u=l:=by rw [←H,along_add _ (by omega)] -- tune
 have hxV:Y.Band i (instant w):=hx.trans_le (Nat.le_of_lt_succ hv); have hB: along (Y.u (i+1)) (instant p)=b:=he ▸ along_add _ (lt_of_le_of_lt hb (by omega))
 have hyV:Y.Band (i+1) (instant p):=hB.trans_le hb; refine ⟨w,(Y |> (fun _=> loom_s Y w)).2 ⟨i,hxV⟩,(loom_s Y p).2 ⟨i+1,hyV⟩, ?_,?_,?_⟩
 · change w∈_ ↔ p∉_; rw [loom_b Y hxV, loom_b Y hyV, Y.next i,not_not]
 · apply area_up Y i (l) t (pairsZ m t) (by unfold pairsZ; omega) w (areaT Y |>.2 (Y.cold_vic i _ _ ⟨hp.le,hxV⟩))
 apply area_up Y i b t (pairsZ m t) (by unfold pairsZ b; omega) p (areaT Y |>.2 (Y.hot_vic i _ _ ⟨hB.le,hyV⟩))
lemma currents (m t v:ℕ)(e:2*m<Y.long)(u:Y.short≤v): Vent (StackS Y) (bright Y) (area Y i (pairsZ m t)) v m t:=by
 constructor; intro k h; let z:=k.valMinAbs; obtain ⟨p,v'⟩:= mem_sdiff.mp h; rw [cent_at] at p v'; replace v': v<z.natAbs := Nat.lt_of_not_ge (by unfold delta1 at v'; rw [sub_zero] at v'; exact v'); obtain ⟨w,hp,hx,he,v₁,v₂⟩:=port_sheet Y i m t e z.natAbs (u.trans_lt v') (by unfold delta1 at p; rw [sub_zero] at p; exact p)
 let y:Per N:= w+ z.natAbs; let a:= (StackS Y); let b:=(bright Y); have h:(w∈ b ∧ y∉ b)∨ (w∉b∧ y∈b):=by change w ∈b ↔ y∉b at he; tauto
 by_cases p:0≤z
 · use w; rw [show w+k=y from (by unfold y; rw [← Int.cast_natCast,Int.natAbs_of_nonneg p,show (z: Per N)=k from ZMod.coe_valMinAbs _])]; exact ⟨hp,hx,h,v₂⟩ -- tune use
 refine ⟨y,hx,?_⟩; rw [show y+k=w from (by unfold y; rw [add_assoc,← Int.cast_natCast,show (z.natAbs:ℤ)= -z from (by omega),Int.cast_neg,show (z: Per N)=k from ZMod.coe_valMinAbs _,neg_add_cancel,add_zero])]; refine ⟨hp,?_ ,v₁⟩; exact h.elim (fun ⟨x,a⟩=>.inr ⟨a,x⟩) (fun ⟨x,a⟩=>.inl ⟨a,x⟩)
end YM.CF.BProof.Bias
