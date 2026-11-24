import YM.CF.Brace.Mural
/-! Append a real field value at bottom face and keep uniform separation. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.Brace
open Function Filter Lattice Metric Lat Finset Cube Tenant SU Fock Dial Phase
open scoped Topology Matrix BigOperators Matrix.Norms.L2Operator InnerProductSpace
attribute [local instance] opCStarAlgebra
variable {m B: Side}
def padC(m:Side)(a:Spot m): List (Ramp m)→ List (Ramp m)
 | []=> [((a.1,0),1)]
 | i::l => i::padC m i.1 l
lemma pads(a:Spot m)(l): (padC m a l).length=l.length+1:=by induction l generalizing a with| nil=>rfl| cons i l ih=>rw [padC,List.length_cons,List.length_cons,ih]
lemma moves_pad(a:Spot m)(l)(h:Moves m a l)(hp:a.2 ≠0)(he:∀ i∈l, (i:Ramp m).1.2 ≠0): Moves m a (padC m a l) ∧ singleU m a (padC m a l):=by
 induction l generalizing a with
 | nil=> exact ⟨⟨⟨fits_id m a.1,bot_le,(fun p=>hp (congr_arg Prod.snd p.symm))⟩,trivial⟩,hp,trivial⟩
 | cons i l ih=> obtain ⟨hh,q⟩:= ih i.1 h.2 (he i (by simp)) (fun i hi=> he i (List.mem_cons_of_mem _ hi)); exact ⟨⟨h.1,hh⟩,hp,q⟩
lemma free_pad (a:Spot m)(r:Zone)(p:0∈r)(l)(h:InRows r l): InRows r (padC m a l):=by
 induction l generalizing a with
 | nil=> simpa [InRows,padC]
 | cons i l ih=> exact fun j hp=> (List.mem_cons.mp hp).elim (fun q=>q.symm ▸ h _ (by simp)) (ih _ (fun i hi=>h i (List.mem_cons_of_mem _ hi)) j)
abbrev Sheen (m B:Side):= Stun (CSide m B)
def Tags (s:ArrayF m)(x:Sheen m B):Prop:=∀ i,s (i,0)=x (address m B i)
lemma tray_ext (c:ℝ)(x:List Vect)(q:List ℝ)(v:Vect)(h:x.length=q.length): tray (q++[c]) (x++[v]) =tray q x+c • v:=by
 induction x generalizing q with
 | nil=> obtain rfl:q=[]:=List.eq_nil_of_length_eq_zero (h.symm); simp [tray,combo]
 | cons i l ih=> cases q with
   | nil=>simp at h
   | cons j q=> rw [List.cons_append,List.cons_append,tray_cons,tray_cons, ih _ (by simpa using h),add_assoc]
lemma tray_cash (x:List Vect)(q:List ℝ)(t:ℝ)(h:x.length=q.length): tray (q.map (t * ·)) x=t • tray q x:=by induction x generalizing q with| nil=> simp [tray,combo]| cons i l ih=> cases q <;> simp at h; rw [List.map_cons,tray_cons,tray_cons, ih _ h,smul_add,smul_smul]
lemma parcel_id (U:Skin m B)(a:Index m): Cube.parcel m B U a a 1=1:=by
  let p:=address m B a; have ht:=march_len p p 1 (show separation p p≤0 by simp); -- tune
  unfold Cube.parcel; rw [List.eq_nil_of_length_eq_zero (Nat.eq_zero_of_le_zero ht)]; rfl
lemma walk_addr {U:Skin m B} {X:Sheen m B}{p:ℝ} (h:Slow U (hook X) p)(hp:0<p)(a b:Index m)(o:Lattice.Order)(hh:Fits m b a): ‖turn (Cube.parcel m B U a b o) (hook X (address m B b))-hook X (address m B a)‖ ≤ 4*B.val*p:=by
  have he:= stroll_h U _ p h (march (address m B a) (address m B b) o) (address m B a); rw [Cube.arrive] at he
  apply he.trans; apply mul_le_mul_of_nonneg_right _ hp.le
  exact_mod_cast march_len (address m B a) _ o (show separation (address m B b) (address m B a)≤B.val by rw [separation_comm]; exact chain_near hh _) -- tune
lemma handset {U:Skin m B}{s:ArrayF m}{X:Sheen m B}{p:ℝ} (h: Tags s X) (hp:Slow U (hook X) p)(hs:0<p)(a:Spot m)(l)(hb:Moves m a l): ∃ y:Vect,
   serve m B U s a (padC m a l)=serve m B U s a l++[y] ∧ ‖y-hook X (address m B a.1)‖≤l.length * (4*B.val*p):=by
   induction l generalizing a with
   | nil=>
     refine ⟨hook X (address m B a.1),?_,?_⟩; swap; exact (show ‖hook X (address m B a.1)-hook X (address m B a.1)‖ ≤ _ by simp)
     rw [padC,serve_cons,parcel_id]; simp [serve,train,h a.1,turn,fund_one]; rfl
   | cons i l ih=>
     obtain ⟨y,H,T⟩:= ih i.1 hb.2; let V:=Cube.parcel m B U a.1 i.1.1 i.2
     refine ⟨turn V y,?_,?_⟩
     · rcases i with ⟨v,o⟩; simp only [padC,serve_cons,H,List.map_append,List.cons_append]; rfl
     apply (norm_sub_le_norm_sub_add_norm_sub _ (turn V (hook X (address m B i.1.1))) _).trans
     rw [←turn_sub,turn_norm, List.length_cons]; push_cast; rw [add_mul _ 1,one_mul]; exact add_le_add T (walk_addr hp hs a.1 i.1.1 i.2 hb.1.1) -- tune
end YM.CF.Brace
