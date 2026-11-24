import YM.CF.Phase.PairLaw
import YM.CF.Jet.Sam

/-! Uniform positivity of regular law normalizations; no log under a zero rate. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.Jet
open Function Filter Metric Finset MeasureTheory Phase Phase.Sample Lattice SU Cube Lat
open scoped Topology BigOperators ContDiff NNReal Matrix.Norms.L2Operator InnerProductSpace
attribute [local instance] opCStarAlgebra
abbrev bias:=6*budgetW
variable {I:Type} [Fintype I][DecidableEq I]{N:ℕ}{m B:Side}
def parsed (f:List Lat.Vect)(w:Ballot):ℝ:=expNegInvGlue (‖restrain margin f w.val‖-broad)
lemma enum_avoid {s:Finset I} (h:s.card≤bias)(F:I→List Lat.Vect)(hp:∀ i∈s,(F i).length≤6):∃ w:Ballot, 0< ∏ i ∈ s, parsed (F i) w :=by
 choose v hv using fun u:s=> normal (F u.val) (lt_of_le_of_lt (hp u.val u.property) (by norm_num))
 obtain ⟨w,h⟩:=(uniform_miss ..).choose_spec.2 I s h v
 refine ⟨w,prod_pos fun i hi=> expNegInvGlue.pos_of_pos (sub_pos.mpr ((h ⟨i,hi⟩).trans_le (strain_margin margin _ (v ⟨i,hi⟩) w.val (hv ⟨i,hi⟩))))⟩ -- tune

def pitchR (l:I→ Fin 7):= I→ Fin 6→Ballot -- pad
abbrev readyK (n:ℕ):= Fin n→ Fin 6→ Ballot
def chest (l:Fin N→Fin 7)(p:readyK N)(i:Fin N):= ((List.finRange 6).take (l i).val).map fun j=> (p i j).val
def blond (l:Fin N→Fin 7) (p:readyK N) (w:Ballot):=∏ i,parsed (chest l p i) w
lemma chest_any (v:List Lat.Vect)(h:v.length≤6)(w:∀ i∈v,‖i‖=1):∃ l:Fin 7,∃ p:Fin 6→Ballot, v= ((List.finRange 6).take l.val).map fun i=>(p i).val:=by
 classical
 have ht : ∃ p:Fin 6→Lat.Vect, (∀ i, ‖p i‖=1) ∧ ((List.finRange 6).take v.length).map p=v:=by
    let F(i:Fin 6):Lat.Vect:= if h:i.val<v.length then v[i.val] else basisKet 0
    refine ⟨F,fun i=>?_, List.ext_get ?_ ?_⟩
    · unfold F; split
      next hx=> exact w _ (List.getElem_mem ..)
      next h=>simp [basisKet]
    · simp [h]
    intro i hi hi'; unfold F; simp [hi']
 obtain ⟨P,H,T⟩:=ht
 exact ⟨⟨v.length,by omega⟩,fun i=> ⟨P i,by simp [Sphere,H]⟩,T.symm⟩
lemma bl_cont (l:Fin N→ Fin 7) : Continuous (fun x:readyK N×Ballot=> blond l x.1 x.2):=by
 apply continuous_finsetProd; intro i _
 apply (expNegInvGlue.contDiff (n:=0)).continuous.comp
 apply Continuous.sub _ continuous_const; apply Continuous.norm
 exact strain_cont margin margin_pos ((List.finRange 6).take (l i).val) (fun i' (x:readyK N×Ballot)=> (x.1 i i').val) (fun i' _=>continuous_subtype_val.comp ((continuous_apply i').comp ((continuous_apply i).comp continuous_fst))) _ (continuous_subtype_val.comp continuous_snd)
lemma born_bl(l:Fin N→Fin 7)(p:readyK N)(h:N ≤ bias): 0<∫ w, blond l p w ∂cloud :=by
 have ht : (Finset.univ:Finset (Fin N)).card ≤ bias:= by rw [card_univ,Fintype.card_fin]; exact h
 have he (i:Fin N) (_:i∈Finset.univ): (chest l p i).length≤6:=by simp only [chest,List.length_map,List.length_take,List.length_finRange]; exact Nat.min_le_right _ _
 obtain ⟨v,hv⟩:=enum_avoid ht (chest l p) he
 change 0 < blond l p v at hv
 have hc:Continuous (blond l p):=by
   have h : Continuous (fun t:Ballot=> (p,t)):= continuous_const.prodMk continuous_id
   have ht:=(bl_cont l).comp h; exact ht
 have hp (w:Ballot):0≤blond l p w:=prod_nonneg (fun i _=> expNegInvGlue.nonneg _)
 exact integral_pos_of_integrable_nonneg_nonzero hc (net_compact hc) hp hv.ne'
lemma uni_bl (B:ℕ)(e:B≤bias)(n:Fin (B+1))(l: Fin n.val→Fin 7):∃ a>0,∀ p:readyK n.val, a≤ ∫ w,blond l p w ∂cloud :=by
 have hc:Continuous (fun p:readyK n.val=> ∫ w,blond l p w ∂cloud):= net_cont _ _ (bl_cont l)
 obtain ⟨x,-,ht⟩:= isCompact_univ.exists_isMinOn Set.univ_nonempty hc.continuousOn
 exact ⟨_,born_bl l x ((Nat.le_of_lt_succ n.isLt).trans e),fun p=>ht (Set.mem_univ p)⟩
set_option maxRecDepth 4096 in
lemma joint_under(B:ℕ)(e:B≤bias) :∃ a,0<a ∧∀ N:ℕ,N≤B→∀ l (p:readyK N),a≤ ∫ w,blond l p w ∂cloud :=by
 let V:=Σ n:Fin (B+1), Fin n.val → Fin 7; choose c C h using fun x:V =>uni_bl B e x.1 x.2
 obtain ⟨v,H,t⟩:=sm_min Finset.univ c (fun i _=> C i); refine ⟨v,H,fun n hn l p=>?_⟩
 let i:V:=⟨⟨n,Nat.lt_succ_of_le hn⟩,l⟩; exact (t i (mem_univ i)).le.trans (h i p)
lemma bonnet (K:Finset I)(f:I→ ArrayF m)(j:Row)(r:I→ Phase.Zone)(x:Cue m)(a:Index m)(U:Skin m B)(h:K.card≤6): ∃ n:ℕ, n≤bias∧ ∃ l,∃ p:readyK n,draw m B K U f r j a ∘ update x a=blond l p:=by
 classical
 let g (i:I):= permits m (a,j) (insert j (r i)); let S:= K.biUnion fun i=>(g i).image (fun x=>(i,x)); let I' := ↥S
 have ht:S.card≤bias:=le_trans (Finset.card_biUnion_le ..) (le_trans (sum_le_sum (g:=fun _=> budgetW) (fun i hi=> (card_image_le).trans (permits_cap ..))) (by simpa using Nat.mul_le_mul_right budgetW h))
 let t(i:I×List (Ramp m)):= train m B U (capRow (f i.1) j x) a i.2
 have hm (i:I') :(t i.val).length≤6:=by obtain ⟨j,-,J⟩:=mem_biUnion.mp i.property; obtain ⟨d,h,p⟩:=mem_image.mp J; unfold t; rw [train_len,←p]; exact total_len (permits_iff.mp h).1
 have he (i:I')(v:Lat.Vect)(h:v∈t i.val): ‖v‖=1:=by
   have hp (l:List (Ramp m)) b (p:ArrayF m) :∀ x∈train m B U p b l,‖x‖=1:=by
      induction l generalizing b with
      | nil=>simp [train]
      | cons i l ih=>
         rcases i with ⟨w,k⟩; rw [train]; intro z ht; obtain ⟨u,h,rfl⟩:=List.mem_map.mp ht
         rw [turn_norm]; rcases List.mem_cons.mp h with t|t; exact t ▸ vote_unit _; exact ih _ _ t
   exact hp _ _ _ _ h
 choose l p H using fun i:I'=>chest_any (t i.val) (hm i) (he i)
 let e:= Fintype.equivFin I'; refine ⟨Fintype.card I', by simpa [I'] using ht, l ∘ e.symm, p ∘ e.symm,?_⟩; funext w
 let X:=fun i:List (Ramp m)=>i
 calc
   _ = ∏ i ∈ S,parsed (t i) w:=by
     rw [Finset.prod_biUnion]
     · apply Finset.prod_congr rfl; intro i hi; rw [Finset.prod_image _]; change fundF _ _ _ _ _ _=_; apply Finset.prod_congr rfl; intro x' hx
       unfold t parsed rateF
       rw [train_eq m B U (capRow (f i) j x) _ _ (capRow (f i) j (update x a w)) ?_,show capRow _ _ (update x a w) (a,j)=w from by simp [capRow]]
       rintro ⟨⟨y,l⟩,k⟩ t; have H := move_mem (permits_iff.mp hx).1 _ t; have v:= H.2.2
       unfold capRow; dsimp only; split; rename_i he; subst l; change update x a w y= x y; rw [update_of_ne (show y ≠ a from fun p=>v (by rw [p]))]; rfl
       exact fun x _ y _ h=> (Prod.mk.inj h).2
     intro i hi j hj h; apply Finset.disjoint_left.mpr; intro x p q; obtain ⟨x,h',rfl⟩:= mem_image.mp p; obtain ⟨y,_,t⟩:= mem_image.mp q; exact h (Prod.mk.inj t|>.1.symm)
   _ = ∏ i:I',parsed (t i.val) w:= by rw [← prod_coe_sort]
   _ = _:= by unfold blond; rw [← Equiv.prod_comp e]; apply prod_congr rfl; intro i _; rw [H i]; simp [chest,Function.comp_apply]
lemma payment (K:Finset I)(h:K.card≤6) : ∃ a:ℝ,0<a∧∀ m B:Side,∀ U f r j b x,a≤ limitW m B K U f r j b x:=by
 obtain ⟨k,p,H⟩:=joint_under bias le_rfl; refine ⟨k,p,fun m B U f r j b x=>?_⟩; obtain ⟨n,c,l,w,T⟩:= bonnet K f j r x b U h; unfold limitW; simp_rw [show ∀ i, draw m B K U f r j b (update x b i)=_ from congr_fun T]; exact H n c l w
end YM.CF.Jet
