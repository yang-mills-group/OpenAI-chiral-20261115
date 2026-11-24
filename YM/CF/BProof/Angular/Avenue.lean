import YM.CF.BProof.Angular.Faces

/-! Coordinates at gap columns, and the vertical direction may be reversed. Exact indexing. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BProof.Angular.Yard
open Function Filter RG Wilson Lattice Finset MeasureTheory
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius
variable {s:Side}(Y:Yard s)

abbrev Col := Y.Index × Space s
abbrev Apt := Fin Y.short × TAxis
abbrev Door := Y.Col × Y.Apt
abbrev reach (i:Y.Index)(d:Fin Y.short):= Y.atD i (d.val+1)
def inter (b:Y.Door):= horiz (Y.reach b.1.1 b.2.1) b.1.2 b.2.2
def side (b:Y.Door) := horiz (Y.atD b.1.1 b.2.1.val) b.1.2 b.2.2 -- vertical row neighbor (lower depth)
def dawn (i:Y.Index)(d:Fin Y.short) := if Y.D i then Y.atD i d.val else Y.reach i d
def dusk (i:Y.Index)(d:Fin Y.short) := if Y.D i then Y.reach i d else Y.atD i d.val
def rise (b:Y.Door):= nf (Y.dawn b.1.1 b.2.1) b.1.2 b.2.2
lemma adlaw (i:Y.Index) {x y:Per s} (hx:Y.Gap i x)(hy:Y.Gap i y): Y.depth i x=Y.depth i y↔ x=y:= ⟨fun u=> (Y.at_depth i x hx).symm.trans ((congrArg (Y.atD i) u).trans (Y.at_depth i y hy)),fun u=> u ▸ rfl⟩
lemma depth_land (i:Y.Index)(d:Fin Y.short): along (Y.v i) (Y.atD i d.val)= if Y.D i then d.val else Y.short-d.val:= by unfold atD; split; exact along_add _ (d.isLt.trans (Y.short_lt.trans Y.count_lt)); exact along_add _ ((Nat.sub_le ..).trans_lt (Y.short_lt.trans Y.count_lt))
lemma depth_inter (i:Y.Index)(d:Fin Y.short): along (Y.v i) (Y.reach i d)= if Y.D i then d.val+1 else Y.short-(d.val+1):= by
 unfold reach atD; split
 · exact along_add _ ((show d.val+1≤_ from d.isLt).trans_lt (Y.short_lt.trans Y.count_lt)) -- tune
 exact along_add _ ((Nat.sub_le ..).trans_lt (Y.short_lt.trans Y.count_lt))
lemma inter_mem (b:Y.Door): Y.inter b∈Y.field:= by unfold inter; rw [noPay Y b.1.1 _ (Y.atD_mem b.1.1 b.2.1.isLt)]; rw [depth_at Y _ b.2.1.isLt]; omega -- parameters order?
lemma horiz_inj {x y:Per s}{p q:Space s}{i j:TAxis}(e:horiz x p i=horiz y q j) : x=y∧p=q∧i=j:= by
    refine ⟨congrArg (time ∘ Prod.fst) e,?_,Fin.succ_inj.mp (congrArg Prod.snd e)⟩; simpa only [horiz,Function.comp_apply,space_join] using congrArg (space (s:=s) ∘ (Prod.fst: Bond s→ Site s)) e
lemma enters : Injective Y.inter:=by
 rintro ⟨⟨i,p⟩,⟨a,x⟩⟩ ⟨⟨j,q⟩,⟨b,y⟩⟩ h; unfold inter at h; dsimp only at h; obtain ⟨u,u',e⟩:= horiz_inj h; subst q; subst y
 have he(k:Y.Index)(a:Fin Y.short): Y.twinsGap (Y.reach k a)=k:= Y.v_part _ _ (Y.atD_mem _ a.isLt); have v:i=j:= (he ..).symm.trans ((congrArg Y.twinsGap u).trans (he ..)); subst j
 have h:a=b:=Fin.ext (Nat.succ.inj ((Y.depth_at _ a.isLt).symm.trans ((congrArg (Y.depth i) u).trans (Y.depth_at _ b.isLt))))
 rw [h]
lemma reachedBy (p:Bond s)(h:p∈Y.field): ∃ b:Y.Door,Y.inter b=p:=by
 rcases whichBond p with ⟨x,p,rfl⟩|⟨x,p,i,rfl⟩; exact False.elim (Y.fieldV x p h)
 obtain ⟨j,h,hp⟩:= (Y.fieldH x p i).1 h; let d:=Y.depth j x; obtain ⟨c,hc⟩:∃ c:Fin Y.short,c.val+1=d:= ⟨⟨d-1,by unfold d; have := Y.depth_le j x h; omega⟩,show d-1+1=d by unfold d; omega⟩
 exact ⟨((j,p),c,i),congrArg (fun x=> horiz x p i) ((congrArg (Y.atD j) hc).trans (Y.at_depth j x h))⟩
def enter : Y.Door ≃ (↑Y.field):= Equiv.ofBijective (fun i=> ⟨Y.inter i,Y.inter_mem i⟩) ⟨fun a b h=>Y.enters (congrArg Subtype.val h),fun ⟨p,h⟩=> by obtain ⟨i,rfl⟩:= Y.reachedBy p h; exact ⟨i,rfl⟩⟩
lemma dawn_open (i:Y.Index)(d:Fin Y.short): along (Y.v i) (Y.dawn i d)<Y.short:= by unfold dawn; split <;> rename_i h; rw [depth_land,if_pos h]; exact d.isLt; rw [depth_inter,if_neg h]; have :=d.isLt; omega
lemma sequence (i:Y.Index)(d:Fin Y.short): Y.dusk i d=Y.dawn i d+1:=by unfold dawn dusk; split; rename_i h; unfold reach atD; rw [if_pos h,if_pos h,atL_succ]; rename_i h; unfold reach atD; rw [if_neg h,if_neg h,← atL_succ,show Y.short-(d.val+1)+1=Y.short-d.val from by have ht:=d.isLt; omega] -- tune
lemma dawn_at (i:Y.Index)(x:Per s)(h:along (Y.v i) x<Y.short): ∃ d:Fin Y.short,Y.dawn i d=x:=by
 let a:=along (Y.v i) x; by_cases v:Y.D i
 · refine ⟨⟨a,h⟩,?_⟩; unfold dawn atD; rw [if_pos v,if_pos v]; exact add_along ..
 let b:=Y.short-(a+1); have h':b<Y.short:=by unfold b a; omega
 let d:Fin Y.short:=⟨b,h'⟩; have he:Y.short-(d.val+1)=a:=by change Y.short-(b+1)=a; unfold b a; omega
 exact ⟨d, (by unfold dawn reach atD; rw [if_neg v,if_neg v,he]; exact add_along ..)⟩
lemma dawn_inj (i:Y.Index) : Injective (Y.dawn i):= fun a b h=> by
 by_cases u:Y.D i<;> unfold dawn at h; rw [if_pos u,if_pos u] at h; apply Fin.ext; exact (Y.depth_at i a.isLt.le).symm.trans ((congrArg (Y.depth i) h).trans (Y.depth_at i b.isLt.le))
 rw [if_neg u,if_neg u] at h; apply Fin.ext; exact Nat.succ.inj ((Y.depth_at i a.isLt).symm.trans ((congrArg (Y.depth i) h).trans (Y.depth_at i b.isLt)))
lemma birth (b:Y.Door): ¬ Y.Marked (Y.rise b):= fun h=> ((marked_n ..).1 h) ⟨_,Y.dawn_open ..⟩
lemma birth_inj : Injective Y.rise:= by
 rintro ⟨⟨i,p⟩,⟨a,x⟩⟩ ⟨⟨j,q⟩,⟨b,y⟩⟩ h; unfold rise at h; dsimp only at h; have g:= nf_inj h; have ht: Y.dawn i a=Y.dawn j b:=congrArg Prod.fst g
 have he(k:Y.Index)(a:Fin Y.short): Y.twinsGap (Y.dawn k a)=k:= Y.v_part _ _ (Y.dawn_open k a).le; have hk := (he ..).symm.trans ((congrArg Y.twinsGap ht).trans (he ..)); subst j; obtain h1:=Y.dawn_inj i ht; subst b; rw [Prod.mk.injEq,Prod.mk.injEq] at g; rw [g.2.1,g.2.2]
lemma rising (x:Per s)(p:Space s)(i:TAxis)(h:¬Y.Marked (nf x p i)): ∃ b:Y.Door,nf x p i=Y.rise b:=by
 rw [marked_n] at h; obtain ⟨z,h⟩:=not_not.mp h; obtain ⟨d,h⟩:= Y.dawn_at z x h; exact ⟨((z,p),d,i),congrArg (fun x=>nf x p i) h.symm⟩
end YM.CF.BProof.Angular.Yard
