import YM.SU5.Gleam.Shelter
import YM.SU5.Thin.Glacier.Crest
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option quotPrecheck false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 800000
noncomputable section
namespace YM.Gleam
open Function Lattice MeasureTheory Finset RG Wilson Tree Filter Metric Exterior Precision Next.Rank.Spindle Pressure Work.F03 Next.SectorChange Next.SectorChange.Gaussian
open Fineness Matrix
open scoped Matrix BigOperators Classical ContDiff Topology MatrixOrder ENNReal Kronecker Matrix.Norms.Frobenius
variable {c n : Side}{r:Ratio c n}{T:Forest r}{G:Gauge}{p:BudgetPoint}{q:Clip}{v t η C S w δ β:ℝ}{U:Config G n}{A:Support c}{o x z:Site n}{f m:ℕ} {X Y:fieldDir G n 1} {R:Rules G} {Z:PathData G}{b:Cell n}{H:Bed}{F:Finset T.Free}
variable (B:Z.Bounds q η C S) (P:Attached H Z)(L:Floor H q n δ w)
variable {W:Finset (Cell n)}
local notation "St" m:max=> Sequest m +Sequest m
abbrev hallFrozen (T:Forest r)(F:Finset T.Free)(A:Support c)(m:ℕ)(W:Finset (Cell n)):= (room T F A m).filter (fun x=> afar W (St m) x.val.1)
lemma hall_icy (T:Forest r)(a:Finset T.Free)(A:Support c)(m:ℕ)(W:Finset (Cell n)): hallFrozen T a A m W⊆room T a A m:=by intro x h; simp only [hallFrozen,mem_filter] at h; exact h.1
-- separately used charges for surface at any classified cell set.
private lemma box_keep {d k:ℕ} (p:k≤d): box k⊆box d:= fun i h=> box_test.mpr ⟨fun j=>by have ht:=(box_test.mp h).1 j; omega,fun j=>by have ht:=(box_test.mp h).2 j; omega⟩
lemma wall_site {d:ℕ} (t:Odd (r.count.val))(v:d≤r.count.val/2): ((univ:Support n).filter fun i=> ¬ Safe r A d i).card ≤ ( Fintype.card (Site c)* largerBill (r.count.val) d + A.card * (r.count.val)^4):= by
 let H: Support n:= univ.filter (fun i=> ¬ Safe r A d i); let X:= r.count.val; let f:=X/2; let l:= f-d
 let C: Finset Cover:=box f \ box l; let P:=(univ:Support c) ×ˢ C; let Q:= A ×ˢ (univ:Support r.count)
 let y(i: Site c × Cover): Site n:= r.assemble (i.1,wrap r.count i.2)
 have hs:H ⊆ P.image y∪ Q.image r.assemble:=by
    intro x h; obtain ⟨⟨a,b⟩,rfl⟩:= r.assemble_bijective.2 x; let u:=Lattice.lift b; by_cases e:a ∈ A
    · exact mem_union_right _ (mem_image_of_mem _ (mem_product.mpr ⟨e, mem_univ b⟩))
    have h': u ∉ box l:= by intro v'; apply (mem_filter.mp h).2; unfold Safe; simp only [Ratio.assemble_parent,not_false_eq_true,e,true_and]; exact sec_solutions rfl v rfl t _ v'
    exact mem_union_left _ (mem_image.mpr ⟨(a,u), mem_product.mpr ⟨mem_univ a,mem_sdiff.mpr ⟨r.half_box t _,h'⟩⟩, congrArg r.assemble (Prod.ext rfl (wrap_lift _))⟩)
 let hC:= r.count.val; let M:= Fintype.card (Site c)*largerBill hC d+A.card*hC^4; have hp:H.card≤ M:=by
    refine (card_le_card hs).trans ((card_union_le ..).trans ((add_le_add card_image_le card_image_le).trans_eq ?_))
    simp only [P,Q,card_product,card_univ,C,card_sdiff_of_subset (box_keep (show l≤ f from Nat.sub_le ..)),Corona.box_size,site_card]
    unfold M largerBill; have he:f+f+1=hC:=by obtain ⟨k,h⟩:=t; change f+f+1=X; unfold f X; omega
    rw [he]; simp only [site_card]; rw [show l+l+1=(hC / 2-d)*2+1 by unfold l f; change X / 2-d+(X / 2-d)+1=_; unfold X hC; omega]
 exact hp

def speckCount (k:ℕ):ℕ:= (k+k+1)^4
def surfaceBill (r:Ratio c n)(k:ℕ)(A:Support c)(W:Finset (Cell n)):ℕ:= Fintype.card (Site c)*largerBill r.count.val k+ A.card*r.count.val^4 + W.card*speckCount k
lemma field_wall (f:Odd r.count.val)(v:m≤r.count.val/2) : ((univ:Support n).filter fun i=> ¬ Deep r A W m i).card ≤ surfaceBill r m A W:=by
 let D:= (halo m (W.image Prod.fst)); have h0:D.card ≤ W.card*speckCount m:=(Corona.halo_size ..).trans (Nat.mul_le_mul_right _ card_image_le)
 let S:Support n:=univ.filter fun i=> ¬ Safe r A m i
 refine (card_le_card (t:=S ∪ D) (fun x h=>?_)).trans ((card_union_le ..).trans (Nat.add_le_add (wall_site f v) h0))
 by_cases e: x∈ D; · exact mem_union_right _ e
 refine mem_union_left _ (mem_filter.mpr ⟨mem_univ _,fun v=> ?_⟩); apply (mem_filter.mp h).2; refine ⟨v,fun i p=>?_⟩; apply lt_of_not_ge; intro y; apply e; exact halo_spec.mpr ⟨_,mem_image_of_mem Prod.fst p,(separation_comm ..) ▸ y⟩
lemma hall_prop {x:T.Free} : x∈ hallFrozen T F A m W ↔ x∈F ∧ Deep r A W (St m) x.val.1:=by simp only [hallFrozen,room,innerBolts,mem_filter, Deep,and_assoc]
lemma hall_trim (f:Odd r.count.val)(v:St m ≤ r.count.val/2) : F.card-(hallFrozen T F A m W).card ≤ 4*surfaceBill r (St m) A W:= by
 let C:= hallFrozen T F A m W; have hp:C⊆F:= (hall_icy T F A m W).trans (inner_part (a:=F)); let D:= F \ C
 change F.card-C.card≤_; rw [← card_sdiff_of_subset hp]
 let A': Finset (Site n):= univ.filter (fun i:Site n=>¬ Deep r A W (St m) i)
 refine (card_le_card (s:=D.image Subtype.val) (t:= A' ×ˢ (univ:Finset Axis)) ?_).trans ?_|>.trans' ?_
 · intro x u; obtain ⟨y,z,rfl⟩:= mem_image.mp u; obtain ⟨h,g⟩:= mem_sdiff.mp z; exact mem_product.mpr ⟨mem_filter.mpr ⟨mem_univ _,fun z=>g (hall_prop.mpr ⟨h,z⟩)⟩,mem_univ _⟩
 rw [card_product,mul_comm A'.card, card_univ, show Fintype.card Axis=4 from Fintype.card_fin _]; exact Nat.mul_le_mul_left _ (field_wall f v)
 apply le_of_eq; rw [card_image_of_injective D Subtype.val_injective]
lemma beyondCore (a:Finset T.Free){bB:ℝ}(hv:0<bB)(h:a⊆hallFrozen T univ A m W)(Y':LinkArray G (Blip T a))(C: LinkArray G a)(t': broken r bB (T.drape (deep T a C Y')) = A) (g0:2*(r.count.val+1)<n.val) (p':suitedFee r.count.val bB≤v)(s:v≤R.c) : let t:= T.drape (deep T a C Y'); let x:=fun b:↥a=> G.plog (G.mat (C b)); let f:= stock T a x; let D:=myLog T a Y' A; ProbeBox f (2*v) ∧ ProbeBox (f+D) (2*v) ∧ TrustLogs (f+D) t r A v ∧ noiseless f r A W m:=by
 intro t x f D
 let log_use (e:Bond n)(u:Working r A e) : G.chord (t e)≤v:= (purified hv.le (show _∉broken r bB t from t'.symm ▸ u.1) g0 u.2).trans p'; -- parse Proof? 
 let norm_use (e:Bond n)(u:Working r A e) : ‖logX t e‖≤2*v:= (R.sleeve _ ((log_use e u).trans s)).trans (mul_le_mul_of_nonneg_left (log_use e u) (by norm_num))
 have ht (b:↥a) : Working r A b.val.val:= kept_freed (A:=A) (m:=m) rfl ⟨b.val,hall_icy _ _ _ _ _ (h b.property)⟩ -- implicit tune
 have hz(e:Bond n): collect G (f+D) e= (if Working r A e then logX t e else 0):=by
    change collect G (stock T a x) e+ collect G (myLog T a Y' A) e= _; rw [myLog_field]
    by_cases G0: ∀ i:↥a,e≠i.val.val
    · rw [stock_shallow x e G0,zero_add]; have hg:logX (T.drape (deep T a 1 Y')) e=logX t e:= by unfold logX t; rw [drape_agrees (X:=C) G0] -- might rewrites left
      rw [hg]; simp [G0]
    push Not at G0; obtain ⟨i,rfl⟩:= G0; rw [if_neg (show ¬(Working r A i.val.val ∧ ∀ j:↥a,i.val.val ≠ j.val.val) from fun p=> p.2 i rfl), stock_clean, add_zero,if_pos (ht _ )]; unfold x logX t; rw [drapeX]
 have v0:0 ≤ v:= ((suitFee_pos _ hv).le.trans p')
 refine ⟨fun j=> ?_,fun j=> ?_,fun i u=> ?_,fun e pH=>?_⟩
 · by_cases t':∀ i:↥a,j≠i.val.val; · unfold f; rw [stock_shallow _ j t',norm_zero]; positivity
   push Not at t'; obtain ⟨b,rfl⟩:=t'; unfold f; rw [stock_clean,show x b=logX t _ from ?_]; exact norm_use b.val.val (ht b)
   unfold logX x t; rw [drapeX]
 · rw [hz]; split_ifs; rename_i he; exact norm_use _ he; rw [norm_zero]; positivity
 · exact ⟨(hz i).trans (if_pos u),log_use _ u⟩
 by_cases G0:∀ i:↥a,e≠i.val.val; · exact False.elim (pH (stock_shallow x e G0))
 push Not at G0; obtain ⟨b,rfl⟩:=G0; exact (hall_prop.mp (h b.property)).2

end YM.Gleam