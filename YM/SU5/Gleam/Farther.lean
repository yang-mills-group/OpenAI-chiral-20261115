import YM.SU5.Gleam.Refract
/-! # Count retained coordinates. & depth geometry of separating candidate rows from future far field

Use `secluded` to work seamlessly with n winding data. -/
set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option quotPrecheck false
noncomputable section
namespace YM.Gleam
open Function Lattice MeasureTheory Finset RG Wilson Tree Filter Metric
open scoped Matrix.Norms.Frobenius Topology BigOperators ContDiff Classical
variable {c n : Side}{r: Ratio c n}{G:Gauge}{U:Config G n}{A:Support c} {x y z : Site n} {j:Site c} {b : Edge (Site n)} {d e f k:ℕ}
local notation "roofB" R:max => (R).count.val/2 -- parenthesize macro
local notation "W" R:max=> (R).count.val
/-- owns and its whole neighborhood, including this site -/
def Secluded (r: Ratio c n)(j:Site c)(d:ℕ)(x:Site n):=∀ y: Site n, separation x y ≤ d → r.parent y=j
instance (r:Ratio c n) (j:Site c) (x:Site n) : Decidable (Secluded r j d x):=by unfold Secluded; infer_instance
lemma Secluded.elbow (h:Secluded r j d x)(p:separation x y + e ≤ d): Secluded r j e y :=fun z g=> h z ((separation_triangle ..).trans ((Nat.add_le_add le_rfl g).trans p))
lemma Secluded.home (h:Secluded r j d x) : r.parent x=j:= h x (by simp)
def Safe (r: Ratio c n)(A:Support c) (d:ℕ) (x:Site n) := r.parent x∉A ∧ Secluded r (r.parent x) d x
instance (r:Ratio c n) (x:Site n) : Decidable (Safe r A d x):=by unfold Safe; infer_instance
lemma Safe.shift (h:Safe r A d x)(p:separation x y + e ≤ d): Safe r A e y:=by have ht:=h.2.elbow p; unfold Safe; rw [ht.home]; exact ⟨h.1,ht⟩ -- syntax ht.home
lemma sec_solutions (h:d=f-e)(p:e≤f)(t:f=roofB r)(g: Odd (W r))(k: Cover)(v:k∈box d) : Secluded r j e (r.embed j + wrap n k):=by
 intro y u; let X:=r.embed j+wrap n k; let q:= lift (y-X); have he :q∈box e:= Work.E08.lift_mem_box u; let z:= k+q; have hp : z ∈ box (roofB r):=by
    obtain ⟨v,jv⟩:=box_test.mp v; obtain ⟨l',u'⟩:=box_test.mp he; apply box_test.mpr; rw [←t]; constructor <;> intro i<;> simp only [Pi.add_apply,z]; · specialize v i; specialize l' i; omega
    specialize jv i; specialize u' i; omega
 rw [show y=r.assemble (j,wrap r.count z) from ?_]; exact r.assemble_parent _
 rw [Ratio.assemble]; dsimp only; rw [r.half_lift g _ hp]; unfold z q; rw [map_add,wrap_lift]; unfold X; abel -- z maybe no match
private lemma box_monotone (p:k≤d): box k⊆box d:= fun i h=> box_test.mpr ⟨fun j=>by have ht:=(box_test.mp h).1 j; omega,fun j=>by have ht:=(box_test.mp h).2 j; omega⟩
lemma step_towards (x:Site n)(i:Axis): separation x (x+step i) ≤1:=by rw [separation_comm, separation,add_sub_cancel_left]; exact pdist_step _
lemma safeIn (h:Safe r A d b.1)(p:1≤d): InHouse r (r.parent b.1) b:= ⟨rfl,h.2 _ ((step_towards ..).trans p)⟩
/-- Keep from any already-proven available set, with support criterion on anchors. -/
def innerBolts {r:Ratio c n}(T:Forest r) (a:Finset T.Free)(A:Support c) (d:ℕ) := a.filter fun x=> Safe r A d x.val.1
lemma inner_part {T:Forest r}{a:Finset T.Free} : innerBolts T a A d⊆a:= filter_subset ..
def largerBill (R d:ℕ):ℕ:= R^4-((R/2-d)*2+1)^4
lemma inner_charge {T:Forest r}{a:Finset T.Free}(t:Odd (W r))(v:d≤roofB r): a.card-(innerBolts T a A d).card ≤ 4*( Fintype.card (Site c)* largerBill (W r) d + A.card * (W r)^4):= by
 let H: Support n:= univ.filter (fun i=> ¬ Safe r A d i); let X:= W r; let f:=X/2; let l:= f-d
 let C: Finset Cover:=box f \ box l; let P:=(univ:Support c) ×ˢ C; let Q:= A ×ˢ (univ:Support r.count)
 let y(i: Site c × Cover): Site n:= r.assemble (i.1,wrap r.count i.2)
 have hs:H ⊆ P.image y∪ Q.image r.assemble:=by
    intro x h; obtain ⟨⟨a,b⟩,rfl⟩:= r.assemble_bijective.2 x; let u:=Lattice.lift b; by_cases e:a ∈ A
    · exact mem_union_right _ (mem_image_of_mem _ (mem_product.mpr ⟨e, mem_univ b⟩))
    have h': u ∉ box l:= by intro v'; apply (mem_filter.mp h).2; unfold Safe; simp only [Ratio.assemble_parent,not_false_eq_true,e,true_and]; exact sec_solutions rfl v rfl t _ v'
    exact mem_union_left _ (mem_image.mpr ⟨(a,u), mem_product.mpr ⟨mem_univ a,mem_sdiff.mpr ⟨r.half_box t _,h'⟩⟩, congrArg r.assemble (Prod.ext rfl (wrap_lift _))⟩)
 let hC:= r.count.val; let M:= Fintype.card (Site c)*largerBill hC d+A.card*hC^4; have hp:H.card≤ M:=by
    refine (card_le_card hs).trans ((card_union_le ..).trans ((add_le_add card_image_le card_image_le).trans_eq ?_))
    simp only [P,Q,card_product,card_univ,C,card_sdiff_of_subset (box_monotone (show l≤ f from Nat.sub_le ..)),Corona.box_size,site_card]
    unfold M largerBill; have he:f+f+1=hC:=by obtain ⟨k,h⟩:=t; change f+f+1=X; unfold f X; omega
    rw [he]; simp only [site_card]; rw [show l+l+1=(hC / 2-d)*2+1 by unfold l f; change X / 2-d+(X / 2-d)+1=_; unfold X hC; omega]
 rw [← card_sdiff_of_subset (inner_part (d:=d))]; let B:=a \ innerBolts T a A d; let S:= (univ: Finset Axis); refine (card_le_card (s:=B.image Subtype.val) (t:=H ×ˢ S) ?_).trans ?_ |>.trans' ?_ -- elaborate
 ·
    intro x u; obtain ⟨y,z,rfl⟩:= mem_image.mp u; obtain ⟨h,g⟩:= mem_sdiff.mp z; exact mem_product.mpr ⟨mem_filter.mpr ⟨mem_univ _,fun z=>g (mem_filter.mpr ⟨h,z⟩)⟩,mem_univ _⟩
 rw [card_product,mul_comm H.card, card_univ, show Fintype.card Axis=4 from Fintype.card_fin _]; exact Nat.mul_le_mul_left _ hp; -- may fail S
 apply le_of_eq; rw [card_image_of_injective B Subtype.val_injective]
end YM.Gleam
#print axioms YM.Gleam.inner_charge
