import YM.SU5.Gleam.Inlets

/-! # Switchboard through power heights. Keep a thick grey charge but without coarsening *every* tau defect out to those heights: drop only logarithmic halo near tau defects. -/
set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.Gleam
open Function Lattice MeasureTheory Finset RG Wilson Tree Filter Metric Exterior Precision Next.Rank.Spindle Pressure Work.F03
open scoped Matrix BigOperators Classical ContDiff Topology ENNReal Matrix.Norms.Frobenius
variable {c n : Side}{r:Ratio c n}{T:Forest r}{G:Gauge}{p:BudgetPoint}{q:Clip}{v t η C S w δ β κ ξ:ℝ}{U:Config G n}{A:Support c}{o x z:Site n}{f m:ℕ} {X Y:fieldDir G n 1} {R:Rules G} {Z:PathData G}{b:Cell n}{H:Bed}{F:Finset T.Free}

abbrev Flaws (n:Side):=Finset (Cell n)
def Beyond (L:Flaws n)(d:ℕ)(x:Site n):Prop:= ∀ b∈L, d < separation x b.1
variable {L:Flaws n}{d e:ℕ}{y:Site n}
def Brisk (r:Ratio c n)(A:Support c)(L:Flaws n)(d:ℕ)(x:Site n):Prop := Safe r A d x ∧ Beyond L d x
lemma Beyond.shift (h:Beyond L d x)(p:separation x y+e≤d): Beyond L e y:=by
 intro b v; have he:=separation_triangle x y b.1; have hv:=h b v; omega
lemma Brisk.shift (h:Brisk r A L d x)(p:separation x y+e≤d): Brisk r A L e y:= ⟨h.1.shift p,h.2.shift p⟩
lemma Brisk.halo (h:Brisk r A L d x) : x∉ halo d (L.image Prod.fst):=by
 intro v; obtain ⟨a,p,u⟩:= halo_spec.mp v; obtain ⟨k,g,rfl⟩:=mem_image.mp p;
 have he:=h.2 k g
 exact not_le.mpr he (by first | exact u| simpa only [separation_comm] using u)
def Outline (r:Ratio c n)(A:Support c)(d:ℕ): Support n:= (univ:Support n).filter fun x=> ¬ Safe r A d x
lemma misses_brisk (p:¬Brisk r A L d x): x∈ Outline r A d ∪ halo d (L.image Prod.fst):=by
 by_cases e:Safe r A d x; swap; · exact mem_union_left _ (mem_filter.mpr ⟨mem_univ _,e⟩)
 have h : ¬Beyond L d x:=fun a=>p ⟨e,a⟩
 unfold Beyond at h; push Not at h; obtain ⟨b,h,v⟩:=h
 refine mem_union_right _ (halo_spec.mpr ⟨b.1,mem_image_of_mem Prod.fst h,?_⟩)
 first|exact v|simpa only [separation_comm] using v
-- expose neighborhood count from Farther, ports for P3–4
private lemma boxMonotone_A {k d:ℕ} (p:k≤d): Lattice.box k⊆Lattice.box d:= fun i h=> box_test.mpr ⟨fun j=>by have ht:=(box_test.mp h).1 j; omega,fun j=>by have ht:=(box_test.mp h).2 j; omega⟩
lemma outline_bound (A:Support c)(p:Odd r.count.val)(v:d≤r.count.val/2):
 (Outline r A d).card ≤ Fintype.card (Site c)* largerBill r.count.val d + A.card*r.count.val^4 :=by
 let H: Support n:= univ.filter (fun i=> ¬ Safe r A d i); let X:= r.count.val; let f:=X/2; let l:= f-d
 let C: Finset Cover:=Lattice.box f \ Lattice.box l; let P:=(univ:Support c) ×ˢ C; let Q:= A ×ˢ (univ:Support r.count)
 let y(i: Site c × Cover): Site n:= r.assemble (i.1,wrap r.count i.2)
 have hs:H ⊆ P.image y∪ Q.image r.assemble:=by
    intro x h; obtain ⟨⟨a,b⟩,rfl⟩:= r.assemble_bijective.2 x; let u:=Lattice.lift b; by_cases e:a ∈ A
    · exact mem_union_right _ (mem_image_of_mem _ (mem_product.mpr ⟨e, mem_univ b⟩))
    have h': u ∉ Lattice.box l:= by intro v'; apply (mem_filter.mp h).2; unfold Safe; simp only [Ratio.assemble_parent,not_false_eq_true,e,true_and]; exact sec_solutions rfl v rfl p _ v'
    exact mem_union_left _ (mem_image.mpr ⟨(a,u), mem_product.mpr ⟨mem_univ a,mem_sdiff.mpr ⟨r.half_box p _,h'⟩⟩, congrArg r.assemble (Prod.ext rfl (wrap_lift _))⟩)
 let hC:= r.count.val; let M:= Fintype.card (Site c)*largerBill hC d+A.card*hC^4; have hp:H.card≤ M:=by
    refine (card_le_card hs).trans ((card_union_le ..).trans ((add_le_add card_image_le card_image_le).trans_eq ?_))
    simp only [P,Q,card_product,card_univ,C,card_sdiff_of_subset (boxMonotone_A (show l≤ f from Nat.sub_le ..)),Corona.box_size,site_card]
    unfold M largerBill; have he:f+f+1=hC:=by obtain ⟨k,h⟩:=p; change f+f+1=X; unfold f X; omega
    rw [he]; simp only [site_card]; rw [show l+l+1=(hC / 2-d)*2+1 by unfold l f; change X / 2-d+(X / 2-d)+1=_; unfold X hC; omega]
 exact hp
abbrev rimTax (A:Support c)(r:Ratio c n)(d:ℕ) := Fintype.card (Site c)*largerBill r.count.val d
abbrev wallTax (A:Support c) (L:Flaws n)(r:Ratio c n)(d:ℕ) := rimTax A r d + A.card*r.count.val^4 + L.card*(2*d+1)^4

def Danes (A:Support c)(L:Flaws n)(r:Ratio c n)(d:ℕ):Support n:= (univ: Support n).filter (fun i=> ¬Brisk r A L d i)
lemma Danes.tall (p:Odd r.count.val)(v:d≤ r.count.val/2):(Danes A L r d).card ≤ wallTax A L r d:=by
 have he : Danes A L r d ⊆ Outline r A d ∪ halo d (L.image Prod.fst) := fun _ x=> misses_brisk (mem_filter.mp x).2
 refine (card_le_card he).trans ((card_union_le ..).trans (Nat.add_le_add (outline_bound _ p v) ?_))
 apply (Corona.halo_size ..).trans
 have hx: 2*d=d+d:=by omega
 rw [hx]; exact Nat.mul_le_mul_right _ card_image_le

-- retain coordinates which can have ALL their non-negligible rows appear
abbrev heldHigh (r:Ratio c n)(A:Support c)(L:Flaws n)(m:ℕ)(b:Cell n):Prop:= Brisk r A L (Sequest m) b.1

def accRoom (T: Forest r)(F:Finset T.Free)(A:Support c)(L:Flaws n)(m:ℕ):Finset T.Free:= F.filter (fun i=> Brisk r A L (Sequest m + Sequest m) i.val.1)
lemma accRoom.tall {L:Flaws n} (p:Odd r.count.val)(v: Sequest m + Sequest m ≤ r.count.val/2): F.card - (accRoom T F A L m).card ≤ 4*wallTax A L r (Sequest m + Sequest m):=by
 let d:=Sequest m+Sequest m; let B:= F \ accRoom T F A L m; let S:=Danes A L r d;
 have hB: B.image Subtype.val ⊆ S ×ˢ univ:=by
    rintro x h; obtain ⟨i,z,rfl⟩:= mem_image.mp h; obtain ⟨a,b⟩:= mem_sdiff.mp z; refine mem_product.mpr ⟨mem_filter.mpr ⟨mem_univ _, fun v=> b (mem_filter.mpr ⟨a,v⟩)⟩,mem_univ _⟩
 rw [← card_sdiff_of_subset (show accRoom T F A L m ⊆ F from filter_subset _ _)]
 refine (card_image_of_injective B Subtype.val_injective).symm.trans_le ((card_le_card hB).trans ?_)
 rw [card_product,mul_comm S.card, card_univ, show Fintype.card Axis=4 from Fintype.card_fin _]
 exact Nat.mul_le_mul_left _ (Danes.tall p v)
end YM.Gleam
end
