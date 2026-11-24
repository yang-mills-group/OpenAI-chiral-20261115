import YM.SU5.Gleam.Innate
import Refrain.Shrift
import Refrain.Kernel
/-! # Sparse defect treatment under outer-threshold tree purchase -/
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.flexible false
set_option quotPrecheck false
set_option synthInstance.maxSize 24000
set_option maxHeartbeats 300000
noncomputable section
namespace YM.Gleam.Luster
open Function Lattice MeasureTheory Finset RG Wilson Tree Filter Metric Exterior Precision Next.Rank.Spindle Pressure Work.F03 Next.SectorChange Next.SectorChange.Gaussian
open Fineness Matrix
open scoped Matrix BigOperators Classical ContDiff Topology MatrixOrder ENNReal Kronecker Matrix.Norms.Frobenius
variable {c n : Side}{r:Ratio c n}{T:Forest r}{G:Gauge}{p:BudgetPoint}{q:Clip}{v t η C S w δ β κ ξ Λ v' ν θ ω':ℝ}{U:Config G n}{A:Support c}{m:ℕ} {R:Rules G} {Z:PathData G}{b:Cell n}{H:Bed}{F:Finset T.Free}{J:ChartRatio G}
variable {X Y:fieldDir G n 1}{D:Finset (Cell n)}
variable (B:Z.Bounds q η C S) (P:Attached H Z)(L:Floor H q n δ w)(D':LocalRatio J)
-- Added sparse cut. rename Acr etc
abbrev vigilant {n:Side}(D:Finset (Cell n))(k:ℕ)(o:Site n) := ∀ b ∈ D,k < separation b.1 o
abbrev zenith (r:Ratio c n)(D: Finset (Cell n))(A:Support c)(m:ℕ)(b:Cell n):Prop:= insideB r A m b ∧ vigilant D (Sequest m) b.1
def vacuumR (X:fieldDir G n 1) (D:Finset (Cell n))(k:ℕ): Prop:=∀ b:Edge (Site n), collect G X b ≠ 0 → vigilant D k b.1
abbrev lusterBill (k:ℕ):= (k+k+1)^4
local notation "N2" m:max => (Sequest m+Sequest m)
-- bolts and count
def bloom (T:Forest r) (F:Finset T.Free)(A:Support c)(D:Finset (Cell n))(m:ℕ):= (room T F A m).filter (fun x=> vigilant D (N2 m) x.val.1)
lemma bloom_sub {a:Finset T.Free}:bloom T a A D m ⊆room T a A m:=filter_subset ..
lemma bloom_mono {a a':Finset T.Free}(h:a⊆a'):bloom T a A D m ⊆ bloom T a' A D m:=filter_subset_filter _ (filter_subset_filter _ h)
lemma bloom_slick {a:Finset T.Free} : (room T a A m).card - (bloom T a A D m).card ≤ 4*(D.card*lusterBill (N2 m)):=by
 let B:=room T a A m; let d:= N2 m
 rw [← card_sdiff_of_subset (bloom_sub)]
 let E:=B \ bloom T a A D m; let H:=Lattice.halo d (D.image Prod.fst)
 have hx: E.image Subtype.val ⊆ H ×ˢ (univ:Finset Axis):=by
    intro x ht; obtain ⟨i,h,rfl⟩:=mem_image.mp ht; obtain ⟨h,h₁⟩:=mem_sdiff.mp h
    refine mem_product.mpr ⟨?_,mem_univ _⟩
    have hi:¬∀ j∈D,d< separation j.1 i.val.1:=by intro v; exact h₁ (mem_filter.mpr ⟨h,v⟩)
    push Not at hi; obtain ⟨i',e',v'⟩:= hi
    apply halo_spec.mpr; exact ⟨i'.1, mem_image_of_mem _ e', v'⟩ -- which way
 have he:= (card_le_card hx)
 rw [card_product,card_image_of_injective _ Subtype.val_injective, card_univ,show Fintype.card Axis=4 from Fintype.card_fin _] at he
 exact he.trans (le_trans (Nat.mul_le_mul_right _ ((Corona.halo_size _ _).trans (Nat.mul_le_mul_right _ card_image_le))) (le_of_eq (by unfold lusterBill; ring)))
lemma bloom_charge {a:Finset T.Free}(odd:Odd r.count.val)(h:N2 m ≤ r.count.val/2) : a.card-(bloom T a A D m).card ≤ 4*((Fintype.card (Site c)*largerBill r.count.val (hallBill m) + A.card*r.count.val^4)+D.card*lusterBill (hallBill m)):=by
 have hp:=bloom_slick (a:=a) (D:=D) (m:=m) (A:=A); have ht:=inner_charge (T:=T) (a:=a) (A:=A) odd h; have hu:bloom T a A D m⊆room T a A m:=bloom_sub; have hh: room T a A m⊆ a:=inner_part
 have hW:= card_le_card hu; have hl:=card_le_card hh; change a.card-(room T a A m).card ≤ _ at ht
 unfold hallBill; rw [mul_add]; omega -- N2 precedence trouble
lemma saved {a:Finset T.Free}(p:a⊆bloom T univ A D m)(g:LogArray G a):vacuumR (stock T a g) D (N2 m):=by
 intro z h; by_cases t: ∀ i:↥a,z ≠i.val.val
 · exact (h (stock_shallow g z t)).elim -- need h forall
 push Not at t; obtain ⟨b,rfl⟩:= t; exact (mem_filter.mp (p b.property)).2
end YM.Gleam.Luster
