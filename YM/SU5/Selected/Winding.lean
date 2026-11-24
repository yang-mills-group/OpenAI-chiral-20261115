import YM.SU5.Selected.Homeland
/-!
# CP6 entrance reversal and padding identities on real storage paths.

Folds in a word are exact products, with optional Start and End tests.
The analysis here doesn't assume hierarchy Table etc.
-/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.SelectionAnalysis
open Function Set Filter Metric NormedSpace
open CF.Buffered.Afterglow.Tower MeshClock Germ Vacancy ContinuousLinearMap
open scoped Topology InnerProductSpace NNReal ENNReal
variable {M:Mesh}{a:Axis}{H:Hilbert}{I I' : Type*} (X: Repertoire I a M H)
-- Adapt padding; explicit endpoints ignored via Option
structure Ledger (a:Axis)(H:Hilbert) where
 fromT : ℝ
 tillT : ℝ
 ok : fromT ≤ tillT
 expense : H.Op
namespace Ledger
variable (L : Ledger a H)
noncomputable def revs : Ledger a H:= ⟨-L.tillT,-L.fromT, neg_le_neg L.ok,L.expense.adjoint⟩
lemma reread(L: Ledger a H) : L.revs.revs=L:=by
 cases L; simp [revs]
end Ledger
local notation "A"=> Ledger a H
variable (S : OS.Semigroup H a)
namespace Ledger
-- gap from b to t
abbrev trail := Option ℝ
@[simp]
def gap (b t: Option ℝ) : Prop:=∀ (c d:ℝ), b=some c→t=some d→ c≤d
noncomputable def between(b t:Option ℝ) : ℝ≥0 := (b.bind fun x=> t.map fun y=> (y-x).toNNReal).getD 0
noncomputable def rideBook (b t:Option ℝ)(l : List A) : H.Op:= match l with
 | [] => S.E (between b t)
 | i::l=> S.E (between b (some i.fromT)) * i.expense * rideBook (some i.tillT) t l
-- choose lh evaluation; clipping by ATerm.
def eligible (b t : Option ℝ)(l:List A) : Prop:= match l with
 | []=> Ledger.gap b t
 | i::l=> gap b (some i.fromT) ∧ eligible (some i.tillT) t l
open OS
local notation "T" u:max v:max l:max => rideBook S u v l
local notation "G" t:max v:max=> S.E (between t v)
lemma gap_t {b t : ℝ}: Ledger.gap (some b) (some t) ↔ b≤t:=by simp
lemma line {b t k : ℝ} (p:b ≤ t)(q:t ≤ k) : (G (some b) (some k))=(G (some b) (some t))*(G (some t) (some k)):=by
 let u(x y : ℝ):= (y-x).toNNReal
 change S.E (u b k)= S.E _ * S.E _
 have he:u b k=u b t+u t k:=by
   ext; rw [NNReal.coe_add]; unfold u; rw [Real.coe_toNNReal _ (sub_nonneg.mpr (p.trans q)),Real.coe_toNNReal _ (sub_nonneg.mpr p),Real.coe_toNNReal _ (sub_nonneg.mpr q)]; ring
 rw [he,S.time]; rfl
-- pad, need b,g real. by reversing List through snoc
lemma pad_start {b t k:ℝ}(l:List A)(p:b ≤ t) (v:eligible (some t) (some k) l) : eligible (some b) (some k) l ∧ rideBook S (some b) (some k) l=(G (some b) (some t)) * rideBook S (some t) (some k) l:=by
 cases l with
 | nil=> exact ⟨gap_t.mpr (p.trans (gap_t.mp v)), line S p (gap_t.mp v)⟩
 | cons i l=>
    refine ⟨⟨gap_t.mpr (p.trans (gap_t.mp v.1)),v.2⟩,?_⟩; rw [rideBook, rideBook, line S p (gap_t.mp v.1)]; simp only [mul_assoc]
lemma pad_end {b t k:ℝ}(l:List A)(p:t ≤ k)(v:eligible (some b) (some t) l) : eligible (some b) (some k) l ∧ rideBook S (some b) (some k) l= rideBook S (some b) (some t) l*(G (some t) (some k)) :=by
 induction l generalizing b with
 | nil=>exact ⟨gap_t.mpr ((gap_t.mp v).trans p), line S (gap_t.mp v) p⟩
 | cons i l ih=>
    obtain ⟨w,g⟩:= ih v.2; refine ⟨⟨v.1,w⟩,?_⟩; rw [rideBook,rideBook,g]; simp only [mul_assoc]
lemma glue {b t g:ℝ} (l l':List A) (v:eligible (some b) (some t) l) (w:eligible (some t) (some g) l'):
    eligible (some b) (some g) (l++l') ∧ rideBook S (some b) (some g) (l++l')=(T (some b) (some t) l) * (T (some t) (some g) l'):=by
 induction l generalizing b with
 | nil=> exact pad_start S _ (gap_t.mp v) w
 | cons i l ih=>
    obtain ⟨q,k⟩:= ih v.2; refine ⟨⟨v.1,q⟩,?_⟩; rw [List.cons_append,rideBook,rideBook,k]; simp only [mul_assoc]
-- exact reflection for reversed eligible word at GIVEN b,t. lots of some
lemma signed_lane (b t:ℝ): between (some (-b)) (some (-t))=between (some t) (some b):=by unfold between; simp only [Option.bind_some,Option.map_some,Option.getD_some]; congr 1; ring
local notation "[" b ":" t "]" l:max=> eligible (some (b:ℝ)) (some (t:ℝ)) l
lemma backwards {b t:ℝ} (l: List A) (p: eligible (some b) (some t) l) : eligible (some (-t)) (some (-b)) (l.reverse.map revs) ∧ rideBook S (some (-t)) (some (-b)) (l.reverse.map revs) = (T (some b) (some t) l).adjoint:=by
 induction l generalizing b with
 | nil=> rw [rideBook,S.sym]; exact ⟨gap_t.mpr (neg_le_neg (gap_t.mp p)), congrArg _ (signed_lane t b)⟩
 | cons i l ih=>
   obtain ⟨h,k⟩:= ih p.2
   rw [List.reverse_cons,List.map_append,List.map_singleton]
   have t' := Ledger.glue S _ [i.revs] h (show eligible (some (-i.tillT)) (some (-b)) [i.revs] from ⟨gap_t.mpr le_rfl, gap_t.mpr (neg_le_neg (gap_t.mp p.1))⟩)
   refine ⟨t'.1,?_⟩; rw [t'.2,k]; conv_lhs => rhs; rw [rideBook]; rw [rideBook]
   conv_rhs => rw [rideBook]
   change _ * ((G (some (-i.tillT)) (some (-i.tillT))) * i.expense.adjoint * (G (some (-i.fromT)) (some (-b)))) = star (_ * i.expense * _)
   rw [star_mul,star_mul,signed_lane i.fromT]
   rw [IsSelfAdjoint.star_eq (S.stare _), show (G (some (-i.tillT)) (some (-i.tillT)))=1 from ?_,one_mul]; rfl
   rw [show between (some _) _=0 from ?_, S.eZero]; rfl
   simp [between]; rfl
lemma erase_first {t:Option ℝ}(b : ℝ)(l:List A)(p:eligible (some b) t l) : eligible none t l:=by
 cases l with
 | nil=>simp [eligible]
 | cons=> exact ⟨by simp, p.2⟩
lemma pick_first {t:ℝ}(l:List A)(p:eligible none (some t) l): ∃ b:ℝ, eligible (some b) (some t) l:=by
 cases l with
 | nil=> exact ⟨t,gap_t.mpr le_rfl⟩
 | cons i l=> exact ⟨i.fromT, gap_t.mpr le_rfl,p.2⟩
lemma erase_last (t : ℝ){b:Option ℝ}(l:List A)(p:eligible b (some t) l) : eligible b none l:=by
 induction l generalizing b with
 | nil=> simp [eligible]
 | cons i l ih=> exact ⟨p.1,ih p.2⟩
lemma pick_last {b:Option ℝ}(l:List A)(p:eligible b none l): ∃ t:ℝ, eligible b (some t) l:=by
 induction l generalizing b with
 | nil=> cases b with
          | none=> exact ⟨0,by simp [eligible]⟩
          | some b=> exact ⟨b, gap_t.mpr le_rfl⟩
 | cons i l ih=> obtain ⟨t,h⟩:= ih p.2; exact ⟨t,p.1,h⟩
variable (Ω:H)(h:∀ t:ℝ≥0, S.E t Ω=Ω)
include h
-- evaluations ignore ends by vacuum; both sides
lemma invisible_last (b t:Option ℝ)(l:List A) : (T b none l) Ω=(T b t l) Ω:=by
 induction l generalizing b with
 | nil=> rw [rideBook,rideBook,h,h]
 | cons i l ih=> rw [rideBook,rideBook,ContinuousLinearMap.mul_apply,ContinuousLinearMap.mul_apply, ih]; rfl
lemma invisible_first (b t:Option ℝ)(l:List A): inner ℂ Ω ((T none t l) Ω)=inner ℂ Ω ((T b t l) Ω):=by
 cases l with
 | nil=> rw [rideBook,rideBook,h,h]
 | cons i l=> rw [rideBook,rideBook]; simp_rw [ContinuousLinearMap.mul_apply, ← S.swing, h]
end Ledger
namespace Repertoire
local notation "P"=> X.sky.track
local notation "L"=> (P).Realm X.sky.list
local notation "Ξ"=> glass X.sky (daylight M) X.sea X.glides
noncomputable def clerk(i:I)(u:Axis→ℝ) : Ledger a (L) where
 fromT:= X.frontend u i
 tillT:= X.endline u i
 ok:=by unfold endline; linarith [X.bar i]
 expense:=(Ξ).U (diameter u) ∘L (X.rack i) ∘L (Ξ).U (diameter (-u))
local notation "Κ" u:max l:max => (List.map (fun i=>X.clerk i (u i)) l)
lemma sep_book(l:List I)(u:I→Axis→ℝ)(b:Option ℝ): X.Correct l (Repertoire.Pages false) u b ↔ Ledger.eligible b none (Κ u l):=by
 induction l generalizing b with
 | nil=> simp [Correct,Ledger.eligible]
 | cons i l ih=> simp only [Correct,List.map_cons, Ledger.eligible, ih]; cases b <;> simp [clerk,Pages]
lemma on_the_books (l:List I)(u:I→Axis→ℝ)(b:Option ℝ) : Ledger.rideBook (Ξ) b none (Κ u l) X.origin=X.roadList l u b:=by
 induction l generalizing b with
 | nil=> rw [List.map_nil,Ledger.rideBook,roadList]; rw [show Ledger.between b none=0 from by cases b <;> rfl,(Ξ).eZero]; rfl
 | cons i l ih=>
   rw [List.map_cons,Ledger.rideBook,roadList,ContinuousLinearMap.mul_apply,ih]
   have he:Ledger.between b (some (X.clerk i (u i)).fromT)=X.sep b i (u i):=by cases b <;> rfl
   rw [he]; rfl
variable (h:∀ t:ℝ≥0,(glass X.sky (daylight M) X.sea X.glides).E t X.origin=X.origin)
include h
lemma book_account (l:List I)(u:I→Axis→ℝ)(b t:Option ℝ): inner ℂ X.origin ((Ledger.rideBook (Ξ) b t (Κ u l)) (X.origin))= X.reading l u:=by rw [← Ledger.invisible_first _ _ h, ← Ledger.invisible_last _ _ h, X.on_the_books]; rfl
end Repertoire
end YM.SelectionAnalysis
#print axioms YM.SelectionAnalysis.Ledger.glue
#print axioms YM.SelectionAnalysis.Ledger.backwards
#print axioms YM.SelectionAnalysis.Repertoire.book_account
