import YM.CF.BProof.Pods.Arc
import YM.CF.BProof.Mapping.Look

/- reading equivalences, status & support agreement. Keys essential in deep spin reads
and across λ even if not used for calm. -/
set_option autoImplicit false
set_option linter.unusedVariables false
set_option synthInstance.maxSize 24000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.BProof.Pods.Brick
open Function Filter MeasureTheory Relation Finset RG Law
open Lattice Prox Grid Angular Angular.Yard Release Payment Mapping
open House Cube Lat Wilson Skye Charge Gauss Garden Pricing
open Contour Contour.Season Contour.Battery Tower
open scoped Topology BigOperators Classical ENNReal Hearth
variable {m N:Side}(Y:Yard (More N))(g:Ratio m (More N))(y:ℝ)
local notation "s"=> More N
local notation "B"=> Block Y m
local notation "G"=> SU.group
variable (x x': Static Y g)
namespace Act
abbrev pawn := (flats Y g x).1
abbrev extras:= (flats Y g x).2
abbrev ids:Ids N := (extras Y g x).1
abbrev fields : Fields N:= (extras Y g x).2
@[fun_prop] lemma pawn_m : Measurable (pawn Y g) := measurable_fst.comp (flats_m ..)
@[fun_prop] lemma extras_m: Measurable (extras Y g):= measurable_snd.comp (flats_m ..)
@[fun_prop] lemma ids_m: Measurable (ids Y g):= measurable_fst.comp (extras_m ..)
@[fun_prop] lemma fields_m : Measurable (fields Y g):= measurable_snd.comp (extras_m ..)
lemma label (i:Y.Index)(b:Bool)(p:Space s)(t:¬ Y.D i) : let c:Y.Col:=(location Y i b,p); (pawn Y g x).mood i (b,p)=(x (hide Y g c)).1.1 ⟨c,rfl⟩:= if_neg t
lemma marked : Manual.Marked Y (pawn Y g x).mood:= Manual.marks_m Y _
variable (i:Block Y m) (b: Ports Y g i)
abbrev tag (x:PadTotal Y g i) := x.1.1
abbrev sevBits (x:PadTotal Y g i) := x.1.2
abbrev tube (x:PadTotal Y g i) := x.2.2.1
def SevereTag (x:PadTotal Y g i) := ∃ p,sevBits Y g i x p
@[simp] lemma status(i:Block Y m)(v: PadTotal Y g i) : v∈ baseC Y g y i ↔ ¬ SevereTag Y g i v ∧ (∀ p,tag Y g i v p=0)∧ tube Y g i v∈pureTube Y g y i:= by
 change (v.1 = _ ∧ True ∧ _ ∧ True) ↔ _; simp only [virgin,Prod.ext_iff,pureTube,SevereTag,not_exists,Bool.not_eq_true, and_true, true_and,funext_iff]; unfold tube tag sevBits; tauto -- tune
@[simp] lemma label₀ (i:Y.Col) : let P:= Manual.nIndex Y i.1; let b:= Manual.nSide Y i.1; (pawn Y g x).mood P (b,i.2) = tag Y g (hide Y g i) (x _) ⟨i,rfl⟩:=congrFun (Manual.gets_m Y ((fieldTotal Y g x).1.1)) i
lemma card_c (i:Block Y m)(b:Ports Y g i): tag Y g i (x i) b=(Manual.gets Y (pawn Y g x).mood) b.val := by obtain ⟨v,h⟩:=b; subst i; exact (label₀ Y g x v).symm
lemma severe_e(b:Y.Col) : b∈ (pawn Y g x).sev ↔ sevBits Y g _ (x (hide Y g b)) ⟨b,rfl⟩ := by change b∈Finset.filter _ _ ↔ _; rw [mem_filter]; exact and_iff_right (mem_univ b)
lemma tube_c (i:Block Y m)(b:Ports Y g i) : hot.entry Y (pawn Y g x).gauss b.val= tube Y g i (x i) b:=by obtain ⟨v,p⟩:=b; subst i; rfl
lemma sev_c(i:Block Y m)(b:Ports Y g i): b.val∈ (pawn Y g x).sev ↔ sevBits Y g i (x i) b:= by obtain ⟨b,p⟩:=b; subst i; exact severe_e Y g x b
abbrev Fac(i:B)(v:PadTotal Y g i) := SevereTag Y g i v ∨ tube Y g i v∉pureTube Y g y i
lemma fac_m(i:Block Y m) : MeasurableSet {v:PadTotal Y g i| Fac Y g y i v} :=by
 have he: MeasurableSet {v:PadBits Y g i| ∃ p:Ports Y g i, v.2 p}:= Set.Countable.measurableSet (Set.to_countable _); exact (measurable_fst he).union ((((measurable_fst.comp measurable_snd).comp measurable_snd) (pure_m ..)).compl)
lemma severe_m(i:Block Y m) : MeasurableSet {v|SevereTag Y g i v}:= measurable_fst (Set.Countable.measurableSet (Set.to_countable {v:PadBits Y g i| ∃ p:Ports Y g i, v.2 p}))
abbrev raw: Finset Y.Col:= Model.raw y Y (pawn Y g x).sev (pawn Y g x).gauss
def sick : Finset B:= (raw Y g y x).image (hide Y g)
lemma peak(i:Block Y m) : i∈ sick Y g y x↔ Fac Y g y i (x i):=by
 constructor; intro p; obtain ⟨b,v,k⟩:= mem_image.mp p; rcases mem_union.mp v with h|h; exact Or.inl ⟨⟨b,k⟩,(sev_c Y g x i ⟨b,k⟩).1 h⟩; replace h:= (mem_filter.mp h).2; rw [tube_c Y g x i ⟨b,k⟩] at h; exact Or.inr (fun v=> v ⟨b,k⟩ (Set.mem_univ _) h)
 intro p; rcases p with ⟨b,p⟩|k
 · exact mem_image.mpr ⟨b.val,mem_union_left _ ((sev_c Y g x i b).2 p),b.property⟩
 have he:∃ b:Ports Y g i,tube Y g i (x i) b∈ Day.peak (rawQ y):=by unfold pureTube at k; simpa using k -- tune simp count
 obtain ⟨b,t⟩:=he; rw [←tube_c Y g x] at t; exact mem_image.mpr ⟨b.val,mem_union_right _ (mem_filter.mpr ⟨mem_univ _,t⟩),b.property⟩
lemma sick_e : sick Y g y x ⊆ shake Y g y x:=by intro i p; apply mem_filter.mpr; simp only [Finset.mem_univ,status,true_and]; exact fun ⟨u,_w,v⟩=> ((peak Y g y x i).1 p).elim u (fun e=> e v)
@[simp] lemma shakes(i:Block Y m) : i∈shake Y g y x↔ i∈sick Y g y x∨∃ b:Ports Y g i, tag Y g i (x i) b≠0:= by rw [peak Y g y x i]; simp only [shake,buzz,mem_filter,mem_univ, status, true_and]; unfold Fac; simp only [not_and_or,not_not,not_forall]; tauto
lemma severe_sector(b:Y.Col)(h:b∈ (pawn Y g x).sev): hide Y g b∈ sick Y g y x:= mem_image_of_mem (hide Y g) (show b∈raw Y g y x from (mem_union_left _ h))
lemma zero_tag (i:Block Y m)(h:i∉shake Y g y x): ∀ q:Ports Y g i, tag Y g i (x i) q=0:= by
 intro p; by_contra v; exact h ((shakes Y g y x i).2 (Or.inr ⟨p,v⟩))
variable {x x'}{T:Finset (Block Y m)}
lemma agrees (p: beams T x x') : Pawn.Agreed g (pawn Y g x) (pawn Y g x') T:=by
 constructor
 · intro b h; rw [severe_e,severe_e,p _ h]
 · rintro ⟨b,q⟩ h; change tube Y g _ (x (hide Y g b)) ⟨b,rfl⟩ q=tube Y g _ (x' _) _ q; rw [p _ h]
 · intro b h; change (x (hide Y g b)).2.1 ⟨b,rfl⟩ = (x' (hide Y g b)).2.1 _; rw [p _ h]
 · intro b h; change (x (addr Y g b.1)).2.2.2.1 ⟨b,rfl⟩=(x' _).2.2.2.1 _; rw [p _ h]
 intro i b q h k; rw [label Y g x i b q h,label Y g x' i b q h,p _ k] -- tune label let-bind
lemma tag_id(b:Seat N)(v:addr Y g b∈T) (p:beams T x x'): ids Y g x b=ids Y g x' b:= congrArg (fun i:PadTotal Y g (addr Y g b)=> i.2.2.2.2.1 ⟨b,rfl⟩) (p _ v)
lemma phase_y(b:Seat N)(v:addr Y g b∈T)(p:beams T x x'): (fields Y g x).1 b=(fields Y g x').1 b:=congrArg (fun i:PadTotal Y g (addr Y g b) => i.2.2.2.2.2.1 ⟨b,rfl⟩) (p _ v)
lemma phase_z(b:Site N)(v:addr Y g (Cube.node b) ∈ T)(p:beams T x x'): (fields Y g x).2 b=(fields Y g x').2 b:= congrArg (fun i:PadTotal Y g (addr Y g (Cube.node b))=> i.2.2.2.2.2.2 ⟨b,rfl⟩) (p _ v)
-- vis
lemma sick_id (p:beams T x x') (i:Block Y m)(v:i∈T): i∈sick Y g y x↔ i∈sick Y g y x':=by rw [peak,peak,p _ v]
lemma sick_vis : Vis (sick Y g y):=by
 intro t; simp_rw [Finset.ext_iff, peak, Set.setOf_forall]; apply MeasurableSet.iInter; intro i; by_cases h:i∈ t; · simp only [h,iff_true]; exact (measurable_pi_apply i) (fac_m ..)
 simp only [h,iff_false]; exact ((measurable_pi_apply (X:=PadTotal Y g) i) (fac_m ..)).compl
end Act
end YM.CF.BProof.Pods.Brick
