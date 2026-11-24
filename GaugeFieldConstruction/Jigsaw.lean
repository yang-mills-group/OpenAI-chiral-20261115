import GaugeFieldConstruction.Mizan
import GaugeFieldConstruction.Bough
import GaugeFieldConstruction.Kasol
import GaugeFieldConstruction.Bracer
import GaugeFieldConstruction.Savio
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Oath
open Nor
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open CF.Appel CF.Newt CF.Char CF.Neige CF.Summit Next Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Wisps Next.SectorChange.Schur MultiNext.SignedSource Lyre Banjo Analysis Pressure AnalyticBridge.MarginalMultiplier3b1d PatchReads SectorNext.Remainder SectorNext.Remainder.Scales Planned.AtomRegular Extra.Iteration Extra.Iteration.Scales
open Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
open AnalyticBridge.Annulus1AD Ac Esti
open Atala Forge Cloak Rill Hive Fock Stilo Palot Scion
open Cube Lat Tenant Tulip
open Pastry Hake Levier Urn Peaks Fock Laic Branch Drapes
attribute [local instance] opCStarAlgebra
open Rush Scroll Paige Vault Phase Acorn Spire
attribute [local instance] opCStarAlgebra
open Tarn Cay Slate Esti Cour Hest Arena Reine Kennel Facet Broc Pec Push.SectorMeasure.Oriented
open Hom Vale Vale.Grace Next.Free Thera Nacre Dial Fock
open Tye Lich Stake Pail Pail.Dew
open Lich.Muster Lor
open Jet Vol Rel
open Cascade
open Fief
open Yaw Pig
open Lich.Muster Push.AbsoluteSums
open Iva Eire
open Wray Prism Font
open PhysicalNext.JointLoad PhysicalNext.JointLoad.Heir Siete
open Feu Feu.Corset Haro
open Jet Plume Eire.Dress
section
open Py Riant Lattice Prism Tap FlightFlux TableF Boom Axon Flot Taxi
open Lenten.ModuleB
open Trees Hake Vow Bake Rue Larch
open TableF Lenten.Bank Lenten
open Layout Fren
open TableF Lenten.Bank Lenten Lenten.Layout Fren
variable {N:Side}{P:BudgetPoint}{o:Seat N}{E:InkD N}{X:Scree.Hub N}{M:Tulip.Male}{h t a v k b d:ℝ}{r l:ℕ}
-- canonical scanner, linear on admissible. defines all payload algorithms. assumes only outputs satisfying Qual at flat.Trace interfaces.
noncomputable def SealT (X:Scree.Hub N)(E:InkD N)(P:BudgetPoint)(h:ℝ)(M:Tulip.Male) := if p:∃ f: Waves, MetaB X.val.1 M f E P h then p.choose else 0
lemma meterL (w:PressB P X E h t) (s:0≤h)(M:Tulip.Male): MetaB X.val.1 M (SealT X E P h M) E P h:=by
 let p:=export_full X.val.1 M w s rfl; unfold SealT; rw [dif_pos (show ∃ f,MetaB X.val.1 M f E P h from ⟨_,p⟩)]; exact Exists.choose_spec (show ∃ f, MetaB X.val.1 M f E P h from ⟨_,p⟩)
lemma meter_sure (Z:Waves)(p:MetaB X.val.1 M Z E P h):Z=SealT X E P h M:=by unfold SealT; rw [dif_pos (Exists.intro Z p)]; exact metaUnique X.val.1 _ _ _ _ _ _ p (Exists.choose_spec (show ∃ f,MetaB X.val.1 M f E P h from ⟨Z,p⟩))
lemma meter_zero(M:Tulip.Male): SealT X 0 P h M=0:=Eq.symm (meter_sure (M:=M) _ (show MetaB X.val.1 M 0 0 P h from by have ht:=linearØ (p:=P) (h:=h) X.val.1 M 0; convert ht using 1; funext i; exact Subtype.ext (zero_smul ..).symm)) -- tune binder
lemma SeT_add (hB:0≤h){U V:InkD N}(x:PressB P X U h t)(y:PressB P X V h a)(M:Tulip.Male): SealT X (U+V) P h M=SealT X U P h M+SealT X V P h M:= Eq.symm (meter_sure (M:=M) _ (linearHU X.val.1 M (meterL x hB M) (meterL y hB M) hB x y))
lemma SeT_at (Y:Scree.Hub N)(p:PressB P X E h a)(q:0≤h)(t:X.val.2⊆ Y.val.2)(h₀:X.val.1=Y.val.1)(M:Tulip.Male): SealT X E P h M=SealT Y E P h M:=by -- bind h rename
 exact meter_sure (M:=M) _ (show MetaB Y.val.1 M (SealT X E P h M) E P h from (by rw [←h₀]; exact meterL p q M)) -- tune eq cast
-- Coffer.Word meter.Oath
lemma S_along (v:PressB P X E h t)(p:0≤h)(M:Tulip.Male) : ‖SealT X E P h M‖ ≤ SectorVal*t:= well_Z X.val.1 M v p rfl _ (meterL v p M)
-- half price across smaller crop. for U.Uint
abbrev BeZT (A: Waves)(r:ℕ):Waves := MSlot r A
lemma MSlot_k (x y:Waves): MSlot r (x+y)=MSlot r x+MSlot r y:=by
 unfold MSlot; split_ifs <;> apply Prod.ext <;> first | rfl | apply Prod.ext <;> first|rfl|exact (@add_zero J4 (CartPack PackG PackP).G.toAddCommGroup.toAddMonoid.toAddZeroClass _).symm | exact (@add_zero J5 (CartPack PackH (CartPack PackM PackS)).G.toAddCommGroup.toAddMonoid.toAddZeroClass _).symm -- tune type
lemma MStore {n:ℕ}(T:Waves)(p:r ≤ n):MSlot r (MSlot n T)=MSlot r T:=by
 unfold MSlot; split_ifs <;> first|rfl|exfalso; omega -- tune
lemma void_M (i:ℕ):MSlot i 0=0:=by unfold MSlot; split_ifs <;> rfl
lemma n_short {f:Waves}(p:Nail f (r+1))(e:r ≤2):MSlot r f=0:=by
 obtain ⟨t,q,z,a,b,c⟩:=p; apply Prod.ext (by exact z (by omega)) ; unfold MSlot; interval_cases r; -- compute
 · rfl
 · apply Prod.ext; swap; · rfl
   exact Prod.ext (t (by omega)) (a (by omega))
 exact Prod.ext (Prod.ext (t (by omega)) (a (by omega))) (Prod.ext (q (by omega)) (Prod.ext (b (by omega)) (c (by omega))))
lemma short_none {f:Waves}(p:MSlot r f=0)(v:r≤2): Nail f (r+1):=by have he:= MNil (f:=f) r v; rw [p] at he; rw [show f-0=f from sub_zero f] at he; exact he
-- Cubic small short. Ring backup Press.C.Local Seat.
abbrev Cresc (l:ℕ)(p:BudgetPoint)(X:Scree.Hub N):Prop:=coverNumber p.B X.val.2^3 < l
abbrev Zone (N:Side):= (RegBudget N) × Cusp N × ℂ
-- projections learn line. Keep sums.SMap. Need root glyph predicate only on short excluding root.And unit on all short.
abbrev Tangle {N:Side}(l:ℕ)(P:BudgetPoint)(Q:Scree.Hub N)(M:Tulip.Male)(h:ℝ)(n:ℕ)(R:RegBudget N):Prop:=∀ i:Scree.Hub N,Cresc l P i→ lifeH (R i) 1=0∧ (i≠ Q → MSlot n (SealT i (R i) P h M)=0)
structure Basalt {N:Side} (p:BudgetPoint)(o:Seat N)(l L:ℕ)(U:Zone N)(t a d h:ℝ)(n:ℕ)(M:Tulip.Male):Prop where
 rates :∃ F:Scree.Hub N→ℝ,ArenaC p U.1 o F a h (t-‖U.2.2‖)
 tags: Tangle l (KeyUp p) (Zhub o) M h n U.1
 keeps: HasCopper L o p h U.2.1 d
variable {A B:Zone N}{j:ℕ}{c:ℝ}
lemma ArenaC.rates_plus {R S:RegBudget N}{F L:Scree.Hub N→ℝ}(p:ArenaC P R o F a h v)(q:ArenaC P S o L a h k) : ArenaC P (R+S) o (F+L) a h (v+k):=by
 refine ⟨fun i=> prop_add _ i (p.fits i) (q.fits i),?_,fun i=>add_nonneg (p.paid i) (q.paid i),fun i g=>?_⟩
 · unfold ΩBook; simp_rw [Pi.add_apply,mul_add,sum_add_distrib]; exact add_le_add p.bill q.bill
 simp only [Pi.add_apply,(p.off i g).1,(p.off i g).2,(q.off i g).1,(q.off i g).2, add_zero,and_self] -- tune
lemma ArenaC.moveup {T:Scree.Hub N→ℝ}{L:RegBudget N}(p:ArenaC P L o T a h k)(v:k≤b) : ArenaC P L o T a h b:=⟨p.fits,p.bill.trans v,p.paid,p.off⟩ -- b undecl
lemma Basalt.none : Basalt P o l j (0:Zone N) 0 a 0 h r M:=by
 have ht(h):ArenaC P 0 o (0:Scree.Hub N→ℝ) a h 0:=by
    refine ⟨fun i=>Vale.rinse ..,?_,fun i=>le_rfl,fun i _=> ⟨rfl,rfl⟩⟩; simp [ΩBook] -- tune o implicit
 refine ⟨⟨0,ArenaC.moveup (ht _) ?_⟩,?_,HasCopper.zero⟩; · change (0:ℝ)≤0-‖(0:ℂ)‖; simp
 intro i v; refine ⟨rfl,fun e=>?_⟩; change MSlot _ (SealT i 0 _ _ _) =0; rw [meter_zero,void_M]

lemma Basalt.sharpen (t': Basalt P o l j A t a d h r M) (x:t≤v)(y:d≤ c): Basalt P o l j A v a c h r M:=by obtain ⟨F,p⟩:= t'.rates; exact ⟨⟨F,ArenaC.moveup p (sub_le_sub_right x _)⟩, t'.tags,t'.keeps.shove y⟩
lemma Basalt.terms (t':Basalt P o l j A t a d h r M)(u:Basalt P o l j B v a k h r M)(w:0≤h): Basalt P o l j (A+B) (t+v) a (d+k) h r M:=by
 obtain ⟨F₀,v₀⟩:=t'.rates; obtain ⟨F₁,v₁⟩:=u.rates; refine ⟨⟨F₀+F₁,ArenaC.moveup (ArenaC.rates_plus v₀ v₁) ?_⟩,?_, t'.keeps.add u.keeps⟩
 · have hp:= norm_add_le A.2.2 B.2.2; change _+_≤ t+v-‖A.2.2+B.2.2‖; linarith only [hp]
 intro i p; have he:= t'.tags i p; have hx:=u.tags i p; constructor
 · rw [show (A+B).1 i=A.1 i+B.1 i from rfl, Layout.life_add,Pi.add_apply,he.1,hx.1, add_zero]
 intro s; rw [show (A+B).1 i=A.1 i+B.1 i from rfl,SeT_add w (v₀.fits i) (v₁.fits i), MSlot_k,he.2 s,hx.2 s]; exact @add_zero Waves kinnG.toAddCommGroup.toAddMonoid.toAddZeroClass _
lemma Basalt.sumA {I:Type*}(U:Finset I)(F:I→Zone N)(A B:I→ℝ)(k:∀ i∈U,Basalt P o l j (F i) (A i) a (B i) h r M)(p:0≤h): Basalt P o l j (∑ i∈U,F i) (∑ i∈U, A i) a (∑ i∈U,B i) h r M:=by
 induction U using Finset.induction_on with
 | empty => rw [sum_empty,sum_empty,sum_empty]; exact Basalt.none
 | @insert i T t ih=>rw [sum_insert t,sum_insert t,sum_insert t]; exact (k i (mem_insert_self ..)).terms (ih fun j v=> k j (mem_insert_of_mem v)) p
end
end YM.CF.Oath
end
