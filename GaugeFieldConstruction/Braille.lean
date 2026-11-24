import YM.CF.BProof.Floral.Myrtle
import YM.CF.BProof.Floral.Prop
import GaugeFieldConstruction.Tramp
/-! graded operator shape & comparison.-/
set_option autoImplicit false
set_option maxHeartbeats 50000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Oath
open Nor
open Function NormedSpace Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
open Atala Forge Cloak Rill Hive Fock Stilo Palot Scion
open Cube Lat Tenant Tulip
open Pastry Hake Levier Urn Peaks Fock Laic Branch Drapes
attribute [local instance] opCStarAlgebra
open Rush Scroll Paige Vault Phase Acorn Spire
open Tarn Cay Slate Cour Hest
open Hom Vale Vale.Grace Next.Free Thera Nacre Dial Fock
open Fief Jet Vol Rel
open Yaw Pig
open Feu Feu.Corset Haro
section
open Py Riant Lattice Prism Tap FlightFlux TableF Boom Axon Flot Taxi
open Lenten.ModuleB
open Lich.Muster
open Hake Vow Bake Rue Larch
open TableF Lenten.Bank Lenten Lenten.Layout Fren
open Frugal
open scoped YM.CF.Mew
variable {N:Side}{P:BudgetPoint}{o:Seat N}{t v s a k b h:ℝ}{p l L n:ℕ}{M: Male}
lemma Arena_κ (z:ℂ) {X:Scree.Hub N→ℝ}{T:RegBudget N}(p₀:ArenaC P T o X a h t): ArenaC P (z • T) o (‖z‖ • X) a h (‖z‖*t):=by
 refine ⟨fun i=> Floral.regular_scale _ (p₀.fits i),?_,fun i=> mul_nonneg (norm_nonneg _) (p₀.paid i), fun i v=>?_⟩
 · have he:=mul_le_mul_of_nonneg_left p₀.bill (norm_nonneg z); unfold ΩBook at *; simp_rw [Pi.smul_apply,smul_eq_mul,mul_left_comm _ ‖z‖, ←mul_sum]; exact he -- tune
 rw [Pi.smul_apply,Pi.smul_apply,(p₀.off i v).1,(p₀.off i v).2]; simp
lemma HasCopper.smul (z:ℂ){K:Cusp N}(p:HasCopper l o P h K t) :HasCopper l o P h (z • K) (‖z‖*t):=by
 obtain ⟨A,W,a,g,t⟩:=p; refine ⟨fun i p=>A i ?_,‖z‖ • W,⟨fun i=> mul_nonneg (norm_nonneg _) (a.1 i),fun i D e u=>Floral.medal_scale _ (a.2 i D e u)⟩,fun i p=> g i ?_,?_⟩
 · intro v; rw [Pi.smul_apply,v,smul_zero] at p; exact p rfl
 · intro v; rw [Pi.smul_apply,v,smul_zero] at p; exact p rfl
 simp_rw [Pi.smul_apply,smul_eq_mul,mul_left_comm _ ‖z‖,←mul_sum]; exact mul_le_mul_of_nonneg_left t (norm_nonneg _)
lemma BeaconΚ (M:Male)(z:ℂ){X:Scree.Hub N}{E:InkD N}(q:PressB P X E h a)(p:0≤h): SealT X (z • E) P h M=z • SealT X E P h M:= (meter_sure _ (linearHQ _ _ (meterL q p _) q z p)).symm
lemma ΓWave (z:ℂ) (T:Waves):MSlot n (z • T)= z • MSlot n T:= (ΓProj n).map_smul z _
lemma Troot_z {E:Type}(P:TPack E)(z:ℂ):letI:=P.G; letI:= P.S; z • (0:E)=0:=by letI:=P.G; letI:=P.S; exact smul_zero z
lemma Basalt.smul (z:ℂ){A:Zone N}(p:Basalt P o l L A t a v h n M)(hx:0≤h) : Basalt P o l L (z • A) (‖z‖*t) a (‖z‖*v) h n M:=by
 obtain ⟨F,T⟩:=p.rates; refine ⟨⟨‖z‖ • F,ArenaC.moveup (Arena_κ z T) ?_⟩,?_,p.keeps.smul z⟩
 · change ‖z‖*(t-‖A.2.2‖) ≤ _-‖z • A.2.2‖; rw [norm_smul,mul_sub]
 intro i hk; have He:= p.tags i hk; rw [show (z • A).1 i=z • A.1 i from rfl, BeaconΚ M z (T.fits i) hx,ΓWave, life_smul,Pi.smul_apply]; constructor; · rw [He.1,smul_zero]
 intro u; rw [He.2 u]; exact Troot_z Packs_U z

variable {A B:Zone N}
lemma CardT_plus (p:Basalt P o l L A t a k h n M)(q:Basalt P o l L B v a b h n M)(ht:0 ≤ h) (r:ℕ): CardT (A+B) (KeyUp P) M h o r=CardT A (KeyUp P) M h o r+CardT B (KeyUp P) M h o r:=by
 obtain ⟨_,e⟩:=p.rates; obtain ⟨_,z⟩:=q.rates; let X:=Zhub o; change MSlot r (SealT X (_ + _) _ _ _) =_; rw [SeT_add ht (e.fits _) (z.fits _),MSlot_k]
lemma CardT_scalar (z:ℂ)(p:Basalt P o l L A t a k h n M)(ht:0≤h)(r:ℕ): CardT (z • A) (KeyUp P) M h o r=z • CardT A (KeyUp P) M h o r:=by
 let X:= Zhub o; obtain ⟨F,Y⟩:= p.rates; unfold CardT; dsimp only; rw [show (z • A).1 (Zhub o)=z • A.1 (Zhub o) from rfl, BeaconΚ M z (Y.fits X) ht,ΓWave]
lemma CardT_sum {I:Type*}(J: Finset I)(F:I→Zone N)(X Y:I→ℝ)(u:∀ i∈J,Basalt P o l L (F i) (X i) a (Y i) h n M)(p:0 ≤ h)(r:ℕ) : CardT (∑ i∈J,F i) (KeyUp P) M h o r=∑ i∈J, CardT (F i) (KeyUp P) M h o r:=by
 induction J using Finset.induction_on with
 | empty=> rw [sum_empty,sum_empty]; change MSlot _ (SealT _ 0 _ _ _) = _; rw [meter_zero,void_M]
 | @insert i J t ih=>
    have h'(j)(p:j∈J):= u j (mem_insert_of_mem p); rw [sum_insert t,sum_insert t,CardT_plus (u i (mem_insert_self ..)) (Basalt.sumA J F X Y h' p) p,ih h']
lemma InterestC : 0 ≤ SectorVal:= le_trans (by norm_num : 0 ≤ (2500:ℝ)) (le_max_left ..)
lemma CardT_note (p:Basalt P o l L A t a k h n M)(ht:0≤h)(x:0≤a)(j:ℕ): ‖CardT A (KeyUp P) M h o j‖≤ SectorVal*t:=by
 unfold CardT; dsimp only; apply (MSlot_m ..).trans; obtain ⟨F,Z⟩:= p.rates; exact (S_along (Z.fits _) ht M).trans (mul_le_mul_of_nonneg_left ((Z.earns _ x).trans (sub_le_self _ (norm_nonneg _))) InterestC) -- tune syntax
end
end YM.CF.Oath
end
