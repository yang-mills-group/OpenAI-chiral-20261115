import YM.SU5.Six.TransitWall
import YM.SU5.Six.Photos
import YM.SU5.Six.OrdinaryMist
import YM.SU5.Aria.Grotto
import YM.SU5.Six.KeepCharge
import YM.SU5.Six.MirrorCharge
set_option maxHeartbeats 200000
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 2000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common Ballad Cordial
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
open Germ Alliance
open Lamour.Bridge.Celeste
open Designs Twah Prototype
open YM.Stationary (Gaia) -- tune
open CF.Onyx (riseX moor)
open Lamour.Bridge.Celeste.Morn
namespace Spine
open Aria Set
open Cheer (Narrow)
/-!
# eq:As, resolution consultation

Independent smooth probes with real densities. They don't vary after resolution
budgets were chosen. `activation` distributes the mesh payment h^4 into the
weights. Use actual `u ∈ tsupport` for the paid finite finsets.
Everything at t goes into Dome. No unstated contacts/fusions are priced.
-/
open MacroGrid
open Casting
-- indices for C∞: s infinity natural (not omega analytic)
open scoped ContDiff
structure Dose (E:Type)[NormedAddCommGroup E][NormedSpace ℝ E] where
 val: E→ℝ
 smooth: ContDiff ℝ ∞ val
 budget: HasCompactSupport val
def Dose.Normalized {E:Type}[NormedAddCommGroup E][NormedSpace ℝ E][MeasureSpace E](d:Dose E):Prop:= (∀ x,0≤d.val x)∧∫ x,d.val x=1
abbrev SampleDose := Dose Vantage

def poseMirror (j:Axis): Vantage≃ₜ Vantage where
  toFun:= opposeR j
  invFun:= opposeR j
  left_inv:= reflectPose_twice j
  right_inv:= reflectPose_twice j
  continuous_toFun:=mirrorPose j
  continuous_invFun:=mirrorPose j
lemma opposite_money (j:Axis): MeasurePreserving (opposeR j):=by
 let f(i:Axis)(x:ℝ):= if i=j then -x else x
 have h:opposeR j=fun x i=> f i (x i):=funext fun x=>funext fun i=>by by_cases p:i=j<;> simp [opposeR,mirrorΩ,p,f]
 rw [h]; apply volume_preserving_pi; intro i; unfold f; split <;> first| exact Measure.measurePreserving_neg _| exact MeasurePreserving.id .. -- branch split lambda

def flipDose (A: SampleDose) (j:Axis): SampleDose where
 val:= A.val ∘ (poseMirror j)
 smooth:= A.smooth.comp (contDiff_pi.mpr (fun i=> by
   change ContDiff ℝ ∞ (fun x:Vantage=> if i=j then -x j else x i)
   by_cases p:i=j
   · simp_rw [if_pos p]; fun_prop
   simp_rw [if_neg p]; fun_prop))
 budget:= A.budget.comp_homeomorph (poseMirror j)
lemma flipPay (A:SampleDose)(p:A.Normalized)(j:Axis): (flipDose A j).Normalized:= ⟨fun k=>p.1 _, (((show MeasurePreserving (poseMirror j).toMeasurableEquiv volume volume from opposite_money j).integral_comp' A.val).trans p.2)⟩
lemma flipBudget (A:SampleDose)(j:Axis): tsupport (flipDose A j).val = (poseMirror j) ⁻¹' tsupport A.val := by
 change closure (Function.support (A.val ∘ (poseMirror j)))=_
 exact ((poseMirror j).preimage_closure (Function.support A.val)).symm -- simp? support

-- Actual independent-test sums
variable (P:Spine)(t:ℕ)(A:P.Apron)(r:SampleDose)
local notation "u"=> P.meshPose t
local notation "T"=> P.Test
def usedGrid : Finset Cover :=
 (finite_ledger (I:=Axis) (P.macroStep t) (P.macroStep_pos t) (tsupport r.val) r.budget).toFinset
lemma usedPose (k:Cover): k∈ P.usedGrid t r ↔ u k ∈ tsupport r.val := by rw [usedGrid, Set.Finite.mem_toFinset]; rfl
def activation (k:Cover): ℂ:= ↑((P.macroStep t)^4 * r.val (P.meshPose t k))
local notation "a" i:max => P.activation t r i
def prepared : P.Test := ∑ k ∈ P.usedGrid t r, P.activation t r k • P.issuing t A k
lemma prepared_literal : P.prepared t A r=((P.macroStep t:ℂ)^4) • ∑ k∈ P.usedGrid t r,(r.val (P.meshPose t k):ℂ) • P.chartAll k (A.full P t):= by
 rw [prepared,Finset.smul_sum]; simp_rw [smul_smul, issuing, activation]; push_cast; rfl
lemma prepared_color : P.prepared t A r∈enclave P.calibration:= Subalgebra.sum_mem _ (fun k _=>Subalgebra.smul_mem _ (P.issuing_color t k A) _)
-- total price and check height-t support contained there
abbrev spacePrice : Set Vantage:= ⋃ p∈ tsupport r.val,P.Aperture A p
lemma pin_union(k v:Finset Cover): P.pinFoot t (k∪v)= P.pinFoot t k ∪ P.pinFoot t v:= by
 ext; simp only [pinFoot,mem_setOf_eq,Set.mem_union, Finset.mem_union,or_and_right,exists_or]
def asked_at (P: Spine)(t:ℕ)(g:P.Test)(Y:Set Vantage): Prop:=∃ S:Finset Cover,g∈bay P.calibration S true∧ P.pinFoot t S ⊆ Y
lemma prepared_at (p:A.s≤ t): P.asked_at t (P.prepared t A r) (P.spacePrice A r):= by
 let f(k:Cover):= P.issuing t A k; let Y:=P.spacePrice A r; let S:=P.usedGrid t r
 suffices h:∀ L,L⊆S→ P.asked_at t (∑ k∈L,a k • f k) Y from h S fun _ h=>h
 intro L; induction L using Finset.induction_on with
 | empty=>
   intro _; refine ⟨∅,?_,?_⟩
   · rw [sum_empty]; exact Subalgebra.zero_mem _
   simp [pinFoot]
 | @insert i L hi ih=>
   intro h
   obtain ⟨R,H,e⟩:=ih ((Finset.subset_insert ..).trans h)
   let k:= P.plotSet t A i; refine ⟨k∪R,?_,?_⟩
   · rw [sum_insert hi]; exact Subalgebra.add_mem _ (tallerBay _ _ true Finset.subset_union_left (Subalgebra.smul_mem (bay _ k true) (P.issuing_support t i A) _)) (tallerBay _ _ true Finset.subset_union_right H)
   rw [P.pin_union]; exact Set.union_subset (Set.Subset.trans (P.inside_now t i A p) (Set.subset_iUnion₂_of_subset (P.meshPose t i) ((P.usedPose t r i).1 (h (Finset.mem_insert_self ..))) Set.Subset.rfl)) e

lemma prepared_opposition (j:Axis) : P.prepared t (A.kiss P j) (flipDose r j)= P.reflectTest j (P.prepared t A r):= by
 let F:= (flipDose r j); let G:=P.prepared t A r; let B:=A.kiss P j
 let S:=P.usedGrid t r; let L:=P.usedGrid t F
 let Φ:= P.reflectTest j; let g:=opposeQ j; let f(k:Cover):T:= P.activation t r k • P.issuing t A k
 have hx: Function.Injective g:= (reflectInt_twice j|> Function.Involutive.injective)
 have hp(k:Cover): g k∈L ↔ k∈S:= by
   unfold L S; rw [P.usedPose,P.usedPose,P.tile_reflect t k j, show tsupport F.val=_ from flipBudget r j]; change opposeR j (opposeR j (u k))∈ tsupport r.val ↔ _; rw [reflectPose_twice]
 have he:L= S.image g:=Finset.ext (fun k=> by
   rw [Finset.mem_image]; constructor
   · intro h; exact ⟨g k,(hp (g k)).1 (Eq.mpr (congrArg (· ∈ L) (reflectInt_twice j k)) h), reflectInt_twice j k⟩
   rintro ⟨p,h,rfl⟩; exact (hp _).2 h)
 have ht (L:Finset Cover) : Φ (∑ k∈L, f k)=∑ k∈L,Φ (f k):= by
   induction L using Finset.induction_on with
   | empty=>simp only [sum_empty]; simpa only [zero_smul,star_zero] using P.scale_mirror (0:T) 0 j -- star zero rewrite smul_zero needs Φ0 ?
   | @insert k L' h H=> rw [sum_insert h,sum_insert h,P.sum_mirror,H]
 change ∑ i∈L,_= Φ _
 rw [he,Finset.sum_image (fun a₀ _ b _ p=> hx p), prepared, show (∑ k ∈ P.usedGrid t r, P.activation t r k • P.issuing t A k) = (∑ k∈S,f k) from rfl,ht]
 refine Finset.sum_congr rfl (fun i _=> ?_); rw [P.issue_reflect, show Φ (f i)=star (a i) • Φ (P.issuing t A i) from P.scale_mirror ..]; apply congrArg (· • Φ (P.issuing t A i))
 unfold activation; rw [P.tile_reflect,show F.val (opposeR j (u i))= r.val (u i) from congrArg r.val (reflectPose_twice j (u i))]; simp -- unfold g/F
open Six
lemma Dose_zero (x:P.Spectrum0 3)(g:P.singleState 3 A.s x A.F=0)(e:A.s≤t) : P.singleState 3 t x (P.prepared t A r)=0:= by
 unfold prepared; rw [map_sum]; refine Finset.sum_eq_zero (fun k _=>?_); rw [map_smul,P.issue_price _ _ _ A k e,g,smul_zero]
-- comparison whole smeared product, use exact endpoint `Sensor`
lemma split_test (B:P.Apron)(s:SampleDose)(p:Disjoint (P.spacePrice A r) (P.spacePrice B s))(e: A.s≤t)(g:B.s≤t)(W:Bool)(b:P.Sensor A W) (X:Dome P.calibration →ₗ[ℂ] ℂ)(h:Factors P.calibration X) (u':MatterWard P.calibration X ∨ GaugeWard P.calibration X) :
   X (P.prepared t A r * P.prepared t B s) = 0:=by
 unfold prepared; rw [Finset.sum_mul,map_sum]; refine Finset.sum_eq_zero fun i l=>?_
 rw [Finset.mul_sum,map_sum]; refine Finset.sum_eq_zero fun k v=>?_
 have ht: Disjoint (P.Aperture A (u i)) (P.Aperture B (u k)) := p.mono (Set.subset_iUnion₂_of_subset (u i) ((P.usedPose t r i).1 l) Set.Subset.rfl) (Set.subset_iUnion₂_of_subset (u k) ((P.usedPose t s k).1 v) Set.Subset.rfl)
 have hu:=P.msplit_pair W t h u' A B b e i k ht g
 rw [smul_mul_assoc,mul_smul_comm,map_smul,map_smul,hu,smul_zero,smul_zero]
-- geometry of support: before budget
variable {Y:Set Vantage}(c:ℝ)
def WallBefore : Prop := ∀ x∈ tsupport r.val, x (3:Axis)+A.realWidth P 3<c
def WallAfter : Prop := ∀ x∈tsupport r.val, c+A.realWidth P 3<x (3:Axis)
lemma test_apart (B:P.Apron)(s:SampleDose)(b:P.WallBefore A r c)(f:P.WallAfter B s c): Disjoint (P.spacePrice A r) (P.spacePrice B s):= by
 refine Set.disjoint_left.mpr fun p g v=>?_
 obtain ⟨i,h,g⟩:= Set.mem_iUnion₂.mp g; obtain ⟨k,p,v⟩:= Set.mem_iUnion₂.mp v -- p shadow!
 obtain ⟨_,g⟩:= abs_le.mp (g 3); obtain ⟨v,_⟩:= abs_le.mp (v 3)
 linarith only [b i h,f k p,v,g]
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
