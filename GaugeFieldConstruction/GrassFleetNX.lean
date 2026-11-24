import GaugeFieldConstruction.Pimper
import GaugeFieldConstruction.AcornPathNX
import GaugeFieldConstruction.Synod
set_option autoImplicit false
set_option synthInstance.maxSize 24000
set_option maxHeartbeats 130000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.XGarden
open Function Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG WilsonStartup Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Matrix.Norms.L2Operator Classical
open Buffered Buffered.Region FlightFlux Fluxim Work Tensor
open Fock Tulip Lat Spire Phase Cube Scroll Paige Vault Phase Spire Branch
open Push.SectorMeasure
attribute [local instance] opCStarAlgebra
variable {K d t r u c h a b h0:ℝ}{j k:ℕ}{m B n:Side}
namespace MastTin
open Shield Echo Ledger Jet
local notation "GS"=> SU.group
local notation "Λ"=> CSide m B
local instance nxNightInst1 (I:Type)[Fintype I][DecidableEq I]:MeasurableSpace (Op I):=borel _
local instance nxNightInst2 (I:Type)[Fintype I][DecidableEq I]:BorelSpace (Op I):=⟨rfl⟩
variable (o:Seat n) {X:Hubber n}{p:BudgetPoint}
open Salt Pastry Hake Urn Levier Hive Nacre Rush Peaks
open Next.SectorChange.Motion Ione
open Scree.Ing.Ivey Scree.Ing.Ivey.ShoreQ
variable {i:Axis}
lemma MS_upNX(f:Lit n)(q:MicroShipNX p X f a)(r:a≤ b): MicroShipNX p X f b:=⟨q.1.trans r,q.2.1,q.2.2.1,fun i=> (q.2.2.2 i).mono r⟩
lemma MS_scaleNX (f:Lit n)(q:MicroShipNX p X f a)(z:ℂ): MicroShipNX p X (z • f) (‖z‖*a):=by
 have h:=micro_ms (show Micro p X f a from ⟨q.1,q.2.1,q.2.2.1,fun i _=>q.2.2.2 i⟩) z
 refine ⟨h.1,h.2.1,h.2.2.1,fun i=>?_⟩; let L:=z • (ContinuousLinearMap.id ℝ ℂ); have ht:‖L‖≤ ‖z‖ := (norm_smul z (ContinuousLinearMap.id ℝ ℂ)).le.trans (mul_le_of_le_one_right (norm_nonneg _) ContinuousLinearMap.norm_id_le); exact (q.2.2.2 i).linear L ht
lemma MS_plusNX(f g:Lit n)(q:MicroShipNX p X f a)(r:MicroShipNX p X g b):MicroShipNX p X (f+g) (a+b):=by
 have h:=micro_a (show Micro p X f a from ⟨q.1,q.2.1,q.2.2.1,fun i _=>q.2.2.2 i⟩) (show Micro p X g b from ⟨r.1,r.2.1,r.2.2.1,fun i _=>r.2.2.2 i⟩)
 exact ⟨h.1,h.2.1,h.2.2.1,fun i=> (q.2.2.2 i).add (r.2.2.2 i)⟩
lemma MS_zeroNX : MicroShipNX p X (0:Lit n) 0:=⟨le_rfl,⟨measurable_const,0,fun _=>norm_zero.le⟩,fun _ _ _=>rfl,fun i=> allows_const _ norm_zero.le⟩ -- tune
lemma MS_sumNX {I:Type*} (s:Finset I)(f:I→Lit n)(g:I→ℝ)(p:BudgetPoint)(X:Support (More n))(q:∀ i∈s,MicroShipNX p X (f i) (g i)) : MicroShipNX p X (∑ i∈s,f i) (∑ i∈s,g i):=by
 classical
 induction s using Finset.induction_on with | empty=> simp only [sum_empty]; exact MS_zeroNX | @insert i s v ih=>simp only[sum_insert v]; exact MS_plusNX _ _ (q i (mem_insert_self ..)) (ih fun j p=> q j (mem_insert_of_mem p))
variable {μ:ℕ}{A B:Paper n}
lemma CanoeNX_up (f:DonauNX μ p o h A a)(v:a≤b):DonauNX μ p o h A b:=by obtain ⟨X,t,b⟩:=f; exact ⟨X,t,b.trans v⟩
lemma CanoeNX_plus(f:DonauNX μ p o h A a)(s:DonauNX μ p o h B b) : DonauNX μ p o h (A+B) (a+b):=by
 obtain ⟨V,t,z⟩:=f; obtain ⟨S,q,k⟩:=s; refine ⟨fun i=> V i+ S i,fun i=> ⟨MS_plusNX _ _ (t i).1 (q i).1, fun p=>?_⟩,?_⟩
 · rw [Pi.add_apply,(t i).2 p,(q i).2 p,add_zero]
 simp_rw [mul_add,sum_add_distrib]; exact add_le_add z k
lemma CanoeNX_scale (f:DonauNX μ p o h A a)(v:ℂ):DonauNX μ p o h (v • A) (‖v‖*a):=by
 obtain ⟨V,t,z⟩:=f; refine ⟨fun i=>‖v‖*V i,fun i=>⟨MS_scaleNX _ (t i).1 v,fun p=>?_⟩,?_⟩
 · rw[Pi.smul_apply,(t i).2 p,smul_zero]
 simp_rw [mul_left_comm (papW _ _ _),← Finset.mul_sum]; exact mul_le_mul_of_nonneg_left z (norm_nonneg _)
lemma CanoeNX_zero:DonauNX μ p o h 0 0:=⟨0,fun _=>⟨MS_zeroNX,fun _=>rfl⟩,by simp⟩
lemma CanoeNX_sum {I:Type*} (s:Finset I)(f:I→Paper n)(D:I→ℝ)(q:∀ i∈s,DonauNX μ p o h (f i) (D i)):DonauNX μ p o h (∑ i∈s,f i) (∑ i∈s,D i):=by
 classical
 induction s using Finset.induction_on with|empty=>simp only[sum_empty]; exact CanoeNX_zero _| @insert i s v ih=> simp only[sum_insert v]; exact CanoeNX_plus _ (q i (mem_insert_self ..)) (ih fun j e=>q j (mem_insert_of_mem e))
lemma moorKulNX(i:Wa n)(v:DomainP (CanoeNX o μ) i)(f:Lit n)(q:MicroShipNX p (CanoeNX o μ) f c): DonauNX μ p o h (isolate i f) (papW n h i*c):=by
 refine ⟨Pi.single i c,fun l=>?_,?_⟩
 · by_cases p:l=i
   · subst l; exact ⟨by simpa [isolate] using q, fun k=> (k v).elim⟩
   exact ⟨by simp only [isolate,Pi.single_eq_of_ne p]; exact MS_zeroNX, fun _=> Pi.single_eq_of_ne p _⟩
 apply le_of_eq; rw [sum_eq_single i]
 · simp
 · intro k p v; simp [v]
 simp
end MastTin
end YM.CF.XGarden
end
