import YM.SU5.FiniteGaugeData.Tapestry.Motif
set_option autoImplicit false
set_option synthInstance.maxSize 24000
set_option maxHeartbeats 490000
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tapestry
open Function Filter NormedSpace SU Lat Lattice Cube Finset MeasureTheory RG Wilson Metric
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Kronecker Topology ComplexOrder ENNReal Classical
open Rush Scroll Peaks Stencil Tenant Tap Tulip Branch Fir Scree Advance Reflect Window Laurent Next.Free Bloch Drapes Spire Lifted Skye Sound Precision Tree Push.SectorMeasure Next.SectorChange Common Fock
open Satin
attribute [local instance] opCStarAlgebra
open Py Py.Rate LocalLimit Preparation Journey Vale FullBill
open Nacre Mir Phase RP
open Altitude Heat Pastry
open PiTensorProduct (tprod)

/-!
# Wallet costs on finitely many test factors, w/r support. Uniform-on-ball
estimates for particular seminorm families can be stated in this language, but
we'll state directly for `Pocket`, to treat cost of given written combinations.
Basically pay a projective-norm-like toll for product terms with one support
sequence & observing height; no closure/nondegeneracy claim. Not giving a
global cost as supports & observing levels vary either (need additional work
when using any such adaptivity, and we'll pay for certain such thinnings later).
-/
set_option quotPrecheck false
variable (K:Calibration)(S T: BillOfWork)(n i:ℕ)
variable {x y:Cloud (Dome K)}
def fountainHeads : Subalgebra ℂ (Cloud (Dome K)):= colonnade (Set.Iic n) (fun i=> bay K (S i) true)
local notation "Ψ"=> fountainHeads K S n
lemma prePrice : fountainHeads K S n ≤ shorter (Dome K) n:= curveAbove n (P:={f|Officer (Set.Iic n) (fun i=> bay K (S i) true) f}) (Officer.oneX ..) (fun x p y q=>Officer.inMult _ _ p q) (fun x p=> Officer.visible _ _ p Set.Subset.rfl)
lemma payMotif (x:Employee S)(p: Clocked (K:=K) S n x): motif K S x∈ fountainHeads K S n:= officer_stone (Set.Iic n) (fun i=>bay K (S i) true) (x:=employ K S x) (p:=⟨⟨n,p⟩,(fun i=>locatesBadge ..),fun i t=> p _ (lt_of_not_ge (fun p=>t p))⟩) -- arg f vs x tune
lemma coin_mono (p:∀ i,i≤n→ S i⊆T i)(h:n≤ i): fountainHeads K S n ≤fountainHeads K T i:=makesWay (Set.Iic n) (Set.Iic i) _ _ (Set.Iic_subset_Iic.mpr h) (fun i v=> tallerBay K _ _ (p i v))
lemma anyWords (x:Cloud (Dome K))(h:x∈shorter (Dome K) n): ∃ S:BillOfWork, x∈fountainHeads K S n:=by
 apply boarded (P:={f:ℕ→ Dome K| Altitude.Enough n f}) (M:=fun x=> ∃ S:BillOfWork,x∈fountainHeads K S n) ?_ ?_ ?_ ?_ h
 · intro f h; obtain ⟨S,x,rfl⟩:=badges_location K f; exact ⟨S,payMotif K S n x h⟩
 · exact ⟨fun _=> ∅,(fountainHeads ..).zero_mem⟩
 · rintro x y _ _ ⟨S,p⟩ ⟨T,t⟩; let B:BillOfWork:=fun i=> S i∪ T i; exact ⟨B,(fountainHeads K B n).add_mem (coin_mono K S B n n (fun i u=> subset_union_left) le_rfl p) (coin_mono K T B n n (fun i u=> subset_union_right) le_rfl t)⟩
 rintro z x u ⟨S,p⟩; exact ⟨S,(fountainHeads K S n).smul_mem p z⟩ -- notation S shadow?

inductive Pocket : ℝ→ Cloud (Dome K) → Prop where
 | stone (x:Employee S) : Clocked (K:=K) S n x → Pocket (nectar n x) (motif K S x)
 | no : Pocket 0 0
 | blend {x y a b} : Pocket a x → Pocket b y → Pocket (a+b) (x+y)
 | shade {x a} (z:ℂ) : Pocket a x→ Pocket (‖z‖*a) (z • x)
 | fully {x a b}: a≤ b → Pocket a x→ Pocket b x
variable {K S n}
namespace Pocket
variable {u:ℝ}(h: Pocket K S n u x)
include h
lemma populated : x∈ fountainHeads K S n:=by
 induction h with
 | stone x h=> exact payMotif K S n x h
 | no=> exact (fountainHeads ..).zero_mem
 | shade z a u=> exact (Ψ).smul_mem u z
 | blend _ _ p q=> exact (Ψ).add_mem p q
 | fully _ _ u=> exact u
lemma priced : 0≤u:=by induction h with| stone x _=> exact licensedN n x | no=> exact le_refl _| shade z _ p=> exact mul_nonneg (norm_nonneg _) p| blend _ _ p q=> exact add_nonneg p q| fully h _ p=> exact p.trans h
lemma funded : x∈ shorter (Dome K) n:= prePrice K S n h.populated
-- cost triangle functional estimate: can use to read multiple things
variable {A:Type*}[NormedAddCommGroup A][NormedSpace ℂ A] (F:Cloud (Dome K) →ₗ[ℂ] A){b:ℝ}
lemma bequeath (p:0≤b) (q:∀ x:Employee S, Clocked (K:=K) S n x→ ‖F (motif K S x)‖≤ b*nectar n x): ‖F x‖ ≤ b*u:=by
  induction h with
  | stone x h=> exact q x h
  | no=> rw [map_zero,mul_zero,norm_zero]
  | @blend _ _ a c _ _ h g=> rw [map_add,mul_add]; exact (norm_add_le ..).trans (add_le_add h g)
  | @shade x a z _ t=> rw [map_smul,norm_smul]; exact (mul_le_mul_of_nonneg_left t (norm_nonneg _)).trans_eq (by ring)
  | fully h _ u=> exact u.trans (mul_le_mul_of_nonneg_left h p)
lemma bilAsk (A B:Cloud (Dome K)→ₗ[ℂ]ℂ) (p:0≤b)(q:∀ x:Employee S, Clocked (K:=K) S n x→ ‖A (motif K S x)-B (motif K S x)‖≤ b*nectar n x): ‖A x-B x‖ ≤ b*u:= h.bequeath (A-B) p q
omit h
lemma register {I:Type*}(s:Finset I)(f:I→ Cloud (Dome K))(v:I→ℝ)(q:∀ i∈s,Pocket K S n (v i) (f i)): Pocket K S n (∑ i∈s,v i) (∑ i∈s,f i):= by
 induction s using Finset.induction_on with| empty=> simpa using Pocket.no (K:=K) (S:=S) (n:=n)| insert a s v ih=> rw [sum_insert v,sum_insert v]; exact .blend (q a (mem_insert_self ..)) (ih fun i t=> q i (mem_insert_of_mem t))
end Pocket
lemma issued {x:Cloud (Dome K)} : x∈ fountainHeads K S n↔ ∃ C:ℝ,Pocket K S n C x:=by
  refine ⟨fun p=> ?_,fun ⟨x,v⟩=> v.populated⟩; apply boarded (P:={f|Officer (Set.Iic n) (fun i=>bay K (S i) true) f}) (M:=fun x=>_) ?_ ⟨_,Pocket.no⟩ ?_ ?_ p
  · intro f (t:Officer _ _ f); obtain ⟨x,rfl⟩:= motif_represents K S f t.observes; exact ⟨_, .stone x (t.visible _ _ Set.Subset.rfl)⟩
  · rintro x y p t ⟨A,H⟩ ⟨B,u⟩; exact ⟨_,.blend H u⟩
  rintro t x p ⟨C,h⟩; exact ⟨_,.shade t h⟩
end YM.CF.Buffered.Afterglow.Tapestry
#print axioms YM.CF.Buffered.Afterglow.Tapestry.issued
#print axioms YM.CF.Buffered.Afterglow.Tapestry.anyWords
#print axioms YM.CF.Buffered.Afterglow.Tapestry.Pocket.bequeath
