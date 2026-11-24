import SatinFixedContrastNovember4
import SatinThinFusionPaleness
/-! # Purchasing the wards for fusion -/
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 3500
set_option maxHeartbeats 350000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Heat Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
open Lamour.Bridge.Celeste
open Lamour.Bridge.Celeste.Morn
namespace Spine
variable (P:Spine)
local notation "K"=> P.calibration
local notation "T"=> P.Test
open Papal Regis.Head Gleam
open Clock Clock.Hookah Clock.Hookah.Blaze
open Preparation.Yoke Yoke.Travel Regis.Head.Garland
open QuadClock Again Pressure
open Tapestry.Exhibition Aria Casting Six
open CF.Pannier.Chancel CF.Py.Rate.LocalLimit.Preparation.Yoke
open Worth Pays CF.BProof
open SatinNucleus
lemma trip_pure (X:Cover)(s:ℕ) : PureGauge K (P.tariffQ witnessZ s X):=by
 apply (P.pale_iff _).1; intro m x
 change (loneTrip X).issued witnessZ (hat P.par.R.L P.par.x s) ((K).c m) x∈ _; unfold Trip.issued pension chalkOp
 exact Submodule.mem_span_singleton.mpr ⟨_,rfl⟩
lemma base_pure (x:P.Spectrum0 3)(f r:ℕ): PureGauge K (P.basePlay x f r).F:= by
 let q:= gaugePlane K
 change P.centeredQ x r _ ∈ q; refine q.sub_mem (q.smul_mem _ (P.trip_pure ..)) (q.smul_mem _ ?_); exact (pure_unit K).1
lemma canvas_pure {ι:Type} (A:ι→P.Apron)(S:Finset ι)(h:Axis→ℕ)(s:ℕ)
    (u:∀ j,0<h j)(t:∀ i∈ S,(A i).s ≤ s)(e:∀ i∈ S,∀ j,(A i).zoom P s j≤h j)
    (ρ:ι→ℂ)(p:∀ i∈ S,PureGauge K (A i).F): PureGauge K (P.canvas A S h s u t e ρ).F:=by
 let q:= gaugePlane K; refine q.sum_mem fun i y=> q.smul_mem _ ?_; exact P.convey_pure (A i).s _ (p i y) _
lemma cinema_pure (x:P.Spectrum0 3)(f r:ℕ)(v:ℕ→ℕ)(a:ℕ→(ℕ×ℕ)→ℝ)(q:ℕ→ Coalition)(u:StrictMono v)(i:ℕ): PureGauge K (P.cinema x f r v a q u i).F:= P.canvas_pure _ _ _ _ _ _ _ _ (fun k _=>P.base_pure ..)
variable (s:ℕ) (b:Bool)
lemma sensing_mono {D S:Finset Cover}(h:D ⊆ S): P.sensing D s b ≤ P.sensing S s b:= by
 refine Submodule.span_mono fun x v=>?_
 obtain ⟨A,B,W,t,u,v⟩:= v; exact ⟨A,B,W,t,u.trans h,v⟩
lemma shift_senses {S:Finset Cover}{F:T}(j:Axis)(z:ℤ)(v:F ∈ P.sensing S s b): P.shifts j z F∈P.sensing (plow K j z S) s b:=by
 let q:=P.sensing (plow K j z S) s b; let v':= P.shifts j z; change v' F ∈ q
 refine Submodule.span_induction (p:=fun f _=>v' f∈q) (fun f p=>?_) (by rw [map_zero]; exact q.zero_mem)
    (fun _ _ _ _ h e=> by rw [map_add]; exact q.add_mem h e) (fun r _ _ h=>by rw [map_smul]; exact q.smul_mem _ h) v
 obtain ⟨A,B,W,d,u,v,h,e⟩:=p
 exact Submodule.subset_span (show _∈_ from ⟨_,_,_,union_subset (image_subset_image (subset_union_left.trans d)) (image_subset_image (subset_union_right.trans d)), image_subset_image u, P.pin_relocate s A B j z v,relocate_dressed K b A B W j z h,P.shifts_keep j z e⟩)
lemma dress_senses {F G:T}{D S:Finset Cover}(p:F∈bay K D true)(q:F∈enclave K)(z:PureGauge K F)(v:G∈P.sensing S s b):
    F*G∈P.sensing (D∪S) s b:=by
 let w:=P.sensing (D∪S) s b
 refine Submodule.span_induction (p:=fun g _=> F*g∈w) (fun g h=>?_) (by rw [mul_zero]; exact w.zero_mem)
    (fun _ _ _ _ h e=>by rw [mul_add]; exact w.add_mem h e) (fun a _ _ h=>by rw [mul_smul_comm]; exact w.smul_mem _ h) v
 obtain ⟨A,B,W,t,u,r,h,g'⟩:=h; obtain ⟨i,d⟩:= (turning P.run P.large s (D∪W)).exists
 refine Submodule.subset_span (show _∈_ from ⟨A,B,D∪W,t.trans subset_union_right,union_subset_union (Subset.refl _) u,r,?_, (enclave K).mul_mem q g'⟩)
 have he:(F*g)∈bay K (D∪W) true:= Subalgebra.mul_mem _ (tallerBay K _ true subset_union_left p) (tallerBay K _ true subset_union_right (x:=(g:T)) (dressed_test K b _ _ W t h)) -- maybe x implicit
 apply Six.descend K b A B (D∪W) _ d (t.trans subset_union_right) ((Tapestry.locates ..).1 he)
 intro x; change F.val _ x * g.val _ x∈ _; rw [pin_reads (pure_pale K z _ _),Algebra.smul_mul_assoc, one_mul]; apply Submodule.smul_mem; exact dressedMatrix K b A B W h _ _ -- arg D
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
#print axioms YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine.dress_senses
#print axioms YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine.cinema_pure
