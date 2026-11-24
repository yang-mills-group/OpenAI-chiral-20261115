import Anomaly.Cover.Velum
import YM.SU5.FiniteGaugeData.Tapestry.Chroma
set_option autoImplicit false
set_option synthInstance.maxSize 26000
set_option maxHeartbeats 450000
set_option quotPrecheck false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tapestry
open Function Filter NormedSpace SU Lat Lattice Cube Finset MeasureTheory RG Wilson Metric
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Kronecker Topology ComplexOrder ENNReal Classical
open Rush Scroll Peaks Stencil Tenant Tap Tulip Branch Fir Scree Advance Reflect Window Laurent Next.Free Bloch Drapes Spire Lifted Skye Sound Precision Tree Push.SectorMeasure Next.SectorChange Common Fock
open Satin
attribute [local instance] opCStarAlgebra
open CF.Swell Rill CF.Swell.Sonar
open Py Py.Rate LocalLimit Preparation Journey Vale FullBill
variable {Λ:Preparation}{l:ℕ}(Y:Course Λ (VolumeCape.Dream.Nimbus l)) (H:Real.exp 1≤Λ.x) (s i:ℕ)
namespace StageW
local notation "Ψ"=>tent Y H
local notation "ts"=>momentm Y i s
local notation "N" i:max=>side Y i s
lemma local_cov {x:Family Ψ} (g:covariant (exhibit Y H s i x)): covariant (x ts):= reflect_ps (n:= (Ψ).c ts) (m:=side Y i s) (x ts) (terrain Y H (Y.ir i) s) g
where reflect_ps {n m:Side}(f:Mark n)(p:n=m)(g:covariant (arrange _ _ p f)):covariant f:= by subst m; exact g
variable {I:Type*}[Nonempty I](k:I→ℕ) (S:Finset Cover)
lemma impartial (f:Swatch S)(p:Roomy S (N i))(h:covariant (present Y H s i S f)): Neutral Ψ (render S Ψ f):= onceNeutral (texture S Ψ f) ((terrain Y H (Y.ir i) s).symm ▸ (Roomy.seats p)) (local_cov Y H s i h)
lemma organized {J:Type}[Fintype J](P:J→(j:I)→ Mark (side Y (k j) s))(p:∀ j, Roomy S (N (k j)))(A:∀ u j,AtSupport false (Satin.region S (N (k j))) (P u j)∧covariant (P u j)) (E:∀ u, Menu (T:=fun i:I=>FC (Single (N (k i)))) (fun (j:I) v=> P u j (replant S (N (k j)) v))) : ∃ Q:I→J→ Swatch S, TotallyBounded (Set.range Q) ∧∀ i j, present Y H s (k i) S (Q i j)=P j i ∧ Neutral Ψ (render S Ψ (Q i j)):=by
 choose Q₀ v using fun j i=> present_mend Y H s (k i) S (p i) (A j i).1
 let Q(i j):=Q₀ j i
 refine ⟨Q, captureTuple Q (fun j=>?_),(fun i j=>⟨v j i,impartial Y H s (k i) S (Q i j) (p i) ((v j i).symm ▸ (A j i).2)⟩)⟩
 let g i:=Q i j; exact carpetΞ P j g (fun _=>v j _) (E j) p
where
 carpetΞ(P:J→(j:I)→ Mark (side Y (k j) s))(j:J)(F:I→Swatch S)(v:∀ i,present Y H s (k i) S (F i)=P j i)(hp:Menu (T:=fun i:I=>FC (Single (N (k i)))) (fun i x=>P j i (replant S (N (k i)) x)))(p:∀ j,Roomy S (N (k j))) : TotallyBounded (Set.range F):=by
    choose m u using fun i:I=> eyes_native Y H s (k i) S (Roomy.seats (p i))
    apply captureTuple; intro e; let A(i):= P j i; let V(i):=replant S (N (k i)); let Tup(i):=m i e
    apply paletteTB; have hv(i:I)(y): ‖Tup i y‖ ≤ ‖y‖:= (u i 0 (1,1) e).1 y
    let ψ(i:I)(x:PairsC):= Tup i (A i (V i x))
    have h: Menu ψ:=by
       obtain ⟨c,z,G⟩:= hp.budget; refine ⟨Deal.along (fun (i:I) (x:FC (Single (N (k i))))=> Tup i x) hp.deal (?_),c,z,fun i x=> (hv ..).trans (G ..)⟩
       intro ε he; refine ⟨ε,he,fun i x y b=>?_⟩; rw [dist_eq_norm,← map_sub]; exact lt_of_le_of_lt (hv i _) (by simpa only [←dist_eq_norm] using b)
    apply h.congr; intro i x; rw [(u i (F i) x e).2,v]; -- tune
end StageW
end YM.CF.Buffered.Afterglow.Tapestry
