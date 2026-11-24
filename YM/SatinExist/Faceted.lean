import YM.SatinExist.BelmontX
import YM.SatinExist.SliceBill
set_option autoImplicit false
set_option maxHeartbeats 390000
set_option synthInstance.maxSize 30000
set_option maxRecDepth 5000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter NormedSpace SU Lat Lattice Cube Finset MeasureTheory RG Wilson Metric
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Kronecker Topology ComplexOrder ENNReal Classical
open Rush Scroll Peaks Stencil Tenant Tap Tulip Branch Fir Scree Advance Reflect Window Laurent Next.Free Bloch Drapes Spire Lifted Skye Sound Precision Tree Push.SectorMeasure Next.SectorChange Common Fock
open Satin Heat Fock Analysis SlabMark MeshClock SatinVerification Vacancy
attribute [local instance] opCStarAlgebra
open Mir Haro Tap Dial Cascade Girt Pastry
open Afterglow Tapestry Tower Py Py.Rate Py.Rate.LocalLimit Preparation Journey Six OneCup Xara
open CF.Lamour CF.Lamour.Bridge.Celeste
namespace Spine
variable (P:Spine)
local notation "W"=>P.calibration
local notation "Λ"=>P.par
local notation "Ψ"=>P.run
local notation "π"=>P.width
local notation "H"=>P.large
local notation "ℒ"=>P.law
variable (S T:Finset Cover)(s i:ℕ) (E:P.Test→ₗ[ℂ]ℂ)(r:MatterWard P.calibration E)
local notation "m" i:max=> momentm Ψ (P.nomadic i) (s+1)
local notation "U!" S:max=> wingspan Λ π S
local notation "Σ" F:max=> slice W E F
local notation "ℳ" i:max=> side Ψ (P.nomadic i) s
local notation "t" i:max=> side Ψ (P.nomadic i) (s+1)
local notation "τ" i:max F:max=> distribute Ψ H (s+1) (P.nomadic i) F
-- passed stencil close in all norm pay. income for slice automatic even without extensive. fixed s.
abbrev grown (S:Finset Cover)(F:P.Test) : P.Test := ⟨block Ψ H s (P.nomadic i) (P.engine i) S F.val,broadCompile W (U! S) (booked ..)⟩
lemma grown_bay (F:P.Test): P.grown s i S F ∈ bay W (U! S) true:= (Tapestry.locates ..).2 (booked ..) -- ordering
lemma shippingStd (F:P.Test)(p:F∈bay P.calibration S true) : BQueue (U! S) (fun i=>(P.grown s i S F).val) (P.conveying s 1 F).val:= queue_easy Ψ H ℒ s P.history F.val S p 1
lemma cutsave (F:ℕ→ P.Test)(A:P.Test)(b:BQueue S (fun i=> (F i).val) A.val):BQueue S (fun i=> (slice W E (F i)).val) (slice W E A).val:=by
 -- use toast_limit with ANY m qualified. fixed support. choose once
 let d j:= ‖E (toastPoint W S j)‖; let l:=∑ i:Evens S,d i; obtain ⟨i,v⟩:= (turning Ψ H 0 S).exists
 let U(a:P.Test)(p:a∈bay W S true)(z:ℝ)(w:pay a.val z): pay (Σ a).val (l*z):=fun n x=>toast_limit (K:=W) E S _ v.hosp a p z d (w _) (fun _=>le_rfl) n x
 have hl:0≤l:= sum_nonneg (fun i _=> norm_nonneg _)
 obtain ⟨g,h,⟨c,hc,u,q⟩,x⟩:=b
 refine ⟨fun i=>cuts_local E S _ (g i), cuts_local E S _ h, ⟨l*c+1,by positivity, fun i v=> le_trans (U A h c u i v) (by linarith), q.mono (fun i w n p=>le_trans (U (F i) (g i) c w n p) (by linarith))⟩,fun e v=>?_⟩
 let X:=e/(l+1); have hp:0<X:=div_pos v (by linarith); filter_upwards [x X hp] with i hQ; have hx:F i-A∈bay W S true:=(bay W S true).sub_mem (g i) h
 intro n V; change ‖((Σ (F i)-Σ A).val n V)‖≤_
 rw [←map_sub]; exact (U (F i-A) hx X hQ n V).trans ((mul_le_mul_of_nonneg_right (show l≤l+1 by linarith) hp.le).trans (le_of_eq (mul_comm _ _ |>.trans (div_mul_cancel₀ _ (by linarith)))))
open Hierarchy
include r
variable (a c:Cover)(A B:GemUT)(z:ℝ)
-- use upper bill at any i late: linear extension agrees on Fock part. Slice multiplication estimator
lemma doubts (p:nodeC a∈ S)(l:nodeC c∈ T)(d:Navy.Sizing Λ s)(ζ:0≤z)(q:Disjoint (wingspan P.par P.width S) (wingspan P.par P.width T))
   (h:∀ x:Cover,nodeC x∈wingspan P.par P.width S→∀ y:Cover,nodeC y∈wingspan P.par P.width T→∀ J Q:GemUT, ‖E (sheen W x J*sheen W y Q)‖ ≤ z) :
   ∀ᶠ i:ℕ in atTop,∀ w:Fields (side Ψ (P.nomadic i) (s+1)), ∃ k:ℂ, (τ i (slice W E ((P.grown s i S (sheen W a A))*(P.grown s i T (sheen W c B)))).val) w=k • 1∧ ‖k‖ ≤ (25*DiamondX*z):=by
 let F:= sheen W a A; let D:= sheen W c B
 have hd:= P.history.finance (s+1); have he:Tendsto P.nomadic atTop atTop := (P.law.pick.grow_i.comp P.history.growsA).tendsto_atTop
 filter_upwards [hd, he.eventually (turning Ψ H (s+1) (U! S)), he.eventually (turning Ψ H (s+1) (U! T)), he.eventually (turning Ψ H (s+1) (U! S ∪ U! T)), (P.amount_go s).eventually_gt_atTop (2*aliasLaw Λ)] with i pY tY tZ t' hZ w
 let n:=P.nomadic i; let k:=P.engine i; let A':= U! S ∪ U! T; let V:=P.grown s i S F; let V':=P.grown s i T D; let X:= portLX Ψ H (s+1) n w; let N:=side Ψ n (s+1)
 obtain ⟨I,J⟩:= OneCup.examinator (Y:=Ψ) H A' (s+1) n E t'.hosp
 refine ⟨I (X (V*V')),termBy (Y:=Ψ) H A' (s+1) n E I J ((bay W A' true).mul_mem ?_ ?_) w,?_⟩
 · apply (Tapestry.locates ..).2; exact (booked Ψ H s _ _ S _).mono subset_union_left -- order check
 · apply (Tapestry.locates ..).2; exact (booked Ψ H s _ _ T _).mono subset_union_right
 have v:Wing (Satin.region (U! S) N) (Satin.region (U! T) N) I z:=by
    intro a ha b hb c hc w hw
    exact diagram Ψ H (s+1) n (U! S) (U! T) E r q I J z ζ h _ _ _ _ (by simpa using ha.2.2) (by simpa using hb.2.2) (by simpa using hc.2.2) (by simpa using hw.2.2) ha.2.1 hb.2.1 hc.2.1 hw.2.1 ha.1 hb.1 hc.1 hw.1
 have hx: legalAt Ψ s n k := ⟨pY.depth,pY.enters⟩
 change ‖I (distribute Ψ H (s+1) n (V.val*V'.val) w)‖≤_
 rw [(distribute_arith Ψ H (s+1) _ _ _ 0).2.1,Pi.mul_apply]; change ‖I (((τ i (block Ψ H s n k S F.val)) w)*((τ i (block Ψ H s n k T D.val)) w))‖≤_
 have ht:F∈bay W S true:=shine_local W S _ _ p
 have ht':D∈bay W T true:=shine_local W T _ _ l
 rw [reserved Ψ H s S _ _ hx ht tY, reserved Ψ H s T _ _ hx ht' tZ, show aboveD Ψ H s n k F.val w=_ from whole_bill Ψ H s n k pY _ _ w, show aboveD Ψ H s n k D.val w=_ from whole_bill Ψ H s n k pY _ _ w]; simp_rw [sum_mul,mul_sum,map_sum]
 refine (norm_sum_le ..).trans ((sum_le_sum (fun i _=> (norm_sum_le ..).trans (sum_le_sum (fun p' _=> highIn Ψ H S T s n k pY a c A B z ζ p l d hZ I v _ _ w)))).trans_eq ?_); simp [SU.F]; ring
#print axioms doubts
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
