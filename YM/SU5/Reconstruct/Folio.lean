import YM.SU5.Reconstruct.Card
set_option autoImplicit false
set_option linter.unusedVariables false
set_option synthInstance.maxSize 30000
set_option maxRecDepth 6000
set_option maxHeartbeats 185000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.Reconstruction
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Heat Fock Analysis SlabMark Vacancy SatinVerification
open Tapestry Tapestry.Altitude PhaseChoice
variable {Λ:Preparation}{l:ℕ}(Y:Course Λ (VolumeCape.Dream.Nimbus l))(H:Real.exp 1≤Λ.x)
local notation "K" => tent Y H
open Tower.Selected Set MeshClock Tapestry.Exhibition
open SelectionAnalysis Vacancy.Average
variable {i k:ℕ→ℕ}{I:ℕ→Family (tent Y H)→ℕ→ℂ}{E:ℕ→Family (tent Y H)→ℂ}
  {L:Rack Λ l}{B:Clay Λ l}{T:ℕ→ℕ→Tariff}{t:ℕ→Tariff}(D:Fashion Y H i k I E L B T t)
  (G:GroundExtension (i:=i) (k:=k) (E:=E) Y H)
local notation "Dₚ" => D.toExhibition
local notation "V" => D.univ_
local notation "Q" => G.history
local notation "Qt" => G.clipped
local notation "χ" => Dome (tent Y H)
local notation "O" => Altitude.Cloud (Dome (tent Y H))
local notation "P₀" s:max => vistaFinish Y H s (Dₚ)

variable (s:ℕ) (j:Axis)
section pages
variable {σ: Type}(W:σ→ Set RSpace)(f:∀ i,Pol Y H (W i))(Z:List σ)
noncomputable abbrev Board := ∀ i, StripCard Y H D s j (W i) (f i)
local notation "A"=> Board Y H D s j W f
open StripCard
variable {W f s j}
variable (C:Board Y H D s j W f)(v:σ→RSpace)
local notation "∂" i:max=> StripCard.starts Y H D (s:=s) (j:=j) (U:=W i) (x:=f i) (C i) (v i)
local notation "Υ" i:max=> StripCard.ends Y H D (s:=s) (j:=j) (U:=W i) (x:=f i) (C i) (v i)
def OfferedOn := Z.Pairwise (fun a b=> StripCard.ends Y H D (s:=s) (j:=j) (U:=W a) (x:=f a) (C a) (v a) j < StripCard.starts Y H D (s:=s) (j:=j) (U:=W b) (x:=f b) (C b) (v b) j)
lemma OfferedOn_mono {z:List σ}(p: z.Sublist Z) (o:OfferedOn Y H D Z C v) : OfferedOn Y H D z C v := List.Pairwise.sublist p o
lemma OfferedOn_plus (z:RSpace) : OfferedOn Y H D Z C (fun i=> v i+z) ↔ OfferedOn Y H D Z C v:=by
 have he (a b:σ): StripCard.ends Y H D (s:=s) (j:=j) (U:=W a) (x:=f a) (C a) (v a+z) j < StripCard.starts Y H D (s:=s) (j:=j) (U:=W b) (x:=f b) (C b) (v b+z) j ↔ (Υ a) j < (∂ b) j:=by
   unfold StripCard.starts StripCard.ends; simp only [Pi.add_apply]; constructor <;> intro p <;> linarith
 exact ⟨fun t=>t.imp (fun {_ _} p=> (he _ _).1 p), fun t=>t.imp (fun {_ _} p=> (he _ _).2 p)⟩
lemma OfferedOn_apart (p:OfferedOn Y H D Z C v) : Z.Pairwise (fun a b=> Disjoint (carried (v a) (W a)) (carried (v b) (W b))) :=
  p.imp (fun {i i'} h=>Set.disjoint_left.mpr (fun _ v₁ v₂ => (not_lt_of_ge ((StripCard.contained Y H D (s:=s) (j:=j) (U:=W i') (x:=f i') (C i') _ _ v₂).1.trans (StripCard.contained Y H D (s:=s) (j:=j) (U:=W i) (x:=f i) (C i) _ _ v₁).2)) h))
noncomputable def finer (u:ℕ) (p:s ≤ u): Board Y H D u j W f:=fun i=> StripCard.higher Y H D G (s:=s) (j:=j) (U:=W i) (x:=f i) (C i) u p
lemma OfferedOn_finer (u:ℕ) (p:s≤u): OfferedOn Y H D Z (finer Y H D G C u p) v ↔ OfferedOn Y H D Z C v:=by simp only [OfferedOn, finer, ends_h,starts_h]
lemma chart_open : IsOpen (setOf (OfferedOn Y H D Z C)) := by
 classical
 induction Z with
 | nil=> rw [show setOf _ = _ from (show setOf (OfferedOn Y H D [] C)=Set.univ from Set.eq_univ_of_forall (fun _=> List.Pairwise.nil))]; exact isOpen_univ
   -- ∩-open topology on pi positions
 | cons a Z ih=>
   have he : setOf (OfferedOn Y H D (a::Z) C) = setOf (OfferedOn Y H D Z C) ∩ ⋂ i∈ Z.toFinset,setOf (fun v : σ→ RSpace => StripCard.ends Y H D (s:=s) (j:=j) (U:=W a) (x:=f a) (C a) (v a) j < StripCard.starts Y H D (s:=s) (j:=j) (U:=W i) (x:=f i) (C i) (v i) j):=by
     ext x; simp [OfferedOn,and_comm]
   rw [he]; exact ih.inter (isOpen_biInter_finset (s:=Z.toFinset) fun i p=> isOpen_lt ((continuous_apply j).comp ((continuous_const (y:=physPos Λ (finishBit Y H D (C a)))).add (continuous_apply a))) ((continuous_apply j).comp ((continuous_const (y:=physPos Λ (fromBase Y H D (C i)))).add (continuous_apply i))))
end pages
end YM.CF.Buffered.Afterglow.Tower.Reconstruction
