import YM.SU5.Reconstruct.Regions
set_option autoImplicit false
set_option synthInstance.maxSize 30000
set_option maxRecDepth 6000
set_option maxHeartbeats 270000
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
open Selected

/-!
# Identify at original observing resolution

The wide system gives physical measurements both-links on effective,
bare representatives need only first. But there is also a canonical notion
of narrow physical marks at s itself: the localObs of the FiniteGaugeData system.
We prove direct equivalence of readings and membership in a *local* set. -/
section physical
variable (i s k:ℕ)
local notation "N₀"=> side Y i s
variable (W: Dome (tent Y H)) {S:Finset Cover}

lemma atExecution (v: W.val∈ observ (tent Y H) S false) :
    let Z:= side Y i s; let A:= diagMark (exhibit Y H s i W.val); let T:= Satin.region S Z
    (exhibit Y H s i W.val)= toMark A ∧
    AtSupport false T (exhibit Y H s i W.val) ∧
    A∈ localObs Z -- all locations: edge both and every matter site in the support
      ((Finset.univ : Finset (Tenant.Edges (More Z))).filter fun t=> (t.1∈ T ∧ t.1+step t.2∈ T)) (sitesIn Z T) ∧
    ∀ k, Pay Y s i k →
      taking Y H i k (pinhole _ s W) = Y.texture i k s A := by
  intro Z A T
  have hz:= (obs_in ..).1 v
  obtain ⟨X,x,e⟩:= firstAppearance Y H s i (x:=W) (⟨S,hz.1⟩ : W∈vestibule K false)
  rw [roamsAttire] at x
  have he:A=X:=by unfold A; rw [x]; rfl
  have ea : exhibit Y H s i W.val=toMark A := x.trans (congrArg toMark he).symm
  have u:=exhibited Y H s i S hz.1.widen
  have t : AtSupport false T (toMark A):= ea ▸ u
  have h: covariant (toMark A):= ea ▸ Tapestry.validate (Y:=Y) (s:=s) (i:=i) H hz.2
  let TT:= ((Finset.univ : Finset (Tenant.Edges (More Z))).filter fun t=> (t.1∈ T ∧ t.1+step t.2∈ T))
  have p:A∈ localObs Z TT (sitesIn Z T):= by
    rw [mem_localObs]
    refine ⟨he.symm ▸ e,fun x y p=>?_,fun i=> t.allV (i,i),fun g x=> h g (x,x)⟩
    have he : Agrees T x y:= fun i a b=> p i (Finset.mem_filter.mpr ⟨Finset.mem_univ i,a,b⟩)
    exact t.dep (x,x) (y,y) he he
  refine ⟨ea,u,p,fun k v=>?_⟩
  rw [recordedAt Y H s i k v,actualRead,ea,(Y.true_read i k s ⟨A, fits_all p⟩ v.1 v.2).2.2] -- subtype defeq coe field A? tune
  rfl
end physical

section metric
variable (Λ:Preparation)(l s:ℕ)
-- convenient form of their geometry
noncomputable def realChartFootprint (S:Finset Cover) : Set RSpace :=
    ⋃ x∈S, Metric.closedBall (location Λ s x) (reserve Λ l * gaugeMesh Λ s)

lemma pos_eq (x:Cover) : location Λ s x = gaugePosition Λ s x:= by funext i; unfold location gaugePosition markZ gaugeMesh Tapestry.precisionAt; ring

lemma box_iff (x:Cover)(u:RSpace):
    u ∈ Metric.closedBall (location Λ s x) (reserve Λ l * gaugeMesh Λ s) ↔
        (fun i:Axis=> 2*u i) ∈ Tapestry.shield Λ l s x:= by
  let r:ℝ:= reserve Λ l
  have h:= positiveScale Λ s
  rw [Metric.mem_closedBall,dist_pi_le_iff (show 0 ≤ ((reserve Λ l):ℝ)*gaugeMesh Λ s from mul_nonneg (Nat.cast_nonneg _) (gaugeMesh_pos ..).le)]
  apply forall_congr'; intro i
  change dist (u i) ((x i / precisionAt Λ s)/2:ℝ) ≤ r* (1/(2*precisionAt Λ s)) ↔ |precisionAt Λ s*(2*u i)-↑(x i)|≤ r
  let v:=precisionAt Λ s; change dist (u i) ((x i/v)/2:ℝ) ≤ _ ↔ |v*(2*u i)-↑(x i)|≤ _
  have hx:0 < 2*v:= by change 0 < 2*Tapestry.precisionAt Λ s; positivity
  rw [Real.dist_eq, show u i-(↑(x i)/v)/ (2:ℝ)=(v*(2*u i)-↑(x i))/(2*v) by have hv : v ≠ 0:= h.ne'; field_simp, show r* (1/(2*precisionAt Λ s)) = r/(2*v) by unfold v; ring,abs_div,abs_of_pos hx,div_le_div_iff_of_pos_right hx]

lemma footprint_check (S:Finset Cover)(U:Set RSpace) : SupportedPhysically Λ l s S U ↔ realChartFootprint Λ l s S ⊆ U := by
  constructor
  · intro h x m; obtain ⟨j,e⟩:= Set.mem_iUnion.mp m; obtain ⟨p,e⟩:=Set.mem_iUnion.mp e
    have ht : (fun i:Axis=> (2*x i)/ (2:ℝ)) ∈ U:= h j p ((box_iff Λ l s j x).1 e)
    have hg : (fun i:Axis=> (2*x i)/ (2:ℝ))=x:=by funext; ring
    rwa [← hg]
  intro h x w z v
  let Z:RSpace:=fun i=> z i/2
  refine h (Set.mem_iUnion.mpr ⟨x,Set.mem_iUnion.mpr ⟨w,(box_iff Λ l s x Z).2 ?_⟩⟩)
  rwa [show (fun i=>2*Z i)=z from funext fun _=>by unfold Z; ring]
lemma foot_self (S:Finset Cover): SupportedPhysically Λ l s S (realChartFootprint Λ l s S):= (footprint_check Λ l s S _).2 Set.Subset.rfl
lemma foot_print (S:Finset Cover) : IsCompact (realChartFootprint Λ l s S):= Finset.isCompact_biUnion _ (fun _ _=> isCompact_closedBall ..)
lemma foot_cabin (S:Finset Cover): ∃ R:ℝ, 0<R ∧ realChartFootprint Λ l s S⊆ Tapestry.cabin R:=by
   obtain ⟨b,p,q⟩ :=canBound Λ l s S; exact ⟨_,p,(footprint_check Λ l s S _).1 q⟩
lemma foot_separation {A B:Finset Cover}{δ:ℝ}{j:Axis} (h:PhysicalHush (Λ:=Λ) (l:=l) s j A B δ) :
    ∀ x∈ realChartFootprint Λ l s A,∀ y∈ realChartFootprint Λ l s B, x j +δ ≤ y j:=by
  intro x p y q
  obtain ⟨a,t⟩:=Set.mem_iUnion.mp p; obtain ⟨t,w⟩:=Set.mem_iUnion.mp t
  obtain ⟨b,v⟩:=Set.mem_iUnion.mp q; obtain ⟨v,u⟩:=Set.mem_iUnion.mp v
  have he := h.2 0 a t b v
  have δ' (x:RSpace)(a:Cover)(p:x ∈ Metric.closedBall (location Λ s a) (reserve Λ l * gaugeMesh Λ s)): |x j-gaugePosition Λ s a j|≤ reserve Λ l * gaugeMesh Λ s:= by
    rw [← pos_eq _ _ _, ← Real.dist_eq]; exact (dist_pi_le_iff (by have hp:= gaugeMesh_pos Λ s; positivity)).1 (mem_closedBall.mp p) j
  simp only [Nat.add_zero] at he
  linarith only [(abs_le.mp (δ' x a w)).2,(abs_le.mp (δ' y b u)).1,he]
end metric
end YM.CF.Buffered.Afterglow.Tower.Reconstruction
