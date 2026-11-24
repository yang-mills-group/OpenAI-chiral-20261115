import VerifiedSatinSelectedSectors
import YM.SU5.Reconstruction.Footprint
set_option autoImplicit false
set_option synthInstance.maxSize 30000
set_option maxRecDepth 6500
set_option maxHeartbeats 440000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.Reconstruction
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory
  RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder
  InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Heat Fock Analysis SlabMark Vacancy SatinVerification
open Selected PhaseChoice PhaseChoice.SameCharacter PhaseChoice.Theory
open Tapestry Tapestry.Altitude Tapestry.Exhibition

/-!
# No drift of the physical local support on actual finite histories.

Budget for all `frameBudget` sites for every paying horizon, and all requested access levels
including top UV, staying within the *same* silhouette. True torus distances there once
its period is past threshold at the bottom level. See `the construction notes`.
-/
variable {Λ : Preparation} {l : ℕ} (Y : Course Λ (VolumeCape.Dream.Nimbus l)) (H : Real.exp 1 ≤ Λ.x)
local notation "K" => tent Y H

section
variable {A : Set RSpace} {s : ℕ}

open Set
/-- One detailed support budget for the input curve of all factors, localized throughout. -/
theorem uniform_support {J : Calibration} {wide : Bool} {x : Cloud (Dome J)} (h : x∈ jetty Λ l J wide (handstamp A) (Set.Iic s)) :
    ∃ F : BillOfWork,(∀ i : ℕ, silhouette Λ l i (F i) ⊆ A) ∧ x∈fountainHeads J F s := by
  let P:=fun F:BillOfWork=>∀ i:ℕ, silhouette Λ l i (F i) ⊆ A
  apply boarded (P:={f:sequenceOf J|Officer (Set.Iic s) (fun i => keep Λ l i J wide (handstamp A)) f})
    (M:=fun x : Cloud (Dome J) => ∃ F: BillOfWork, P F ∧ x∈ fountainHeads J F s) ?_ ?_ ?_ ?_ h
  · intro f t; have ht : Officer (Set.Iic s) _ f := t
    choose G v a using fun i => (show ∃ S:Finset Cover, f i∈ bay J S wide∧ printedHere Λ l i S (handstamp A) from ht.observes i)
    exact ⟨G,fun i=> supported_iff.mp (a i),officer_stone (Set.Iic s) (fun i=>bay J (G i) true) (show Officer (Set.Iic s) (fun i=> bay J (G i) true) f from ⟨ht.toll,fun i=>widerBay J (G i) wide (v i),ht.forbids⟩)⟩
  · exact ⟨fun _=>∅,fun n=>by simp [silhouette],Subalgebra.zero_mem _⟩
  · rintro x y _ _ ⟨S,p,h⟩ ⟨T,t,v⟩; let Z (i:ℕ):= S i ∪ T i
    refine ⟨Z,fun i=>?_,?_⟩
    · unfold Z; rw [silhouette_union]; exact Set.union_subset (p _) (t _)
    exact (fountainHeads J Z s).add_mem (coin_mono J S Z s s (fun i h=> Finset.subset_union_left) le_rfl h)
      (coin_mono J T Z s s (fun i h=> Finset.subset_union_right) le_rfl v)
  rintro z x _ ⟨S,h,p⟩; exact ⟨S,h,(fountainHeads J S s).smul_mem p z⟩

lemma future_budget (F : BillOfWork) (h : ∀ i, silhouette Λ l i (F i) ⊆ A) (n : ℕ) :
    silhouette Λ l n (frameBudget F Λ l n) ⊆ A := supported_iff.mp (frame_lines F n Λ l (fun i _=>supported_iff.mpr (h i)))

lemma actual_supported {i k s : ℕ} (t : Tapestry.Pay Y s i k) (F : BillOfWork) (x : Altitude.Cloud (Dome K))
    (e : x∈ fountainHeads K F s) : AtSupport false (Satin.region (frameBudget F Λ l s) (Journey.side Y i s)) (attire (breathing Y H s i k x)) :=
  textureBudget Y H F s i k t x (Tapestry.issued.mp e).choose_spec

lemma pinhole_budget (s : ℕ) {u : Set RSpace} {x : Dome (tent Y H)} (h : x∈ keep Λ l s K true (handstamp u)) :
    pinhole _ s x∈ jetty Λ l K true (handstamp u) (Set.Iic s) := pokes _ _ (Set.mem_Iic.mpr (le_refl s)) h
end

-- uniform over all n, including top level on paid histories.
lemma position_clock (i n : ℕ) :
    (Journey.side Y i n).val*gaugeMesh Λ n = ((Journey.side Y i 0).val: ℝ)/2 := by
  have ht : (Journey.side Y i n).val=Λ.R.L.val^n * (Journey.side Y i 0).val := by simpa using refine_side Y i 0 n
  change (((Journey.side Y i n).val:ℝ))*_= _
  rw [ht, gaugeMesh]; push_cast; field_simp

include H
lemma full_distances {A : Set RSpace} (p : Bornology.IsBounded A) : ∀ᶠ i in atTop, ∀ (n : ℕ) (F : Finset Cover),
    (∀ x∈ F, location Λ n x∈ A) → FullDistances F (Journey.side Y i n) := by
  obtain ⟨R,h⟩ := p.subset_closedBall (0:RSpace)
  let N(i:ℕ) := Journey.side Y i 0
  have he : Tendsto (fun i : ℕ=> ((N i).val:ℝ)) atTop atTop := tendsto_natCast_atTop_atTop.comp (goes Y H 0)
  filter_upwards [he.eventually_gt_atTop (4*R)] with i (hR:(4:ℝ)*R < ((N i).val:ℝ)) n F g
  let m:= Journey.side Y i n; let L:= gaugeMesh Λ n
  intro x px y py; apply lift_eq_iff.mpr; refine ⟨(map_sub ..).symm,fun j=>?_⟩
  have hp(v:Cover)(w:v∈F) : |(v j:ℝ)*L| ≤ R:=by
    let z:= location Λ n v
    have h₁:‖z‖ ≤ R:=by simpa using (show dist z 0 ≤ R from Metric.mem_closedBall.mp (h (g v w)))
    have hz : z j=(v j:ℝ)*L:= congrFun (spatial_units Λ n v) j
    rw [←hz]; exact (norm_le_pi_norm z j).trans h₁
  have ht : 0 < L := gaugeMesh_pos ..; have hh := position_clock Y i n
  have hs : R+R < (m.val:ℝ)*L:= by
    change (m.val:ℝ)*L=(↑(N i).val:ℝ)/2 at hh; linarith only [hh,hR]
  have hv : ((y j-x j:ℤ):ℝ)*L < (m.val:ℝ)*L := by
    push_cast; linarith only [hs,(abs_le.mp (hp y py)).2,(abs_le.mp (hp x px)).1]
  have hz : ((x j-y j:ℤ):ℝ)*L < (m.val:ℝ)*L := by
    push_cast; linarith only [hs,(abs_le.mp (hp x px)).2,(abs_le.mp (hp y py)).1]
  have he1 : y j-x j < (m.val:ℤ) := by exact_mod_cast (mul_lt_mul_iff_left₀ ht).mp hv
  have he2 : x j-y j < (m.val:ℤ) := by exact_mod_cast (mul_lt_mul_iff_left₀ ht).mp hz
  change - ((m.val*2:ℕ):ℤ)<2*(y j-x j) ∧ 2*(y j-x j) ≤ ((m.val*2:ℕ):ℤ); omega
omit H
lemma distances_separate {S T : Finset Cover} {N : Side} (v : FullDistances (S∪T) N)
    (e : Detached Λ l S T) {x y} (h : x∈Satin.region S N) (t : y∈Satin.region T N) :
    2*(Advance.nearZero (aliasLaw Λ)+distanceLaw l) < separation x y := by
  obtain ⟨x,hx,rfl⟩ := mem_image.mp h; obtain ⟨y,ht,rfl⟩ := mem_image.mp t
  by_contra! k
  rw [separation_comm] at k
  have hT:=YM.Work.E08.lift_mem_box k
  rw [v y (Finset.mem_union.mpr (Or.inr ht)) x (Finset.mem_union.mpr (Or.inl hx))] at hT
  exact e.act Λ l x hx y ht hT
lemma unwrapped_inj {A : Finset Cover} {m : Side} (p : FullDistances A m) :
    Set.InjOn (wrap (More m)) A := by
   intro x hx y hy h
   have v := p x hx y hy
   rw [h,sub_self] at v
   exact (sub_eq_zero.mp (v.symm.trans (by simp))).symm

end YM.CF.Buffered.Afterglow.Tower.Reconstruction
