import YM.SU5.Reconstruction.Cross.Smoothed
set_option autoImplicit false
set_option synthInstance.maxSize 30000
set_option maxRecDepth 6500
set_option maxHeartbeats 500000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.Reconstruction.Atlas
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory
  RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder
  InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Heat Fock Analysis SlabMark Vacancy SatinVerification
open Selected Tapestry Tapestry.Altitude Tapestry.Exhibition
open Set OS.Semigroup MeshClock Germ
variable {Λ : Preparation} {l : ℕ} (Y : Course Λ (VolumeCape.Dream.Nimbus l)) (H : Real.exp 1 ≤ Λ.x)
local notation "K" => tent Y H
local notation "L₀" => Λ.R.L.val
local notation "Μ" => timeMesh Λ
open _root_.YM.SelectionAnalysis Vacancy.Average
section average_product
variable {A B Z I:Type*} [NormedAddCommGroup Z] [NormedSpace ℂ Z]
  [Fintype A] [Fintype B] [Nonempty B] [DecidableEq A]
variable {D:Hilbert}
private lemma scattered (F:A → B→ D.Op) (t: List A)
    {p q:A→B} (v:∀ x∈t,p x=q x) : (t.map fun i=> F i (p i)).prod = (t.map fun i=> F i (q i)).prod:=by
 induction t with
 | nil=> rfl
 | cons i t ih=>simp only [List.map_cons,List.prod_cons]; rw [v i (List.Mem.head ..),ih (fun i e=>v i (List.Mem.tail _ e))]
private lemma scalar_point (z:A)(h:(A→B)→Z): Average.center h=Average.center (fun x:B=>Average.center (fun y:Average.Other A z → B => h ((Equiv.funSplitAt z B).symm (x,y)))):=by rw [←Average.trade (Equiv.funSplitAt z B).symm h, Average.domino] -- tune
-- products of smeared factors are averages over all positions of the raw products, assuming independently l.Nodup. No arbitrary shifts after smear on fort.
lemma averaging_op (F:A → B → D.Op) (t: List A) (h:t.Nodup) :
    Average.center (fun u:A→B=> (t.map (fun i=> F i (u i))).prod)= (t.map (fun i=> Average.center (F i))).prod := by
  induction t with
  | nil=> simp only [List.map_nil,List.prod_nil,Average.constant]
  | cons i t ih=>
    obtain ⟨v,u⟩:=List.nodup_cons.mp h
    rw [List.map_cons,List.prod_cons,← ih u,scalar_point i]; simp only [List.map_cons,List.prod_cons];
    let Q(q:A→B):=(t.map (fun i=> F i (q i))).prod
    let E:=Equiv.funSplitAt i B; let b₀:B:=Classical.arbitrary B; let u(p:Other A i→ B):=E.symm (b₀,p)
    have he(x)(z):Q (E.symm (x,z))=Q (u z):= scattered F t (by intro j t; unfold E u; unfold E; simp [show j≠i from fun e=>v (e ▸ t)]) -- tactic `..` trailing
    have hx:Average.center Q= Average.center (fun p=> Q (u p)):=by
       rw [scalar_point i]; change Average.center (fun x:B=>Average.center (fun z=> Q (E.symm (x,z))))=_; simp_rw [he,Average.constant]
    change Average.center (fun x:B=> Average.center (fun p:Other A i→ B=> F i (E.symm (x,p) i)*Q (E.symm (x,p))))= _*Average.center Q
    have hk(x:B)(p:Other A i→ B): E.symm (x,p) i=x:=by simp [E]
    rw [hx]; simp_rw [he,hk]
    unfold Average.center; -- distribute
    -- carefully map mul and scalar norms
    simp only [Algebra.smul_mul_assoc,Algebra.mul_smul_comm,_root_.Finset.sum_mul,_root_.Finset.mul_sum,← _root_.Finset.smul_sum]
    rw [_root_.Finset.sum_comm, smul_comm]
end average_product

section
variable (M:Mesh) {ι Z:Type*}[Fintype ι] [DecidableEq ι][NormedAddCommGroup Z] [NormedSpace ℂ Z]
-- update all positions in absolute slot times (no relative time), finite sum available passing through true chosen response at common levels.
noncomputable def disclose (x : ι→ seeMesh M) (t:ℕ×ℕ) (u : ι→Samples M t.2) : ι→seeMesh M := fun i=> x i + offsets M t.1 t.2 (u i)
noncomputable def smoothPositions (F : (ι→seeMesh M) → Z) (x:ι→ seeMesh M) (q:ℕ×ℕ) : Z :=
  Average.center (fun u:ι→Samples M q.2=> F (disclose M x q u))
lemma besidePositions (F : Set (ι→seeMesh M)) (x:ι→seeMesh M) (h:F∈𝓝 x) : ∀ᶠ t in nested,∀ u: (ι → Samples M t.2), disclose M x t u∈F :=by
  obtain ⟨δ,p,s⟩:=Metric.mem_nhds_iff.mp h
  apply eventually_curry_iff.mpr
  filter_upwards [(show Tendsto (fun i:ℕ=> ((mill M i:ℝ))) atTop (𝓝 0) from NNReal.tendsto_coe.mpr (vanishes M)).eventually (gt_mem_nhds p)] with i hi; apply Eventually.of_forall
  intro n u
  apply s; change dist _ x<δ
  apply (le_trans ?_ (le_refl (mill M i:ℝ))).trans_lt hi
  rw [dist_eq_norm]; apply (pi_norm_le_iff_of_nonneg (mill_pos M i|>.le)).mpr; intro a
  exact (by rw [Pi.sub_apply, ← dist_eq_norm]; exact offset_distance ..)
lemma smooth_fit (F:(ι→seeMesh M)→Z) (x:ι→seeMesh M) (h:ContinuousAt F x): Tendsto (smoothPositions M F x) nested (𝓝 (F x)) := by
 rw [Metric.tendsto_nhds]; intro ε e
 filter_upwards [besidePositions M (F ⁻¹' Metric.closedBall (F x) (ε/2)) x (h (Metric.closedBall_mem_nhds _ (half_pos e)))] with t ht
 apply (le_trans ?_ (le_refl (ε/2))).trans_lt (half_lt_self e)
 have hh: Average.center (fun _ : ι→Samples M t.2=> F x)=F x:= Average.constant _
 exact hh ▸ (show dist (smoothPositions M F x t) (Average.center (fun _ : ι→Samples M t.2=> F x)) ≤ _ from Average.norm_dist ht)
end
end YM.CF.Buffered.Afterglow.Tower.Reconstruction.Atlas
#print axioms YM.CF.Buffered.Afterglow.Tower.Reconstruction.Atlas.smooth_fit
