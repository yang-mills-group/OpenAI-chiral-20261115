import YM.SU5.FiniteGaugeData.Tapestry.Cloudburst
import YM.SU5.MacroSix.Comparison
import Mathlib.Geometry.Manifold.PartitionOfUnity

/-!
# Optional weak Ward hypothesis: suffice sampled compactly-supported
smooth SU transformations. Can also keep the physical function fixed when
paying the births and deaths on fixed physical regions. Not an approximate
Ward rule in the limit!
-/

set_option autoImplicit false
set_option synthInstance.maxSize 24000
set_option maxHeartbeats 460000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Pockets
open Function Filter NormedSpace SU Lat Lattice Cube Finset MeasureTheory RG Wilson Metric
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Kronecker
  Topology ComplexOrder ENNReal Classical ContDiff Manifold
open Rush Scroll Peaks Stencil Tenant Tap Tulip Branch Fir Scree Advance Reflect Window Laurent
  Next.Free Bloch Drapes Spire Lifted Skye Sound Precision Tree Push.SectorMeasure
  Next.SectorChange Common Fock Satin Tapestry Haro Tap Cascade Dial Mir Girt Nacre Pastry Phase RP
attribute [local instance] opCStarAlgebra

structure Painted (p : GPhysical) : Prop where
  finite_ : HasCompactMulSupport p
  smooth : ∀ i j : SU.F, ContDiff ℝ ∞ (fun x : RSpace ↦ fund (p x) i j)

private def lunar (t : ℝ) := Complex.exp ((((2*Real.pi/5)*t:ℝ):ℂ) * Complex.I)
private def phases (t : ℝ) (i : SU.F) := if i=0 then (star (lunar t))^4 else lunar t
private def halfSpin (t : ℝ) := Matrix.diagonal (phases t)
private lemma lunar_norm (t : ℝ) : ‖lunar t‖ = 1 := Complex.norm_exp_ofReal_mul_I _
private lemma lunar_star (t : ℝ) : star (lunar t)*lunar t=1:= scale_unit_self (lunar_norm t)
private lemma lunar_one : lunar 1=SU.z:= by unfold lunar SU.z; push_cast; congr 1; ring

private lemma backed_spin (t : ℝ) : halfSpin t ∈ unitary (Op SU.F) := by
  have he : star (halfSpin t)=Matrix.diagonal (fun i ↦ star (phases t i)) := by
    ext i j; by_cases h : i=j <;> simp [halfSpin,h,Ne.symm]
  have ht (i : SU.F) : star (phases t i)*phases t i=1:= scale_unit_self (by
    by_cases h:i=0 <;> simp [phases,h,lunar_norm])
  apply Matrix.mem_unitaryGroup_iff.mpr
  rw [he]
  unfold halfSpin
  rw [Matrix.diagonal_mul_diagonal]; ext i j; by_cases h : i=j
  · subst j; rw [Matrix.diagonal_apply_eq,Matrix.one_apply_eq]; rw [mul_comm]; exact ht i
  simp [h]

private lemma det_spin (t : ℝ) : (halfSpin t).det=1:= by
  unfold halfSpin; rw [Matrix.det_diagonal]
  have he : (star (lunar t))^4*(lunar t)^4=1:=by rw [←mul_pow,lunar_star,one_pow]
  change ∏ i : Fin 5,_ = 1
  rw [←he]; norm_num [phases,Fin.prod_univ_succ]

private def orbitCenter (t : ℝ) : SU.E := ⟨⟨halfSpin t,backed_spin t⟩,det_spin t⟩
private lemma orbit_origin : orbitCenter 0=(1:SU.E) := by
  apply SU.group.mat_injective; change Matrix.diagonal (phases 0)=1
  rw [show phases 0=(fun _ ↦ 1) by
    funext i; by_cases h : i=0 <;> simp [phases,h,lunar]]; simp
private lemma orbit_peak : orbitCenter 1=SU.central := by
  apply SU.group.mat_injective; change Matrix.diagonal (phases 1)=Matrix.diagonal _
  congr 1; funext i; unfold phases; rw [lunar_one]; split
  · rw [show (star SU.z)^4=SU.z from ?_]
    apply mul_right_cancel₀ (show (SU.z)^4≠0 from pow_ne_zero _ (z_prim.ne_zero (by decide)))
    rw [←mul_pow,show star SU.z*SU.z=1 from scale_unit_self SU.z_n,one_pow]
    exact (pow_succ' SU.z 4 ▸ SU.z_prim.pow_eq_one).symm
  rfl

private lemma orbit_smooth (i j : SU.F) : ContDiff ℝ ∞ fun t : ℝ ↦ fund (orbitCenter t) i j := by
  have he : ContDiff ℝ ∞ lunar := ((Complex.ofRealCLM.contDiff.comp (contDiff_const.mul contDiff_id)).mul contDiff_const).cexp
  change ContDiff ℝ ∞ fun t : ℝ ↦ Matrix.diagonal (phases t) i j
  by_cases h : i=j
  · subst j; by_cases h : i=0
    · simp only [Matrix.diagonal_apply_eq, phases, if_pos h]; exact (Complex.conjCLE.contDiff.comp he).pow 4
    simpa only [Matrix.diagonal_apply_eq, phases, if_neg h] using he
  simpa only [Matrix.diagonal_apply_ne _ h] using (contDiff_const (c:=(0:ℂ)) (n:=∞) (𝕜:=ℝ) (E:=ℝ))

-- manifold scopes don't force globally open. choose bounded plateau even if B unbounded closed.
theorem usesPaint (A B : Set RSpace) (h : Disjoint A B) (u : IsCompact A) (v : IsClosed B) :
    ∃ p : GPhysical, Painted p ∧ (∀ᶠ x in nhdsSet A, p x=SU.central) ∧
      ∀ᶠ x in nhdsSet B, p x=1 := by
  obtain ⟨r,e⟩ := u.isBounded.subset_ball 0
  let T := Metric.ball (0:RSpace) r
  have ht : Disjoint (B∪Tᶜ) A := Set.disjoint_left.mpr fun a w v ↦
    w.elim (fun w ↦ Set.disjoint_left.mp h v w) (fun w ↦ w (e v))
  obtain ⟨f,z,t,g⟩ := exists_contMDiffMap_zero_one_nhds_of_isClosed (modelWithCornersSelf ℝ RSpace)
    (n:=⊤) (v.union (isOpen_ball.isClosed_compl)) u.isClosed ht
  let p := orbitCenter ∘ f
  have hx : ∀ᶠ x in nhdsSet (B∪Tᶜ), p x=1 := z.mono fun x h ↦ (congrArg orbitCenter h).trans orbit_origin
  refine ⟨p,⟨HasCompactMulSupport.of_mulSupport_subset_isCompact (isCompact_closedBall (0:RSpace) r) (Set.Subset.trans ?_ ball_subset_closedBall),
    fun i j ↦ (orbit_smooth i j).comp (contMDiff_iff_contDiff.mp f.contMDiff)⟩,
      t.mono (fun x h ↦ (congrArg orbitCenter h).trans orbit_peak), hx.filter_mono (nhdsSet_mono Set.subset_union_left)⟩
  intro x g; by_contra d; exact g (hx.self_of_nhdsSet x (Or.inr d))

open Py Py.Rate Py.Rate.LocalLimit Preparation Journey
variable {K : Calibration} (Λ : Preparation) (s : ℕ)
def PaintedSplit (M : Prices K) := Split M ∧ ∀ p : GPhysical, Painted p →
  GatesPrice M (restrictG Λ s p) ∨ MantlesPrice M (restrictG Λ s p)

lemma paintedSplit_of_ordinary {M : Prices K} (x : Comparison M) : PaintedSplit Λ s M :=
  ⟨x.1,fun _ _ ↦ x.2.imp (fun w ↦ w _) (fun w ↦ w _)⟩
end YM.CF.Buffered.Afterglow.Pockets
namespace YM.CF.Buffered.Afterglow.Pockets
#print axioms usesPaint
end YM.CF.Buffered.Afterglow.Pockets
