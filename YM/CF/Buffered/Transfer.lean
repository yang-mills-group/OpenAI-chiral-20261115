import YM.CF.Buffered.DonorGram
import YM.CF.Graph.Learn

/-!
# Actual ratio transfer at one fixed period

Delta and pressure supplied **before normalization**, as per needed cases of
ms rec-delta and presrec. This is the independent proof of the transfer, NOT
those input estimates. Sharp lower obtained from donor lower with loss; also
works for varying tilts as long as comparisons in force. Resolve complex
phase of both offset multiplications, do not assume reality or positivity
of CapP denominators. This proof needs just fixed-period estimates (m⁴ will
be a parameter in the constants). To avoid additional high estimates on
vacua, rec-upper etc we prove along an actual subsequential limit: given
SHARP convergence for the marked reading, the difference of ratios tends
to zero. (Writing the difference using bounded sharp ratio and a donor
lower.) No uniform bound across m assumed. All before the selected-period
limit.
-/
set_option autoImplicit false
set_option synthInstance.maxSize 16000
set_option maxHeartbeats 500000
noncomputable section
namespace YM.CF.Buffered
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset Cube SU Fock Lat Spire Scroll MeasureTheory Mesa ProbabilityTheory Peaks Drapes Rush Precision Tree Push.SectorMeasure Next.SectorChange Tulip Jet Tap Laic Dial Paige Vault Pec Skye Pastry Cascade Phase Brace Scree RG Spark RP Gloss Branch Reflect Window Vale Girt
open Py (Vestal Cape)
open Reed (Fine)
open Advance Heat
open scoped Topology BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Matrix.Norms.L2Operator ComplexOrder
attribute [local instance] opCStarAlgebra
section integration
variable {N m B L : Side}
lemma mark_linear (f g : FC (Single N)) (x : Phys N) (a : ℂ) : letterRead (f+g) x= letterRead f x+ letterRead g x ∧ letterRead (a • f) x=a* letterRead f x := by
  simp only [letterRead, ContinuousLinearMap.comp_apply]; rw [act_add,act_smul,map_add,map_smul]; exact ⟨rfl,rfl⟩
lemma mark_bound (f : FC (Single N)) (x : Phys N) : ‖letterRead f x‖ ≤ ‖f‖*‖x‖ := by
  apply (norm_inner_le_norm (𝕜:=ℂ) (mateK N) (acts f x)).trans; rw [(tickB N).2,one_mul]; exact Graph.spentS _ f x
variable {l : Loom N} (t : Measurable l) {f g : Mark N} (p : Envelope f) (q : Envelope g)
include t p
lemma mark_pay : Envelope (f ∘ drawn l) := Env.along p (drawn_m l t)
variable {T : Orbit N → Phys N} (u : Integrable T (city N))
include t p u
lemma mark_integrable : Integrable (fun V=> letterRead (f (drawn l V)) (T V)) (city N) := by
  obtain ⟨C,h⟩:= p.cost; let μ:=city N; let F(V : Orbit N):=f (drawn l V); let H(x : FC (Single N)×Phys N):=letterRead x.1 x.2; have he:Continuous H := (beamL N).continuous.comp ((acts_cont.comp continuous_fst).clm_apply continuous_snd)
  have hf : AEStronglyMeasurable F μ := (mark_pay t p).meas.aestronglyMeasurable; have hk := he.comp_aestronglyMeasurable (hf.prodMk u.aestronglyMeasurable)
  change Integrable (H ∘ fun V=>(F V,T V)) μ
  exact (u.norm.const_mul C).mono' hk (Eventually.of_forall fun i=> (mark_bound (F i) (T i)).trans (mul_le_mul_of_nonneg_right (h _) (norm_nonneg _)))
include q
lemma mark_add : markedRead (f+g) l T=markedRead f l T+markedRead g l T := by
  unfold markedRead; simp_rw [Pi.add_apply, (mark_linear _ _ _ 0).1]; exact integral_add (mark_integrable t p u) (mark_integrable t q u)
omit t p q u
lemma mark_smul (a : ℂ) : markedRead (a•f) l T=a*markedRead f l T := by unfold markedRead; simp_rw [Pi.smul_apply, (mark_linear _ 0 _ _).2]; exact integral_const_mul ..
end integration
section fixed
variable {m B L : Side} {j : ℕ} {ho : Odd L.val} {Z : Pricing j L ho (Thread j)}{e : ℝ}
variable (P : Grasp Z B e) (X Y : GramM (CSide m B)) (R : Loom (CSide m B))
def num0 (A : Mark (CSide m B)) := markedRead A R (Graph.recX P X R)
def vac0 := Complex.exp (- X.v)* partitionZ X P R
lemma num_zeroEq (f : Mark (CSide m B)) : num0 P X R f = Complex.exp (-X.v)* markedRead f R (denZ X P R) := by unfold num0 markedRead Graph.recX; simp_rw [map_smul]; exact integral_const_mul ..
lemma order_one : vac0 P X R=num0 P X R 1 := by rw [num_zeroEq, markvac]; rfl
lemma same_ratio (f : Mark (CSide m B)) : num0 P X R f / vac0 P X R = markedRead f R (denZ X P R)/partitionZ X P R := by rw [num_zeroEq,vac0, mul_div_mul_left _ _ (Complex.exp_ne_zero _)]
lemma part_ne_zero (u : vac0 P X R≠0) : partitionZ X P R ≠ 0 := right_ne_zero_of_mul u
private lemma rec_paid (A : GramM (CSide m B)) (u : Integrable (denZ A P R) (city _)) : Integrable (Graph.recX P A R) (city _) := u.smul (Complex.exp (-A.v))
variable (T : Measurable R) (x : Integrable (denZ X P R) (city _)) (y : Integrable (denZ Y P R) (city _))
variable {d : ℝ}
def Delta (d : ℝ) := ∀ V, ‖Graph.recX P X R V - Graph.recX P Y R V‖ ≤ d
variable (p : Delta P X Y R d)
include T x y p
lemma rec_apply (f : Mark (CSide m B)) (h : Envelope f) {w : ℝ} (v : ∀ i, ‖f i‖ ≤ w) : ‖num0 P X R f-num0 P Y R f‖ ≤ w*d := by
  let F(V : Orbit (CSide m B)):=f (drawn R V); let α:=Graph.recX P X R; let β:= Graph.recX P Y R; have he:0≤w:= (norm_nonneg (f (1,1))).trans (v _)
  change ‖(∫ i, letterRead (f (drawn R i)) (Graph.recX P X R i) ∂city _) - (∫ i, letterRead (f (drawn R i)) (Graph.recX P Y R i) ∂city _)‖ ≤ _; rw [←integral_sub (mark_integrable T h (rec_paid P R X x)) (mark_integrable T h (rec_paid P R Y y))]; refine (norm_integral_le_of_norm_le_const (C:=w*d) ?_).trans_eq ?_
  · apply Eventually.of_forall; intro i; change ‖letterRead (F i) (α i)-letterRead (F i) (β i)‖≤ _; rw [←map_sub]; exact (mark_bound ..).trans (mul_le_mul (v _) (p i) (norm_nonneg _) he)
  simp
lemma transfer_vac : ‖vac0 P X R-vac0 P Y R‖ ≤ d := by
  rw [order_one,order_one]; apply (rec_apply P X Y R T x y p _ (Girt.rite_c (1:FC _)) (show ∀ i : Fields _, ‖(1:Mark _) i‖≤1 from fun i=> (show ‖(1:FC _)‖=1 from norm_one ..).le)).trans (by rw [one_mul])
lemma transfer_lower (w : ℝ) (a : w≤ ‖vac0 P Y R‖) (e : d≤ w/2) : w/2 ≤ ‖vac0 P X R‖ := by
  have he:= transfer_vac P X Y R T x y p; rw [norm_sub_rev] at he; have hx:= norm_sub_norm_le (vac0 P Y R) (vac0 P X R); linarith
-- specialized to real rec-sup comparison with a LOSS allowed for denominators
lemma transfer_ratio {l B₀ D : ℝ} (L : 0 < l) (a : l≤ ‖vac0 P Y R‖) (e : d≤ l/2)
    (f : Mark (CSide m B)) (h : Envelope f) (v : ∀ i, ‖f i‖ ≤ B₀) (k : ‖num0 P X R f / vac0 P X R‖ ≤ D) :
    ‖num0 P X R f / vac0 P X R-num0 P Y R f/vac0 P Y R‖ ≤ (B₀+D)*d/l := by
  let A:= num0 P X R f; let B':=num0 P Y R f; let Z:=vac0 P X R; let U:=vac0 P Y R; let Φ:=A/Z; let φ:= B'/U
  have hv := transfer_lower P X Y R T x y p l a e; have hp:Z≠0:=norm_pos_iff.mp ((half_pos L).trans_le hv); have hx:U≠0:= norm_pos_iff.mp (L.trans_le a)
  have hr:= transfer_vac P X Y R T x y p; have hu:(Φ-φ)*U=(A-B')-Φ*(Z-U):=by unfold Φ φ; field_simp; ring
  change ‖Φ-φ‖≤ _; rw [le_div_iff₀ L]; apply (mul_le_mul_of_nonneg_left a (norm_nonneg (Φ-φ))).trans; rw [←norm_mul, hu, add_mul]
  exact (norm_sub_le ..).trans (add_le_add (rec_apply P X Y R T x y p f h v) ((norm_mul ..).trans_le (mul_le_mul k hr (norm_nonneg _) ((norm_nonneg _).trans k))))
end fixed
namespace Burn
def stage (n : ℕ) := n.sqrt.sqrt -- floor fourth root of horizon
lemma stage_iff (n k : ℕ) : k ≤ stage n ↔ k^4≤n := by rw [stage,Nat.le_sqrt', Nat.le_sqrt', ←pow_mul]
lemma tend_stage : Tendsto stage atTop atTop := tendsto_atTop.2 fun k=> (eventually_ge_atTop (k^4)).mono fun _ h=> (stage_iff ..).mpr h
-- n horizon, b₀ fixed calibration, K=K_b-1 for rec-delta
def depth (b₀ n : ℕ) := n-1-b₀-stage n-1
lemma tend_depth (b₀ : ℕ) : Tendsto (depth b₀) atTop atTop := by
  refine tendsto_atTop.2 fun k=> ?_
  filter_upwards [eventually_ge_atTop (2*(k+2+b₀)+2), tend_stage.eventually (eventually_ge_atTop 2)] with i p h
  have he : 2*stage i ≤ i := by
    apply Nat.le_trans _ ((stage_iff ..).1 le_rfl); exact le_trans (b:=stage i ^ 2) (by nlinarith) (pow_le_pow_right₀ (by omega) (by omega))
  unfold depth; omega
def bill (m n b₀ : ℕ) (M : ℝ) := (2:ℝ)^(-(depth b₀ n:ℝ)/2) * Real.exp (M * m^4)
def presrec (m : ℕ) (C : ℝ) := Real.exp (-C*m^4)
lemma bill_shrinks (b₀ m : ℕ) (M : ℝ) : Tendsto (fun n => bill m n b₀ M) atTop (𝓝 0) := by
  have he : Tendsto (fun n=>(Real.log 2 * -(depth b₀ n:ℝ))/2) atTop atBot := by
    apply Tendsto.atBot_div_const; positivity
    exact (tendsto_neg_atTop_atBot.comp (tendsto_natCast_atTop_atTop (R:=ℝ)|>.comp (tend_depth b₀))).const_mul_atBot (Real.log_pos (by norm_num))
  unfold bill; simp_rw [Real.rpow_def_of_pos (by norm_num : (0:ℝ)<2),←mul_div_assoc]; simpa using (Real.tendsto_exp_atBot.comp he).mul_const (Real.exp (M*m^4))
end Burn
end YM.CF.Buffered
