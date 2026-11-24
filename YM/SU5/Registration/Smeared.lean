import YM.SU5.Registration.WinterBands

/-!
# Field operator from energy blocks.

Test-variable budget is continuous on Schwartz space. Include actual
real translations (at the axis used for S). For convergent families of
such blocks with a common polynomial price, these estimates also pay the
whole-domain strong convergence, including on a *moving input in that
domain topology*. We'll derive such prices then use this for vanishing
extra padding. No assertion about arbitrary-point insertion operators
existing on this domain.
-/
set_option autoImplicit false
noncomputable section
namespace YM.SatinRegistration
open Set Filter Function MeasureTheory Spectral
open scoped Topology NNReal ENNReal BigOperators InnerProductSpace ComplexOrder Classical
open OS OS.Semigroup SatinEdge.RealSheet Boundary Probe Multiplier Roy CF.Buffered.Afterglow.Hierarchy.Seld
open Grading
variable {H : Hilbert} {a : Axis} (S : OS.Semigroup H a)
local notation "G" => bands S
local notation "U" => S.unit.translation

/-- Common for all fields/stamps & widths on one S. -/
abbrev radial := (bands S).domain
local notation "D" => radial S
variable (B : (bands S).Blocks) (w : PowerPaid S B)

def enact : Test4 →ₗ[ℂ] ( (radial S)→ₗ[ℂ] (radial S)) where
  toFun f := (smearedBlocks S B f).acts (usableBlocks S B f w)
  map_add' f g := by
    ext1 x; apply Subtype.ext; change (smearedBlocks S B (f+g)).reach x=(smearedBlocks S B f).reach x+(smearedBlocks S B g).reach x
    unfold Blocks.reach
    simp only [smearedBlocks,map_add,_root_.add_apply]; exact ((smearedBlocks S B f).series_usable (usableBlocks S B f w) x).tsum_add ((smearedBlocks S B g).series_usable (usableBlocks S B g w) x)
  map_smul' c f := by
    ext1 x; apply Subtype.ext; change (smearedBlocks S B (c • f)).reach x = c • (smearedBlocks S B f).reach x
    unfold Blocks.reach; simp only [smearedBlocks,map_smul,_root_.smul_apply,tsum_const_smul'']

lemma enact_blocks (f : Test4) (x : D) : (enact S B w f x).1=(smearedBlocks S B f).reach x:=rfl
lemma enact_tariff {C : ℝ} {r : ℕ} (h : PowerPrice S B r C) (f : Test4) (x : D) (k : ℕ) :
    (G).budget k (enact S B w f x).1 ≤ ((∑' n, tariffW n)*meterLoss r k C f a)*(G).budget (k+2+r+r) x.1 :=
  (smearedBlocks S B f).estimate (usableBlocks S B f w) (path_tariff S B r k C f h) _
lemma enact_distribution {ι : Type*} (f : Filter ι) (X : ι→ Test4) {x : Test4} (t : Tendsto X f (𝓝 x))
    (y : D) : (G).Approaches f (fun i=> enact S B w (X i) y) (enact S B w x y) := by
  intro k
  obtain ⟨r,C,hc,hp⟩ : PowerPaid S B := id w
  let C'(i:ι):= meterLoss r k C (X i-x) a
  have he : Tendsto C' f (𝓝 0) := by
    have ht:Tendsto (fun i=> X i-x) f (𝓝 0):=by simpa only [sub_self] using t.sub_const x
    exact ((meter_continuous r k C a).tendsto' 0 0 (meter_zero r k C a)).comp ht
  let P:= enact S B w
  change Tendsto (fun i=> (G).budget k ((P (X i) y).1-(P x y).1)) f (𝓝 0)
  refine squeeze_zero (fun _=> (G).budget_nonneg _ _) (fun i=> show _≤ (((∑' n, tariffW n))*C' i)*(G).budget (k+2+r+r) y.1 from ?_) ?_
  · rw [show (P (X i) y).1-(P x y).1=(P (X i-x) y).1 from (by rw [map_sub]; rfl)]
    exact enact_tariff S B w hp _ y k
  simpa only [mul_zero,zero_mul] using (he.const_mul ((∑' n, tariffW n))).mul_const ((G).budget (k+2+r+r) y.1)
lemma distribution (x : D) : Continuous (fun f=> (enact S B w f x).1) :=
  continuous_iff_continuousAt.mpr fun f => (Approaches.hilbert (G) (enact_distribution S B w (𝓝 f) _ (show Tendsto id (𝓝 f) _ from tendsto_id) x))

lemma flip_inner (C : (bands S).Blocks) (c : PowerPaid S C)
    (u : ∀ m n, (B.op m n).adjoint=C.op n m) (f : Test4) (x y : D) :
    inner ℂ (enact S B w f x).1 y.1= inner ℂ x.1 (enact S C c (bar f) y).1 := by
  apply (smearedBlocks S B f).adjointness (smearedBlocks S C (bar f)) (usableBlocks S B f w) (usableBlocks S C _ c) _ x y
  intro m n; change (valise S _ f).adjoint=valise S (C.op n m) (bar f); rw [←u]; exact (scenery S _ f).symm

lemma enact_closable (C : (bands S).Blocks) (c : PowerPaid S C)
    (u : ∀ m n, (B.op m n).adjoint=C.op n m) (f : Test4) :
    ((G).asPartial (enact S B w f)).IsClosable := by
  exact (G).closable _ (enact S C c (bar f)) (fun x y=> (flip_inner S B w C c u f x y).symm)

/-- A bounded operator acting diagonally in this grading. Preserve the domain. -/
lemma diagonal_mem (R : H.Op) (e : ∀ n, Commute R (cell S n)) (x : D) : R x.1 ∈ radial S := by
  intro k
  apply Summable.of_nonneg_of_le ((G).due_nonneg _ k) _ ((rapid x.2 k).mul_left ‖R‖)
  intro n; unfold Grading.due; rw [band, ← show R (cell S n x.1)=cell S n (R x.1) from DFunLike.congr_fun (e n).eq x.1,mul_left_comm ‖R‖]; exact mul_le_mul_of_nonneg_left (R.le_opNorm _) (weight_pos k n).le

def onDomain (R : H.Op) (e : ∀ n, Commute R (cell S n)) : (radial S) →ₗ[ℂ] (radial S) :=
  (R.toLinearMap.comp (D).subtype).codRestrict (radial S) (diagonal_mem S R e)
lemma onDomain_tariff (R : H.Op) (e : ∀ n, Commute R (cell S n)) (k : ℕ) (x : D) :
    (G).budget k (onDomain S R e x).1 ≤ ‖R‖*(G).budget k x.1 := by
  rw [Grading.budget,Grading.budget, ← tsum_mul_left]
  apply (rapid (onDomain S R e x).2 k).tsum_le_tsum _ ((rapid x.2 k).mul_left ‖R‖)
  intro n; unfold Grading.due; rw [band]; change weight k n*‖cell S n (R x.1)‖≤ _; rw [← show R (cell S n x.1)=cell S n (R x.1) from DFunLike.congr_fun (e n).eq x.1,mul_left_comm ‖R‖]; exact mul_le_mul_of_nonneg_left (R.le_opNorm _) (weight_pos k n).le
abbrev shift (p : E4) := onDomain S (U p) (translate_cell S p)
lemma covariance (f : Test4) (p : E4) (x : D) : shift S p (enact S B w f x)= enact S B w (ahead p f) (shift S p x):=by
  apply Subtype.ext
  change U p ((smearedBlocks S B f).reach x)=(smearedBlocks S B (ahead p f)).reach (shift S p x)
  unfold Blocks.reach; rw [(U p).map_tsum ((smearedBlocks S B f).series_usable (usableBlocks S B f w) x)]
  apply tsum_congr; rintro ⟨m,n⟩
  change U p (valise S (B.op m n) f x.1)= valise S (B.op m n) (ahead p f) (U p x.1)
  rw [← precursor]; change _ = U p (valise S (B.op m n) f (U (-p) (U p x.1))); rw [show U (-p) (U p x.1)=x.1 from DFunLike.congr_fun ((tgo S (-p) p).trans (by rw [neg_add_cancel,tini] : M S (-p+p)=1)) x.1]

lemma dissect_power (K : H.Op) : PowerPrice S ((G).dissect K) 0 ‖K‖ := by
  intro m n; simp only [Grading.weight,pow_zero,mul_one,Grading.dissect]
  refine (ContinuousLinearMap.opNorm_comp_le ..).trans ((mul_le_of_le_one_right (norm_nonneg _) ((G).norm_project_le n)).trans ?_); exact (ContinuousLinearMap.opNorm_comp_le ..).trans (mul_le_of_le_one_left (norm_nonneg _) ((G).norm_project_le m))
lemma dissect_paid (K : H.Op) : PowerPaid S ((bands S).dissect K):= ⟨0,‖K‖,norm_nonneg _,dissect_power S K⟩

abbrev warm (K : H.Op) := enact S ((G).dissect K) (dissect_paid S K)
lemma warm_actual (K : H.Op) (f : Test4) (x : D) : (warm S K f x).1= valise S K f x.1 :=
  (smearedBlocks S ((G).dissect K) f).reaches_whole _ (smear_bounded S K f) (usableBlocks S ((G).dissect K) f (dissect_paid S K)) x

lemma valise_approach {ι : Type*} (l : Filter ι) [l.IsCountablyGenerated] (A : ι→H.Op) (B : H.Op) (C : ℝ)
    (p : ∀ᶠ i in l, ‖A i‖ ≤ C)
    (t : ∀ x : H, Tendsto (fun i=> A i x) l (𝓝 (B x))) (f : Test4) (x : H) :
    Tendsto (fun i=> valise S (A i) f x) l (𝓝 (valise S B f x)) := by
  simp_rw [vmap]
  refine tendsto_integral_filter_of_dominated_convergence (fun u:E4=> ‖f u‖*(C*‖x‖))
    (Eventually.of_forall fun i => (emberI S x (A i) f).aestronglyMeasurable) (p.mono fun i h => Eventually.of_forall fun u=>?_)
    ((f.integrable (μ:=volume)).norm.mul_const (C*‖x‖)) (Eventually.of_forall fun u=>?_)
  · exact (spice S x (A i) f u).trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h (norm_nonneg _)) (norm_nonneg _))
  · exact (((U u).continuous.tendsto (B (U (-u) x))).comp (t _)).const_smul _

lemma enact_approach {ι : Type*} (l : Filter ι) [l.IsCountablyGenerated] (A : ι→(bands S).Blocks) (u : ∀ i, PowerPaid S (A i))
    {r : ℕ} {C : ℝ} (hC : 0≤C) (e : PowerPrice S B r C) (p : ∀ᶠ i in l, PowerPrice S (A i) r C)
    (t : ∀ m n (x : H), Tendsto (fun i=> (A i).op m n x) l (𝓝 (B.op m n x))) (f : Test4)
    {X : ι → D} {x : D} (s : (bands S).Approaches l X x) :
    (G).Approaches l (fun i=> enact S (A i) (u i) f (X i)) (enact S B w f x) := by
  refine (G).approaches_apply (fun i=> enact S (A i) (u i) f) (enact S B w f) (fun k=>?_ ) (fun z=>?_) s
  · exact ⟨_,_, p.mono fun i h y=> enact_tariff S (A i) (u i) h f y k⟩
  refine (smearedBlocks S B f).approaches (fun i=> smearedBlocks S (A i) f) (usableBlocks S B f w) (fun i=> usableBlocks S _ f (u i)) ?_ ?_ z
  · exact fun k=> ⟨_, _, meter_nonneg r k C f hC, path_tariff S B r k C f e, p.mono fun i h=> path_tariff S (A i) r k C f h⟩
  intro m n v; exact valise_approach S l (fun i=> (A i).op m n) (B.op m n) (C*Grading.weight r m*Grading.weight r n) (p.mono fun i h=> h m n) (t m n) f v
end YM.SatinRegistration
