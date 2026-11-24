import YM.SU5.Reconstruction.Quanta.Perseus
import YM.CF.Buffered.Microscopic
import YM.CF.Buffered.Transfer

/-! # Authentic plane/physics on both grades -/
set_option autoImplicit false
set_option synthInstance.maxSize 24000
set_option maxHeartbeats 700000
noncomputable section
namespace YM.CF.Buffered.Heat
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Topology Kronecker ComplexOrder
open Function Fock Filter NormedSpace SU Lat Lattice Branch Cube Tenant Phase Mir Mir.Trip MeasureTheory Finset Reflect
open RP Spark RG WilsonStartup Vale Scroll Spire Nova Push.SectorMeasure Nacre Window Tulip Skye Brace
attribute [local instance] opCStarAlgebra

variable {m B n : Side} {c : Phase.Part m B} {e d a₁ a₂ : ℝ}
local notation "X" => Pack m B
local notation "I" => Xmind m B
local notation "A" => FC (Xmind m B)
local notation "N" => CSide m B
local notation "Wμ" => wheel m B
local notation "β₀" => Brace.northZ m B

variable (i : Axis) (z : ℤ)

variable {g₀ : Bool}
lemma liftShift_sector (B : Side) (f : Evaluation n) (w : ℕ)
    (h : ∀ x,Sector (modesIn n (Buffered.band n i (gaugeShift B z) w)) g₀ (f x)) :
    ∀ x, Sector (modesIn n (Buffered.band n i 0 w)) g₀ (liftShift i B z f x) := by
  intro x; apply north_sector _ _ _ (h _); apply prep_moves; intro x
  rw [show (gaugeShift B z)=2*(2*(↑B.val:ℤ)*z) from by unfold gaugeShift; ring]; simpa only [coverShift,zero_add] using (band_shift i 0 n (2*(↑B.val:ℤ)*z) w x)
variable (p : Pinning m B) (W : Scroll m B c) (clip : Clip) (β t u : ℝ)

lemma priced_north (f : Evaluation N) (h : Envelope f) (w : LocalOn (Buffered.band N i (gaugeShift B z) 0 : Set _) f)
    (u : ∀ x, Sector (modesIn N (Buffered.band N i (gaugeShift B z) 0)) g₀ (f x)) : PolePiece g₀ i (rephased i z f) := by
  refine ⟨Girt.pole_w _ (toSeam m B i) ((breeze _).comp (cxC _)) (Env.along (liftShift_env i z B f h) measurable_fst),
    fun x=> toSeam_forward i (north_modes_eq i ▸ liftShift_sector i z B f 0 u x.1) rfl,?_⟩
  intro x y k; unfold rephased; apply congrArg; apply liftShift_local _ z B f 0 w; rw [band_zero]; exact k.gaugeS
lemma passed_pair (f g : Evaluation N) (h : ∀ x,Sector (modesIn N (Buffered.band N i (gaugeShift B z) 0)) g₀ (f x)) :
    rephased i z (chord g₀ • (Buffered.refl i (gaugeShift B z) f * g))=dialProduct g₀ i (rephased i z f) (rephased i z g) := by
  funext x; change toSeam _ _ i (liftShift i B z (chord g₀ • (Buffered.refl i (gaugeShift B z) f * g)) x.1)= chord g₀ • testProduct _ _ _ x; have hu(A': Evaluation (CSide m B)): liftShift i B z (chord g₀ • A')= chord g₀ • liftShift i B z A':=funext fun _=> twist_scalar ..
  rw [hu, Pi.smul_apply,toSeam_scalar]; apply congrArg (chord g₀ • ·); unfold rephased testProduct; rw [liftShift_prod,Pi.mul_apply,toSeam_prod,liftShift_refl _ z B f _ _ h]
  unfold Buffered.refl; rw [carR_zero,fling_zero, toSeam_turn i (north_modes_eq i ▸ liftShift_sector i z B f 0 h _)]
  rfl
section plt
variable (b : Budget B e d) (H : ScaleK a₁ a₂ W)
include H b
local notation "S" => Buffered.band N i (gaugeShift B z) 0
-- whole translated statement, pinning as in Manuscript
lemma pole_displaced_limit (hu : 0 ≤ u) (f g : Evaluation N) (hf : Envelope f) (hg : Envelope g)
    (wf : LocalOn (S:Set _) f) (wg : LocalOn (S:Set _) g)
    (p' : ∀ x,Sector (modesIn N S) g₀ (f x)) (q' : ∀ x,Sector (modesIn N S) g₀ (g x)) :
    let T := fun n => transfer p W clip β t u e i β₀ n
    Tendsto (fun n=>kernelTrace (n+1) (T n (rephased i z g)) (kernelStar (n+1) (T n (rephased i z f)))) atTop
      (𝓝 (heatNum p W clip β t e u β₀ (insertTop (chord g₀ • (Buffered.refl i (gaugeShift B z) f * g))))) := by
  intro T; rw [rephased_eq i z p W, passed_pair _ z _ _ p']
  exact from_poles p W clip β t u b H i _ hu _ _ (priced_north i z f hf wf p') (priced_north i z g hg wg q')

theorem pole_top_nonnegative (hu : 0 ≤ u) (f : Evaluation N) (h : Envelope f) (w : LocalOn (S:Set _) f)
    (w₀ : ∀ x,Sector (modesIn N S) g₀ (f x)) :
    0 ≤ heatNum p W clip β t e u β₀ (insertTop (chord g₀ • (Buffered.refl i (gaugeShift B z) f * f))) := by
  rw [rephased_eq i z p W,passed_pair _ z f f w₀]
  exact pole_positive p W clip β t _ b H i β₀ hu _ (priced_north i z f h w w₀)
end plt
end YM.CF.Buffered.Heat

/-! # The numerator in `summit_num`, with actual heat transfers. -/
set_option autoImplicit false
set_option synthInstance.maxSize 16000
noncomputable section
namespace YM.CF.Buffered.Heat
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset Cube SU Fock Lat Spire Scroll MeasureTheory Mesa ProbabilityTheory Peaks Drapes Rush Precision Tree Push.SectorMeasure Next.SectorChange Tulip Jet Tap Laic Dial Paige Vault Pec Skye Pastry Cascade Phase Brace Scree RG Spark RP Gloss Branch Reflect Window
open Reed (Fine think)
open scoped Topology BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Matrix.Norms.L2Operator ComplexOrder
attribute [local instance] opCStarAlgebra
variable {m B L : Side} {j : ℕ} {ho : Odd L.val} {Y : Pricing j L ho (Thread j)}{e : ℝ}
variable (P : Grasp Y B e) (X : GramM (CSide m B)) (R : Loom (CSide m B)) (p : Pinning m B)
   (W : Scroll m B (Brace.northZ m B)) (clip : Clip) (u : ℝ)
local notation "c₀" => CSide m B
local notation "f₀" => Brace.northZ m B
variable (eyes : Eyes P X R p W clip u) {a D b : ℝ} (k : ScaleK a D W) (v : Budget B e b) {d' b' : ℝ} {n : ℕ} (T : Roof (CSide m B) b' d' n R) (h : X.p.threshold ≤ b') (U : Rue.IsleB SU.group X.p.threshold)
variable {g₀ : Bool}
lemma both_pole (f : Mark (CSide m B)) {i : Axis} {s : ℤ} (h : AtSupport g₀ (Buffered.band (CSide m B) i s 0) f) :
    Envelope (both f) ∧ LocalOn (Buffered.band c₀ i s 0) (both f) ∧ ∀ x, Sector (modesIn c₀ (Buffered.band c₀ i s 0)) g₀ (both f x) := ⟨Env.along h.env (measurable_id.prodMk measurable_id), fun x y v=> h.dep _ _ v v, fun x=> (h.allV (x,x)).sector⟩
include eyes k v T h U
variable (i : Axis) (s : ℤ) (f g : Mark (CSide m B))
local notation "μ" => gaugeShift B s
local notation "E" => Buffered.band c₀ i (gaugeShift B s) 0
-- trace limit on exactly the top mark obtained, reflection simultaneously peeled
lemma strata_trace (a : AtSupport g₀ E f) (b : AtSupport g₀ E g) (hu : 0≤u) :
    let l := fun n => transfer p W clip X.beta X.p.threshold u e i f₀ n
    Tendsto (fun n => kernelTrace (n+1) (l n (rephased i s (both g))) (kernelStar (n+1) (l n (rephased i s (both f))))) atTop
      (𝓝 (markedRead (chord g₀ • (reflMark i μ f * g)) R (denZ X P R))) := by
  intro l; rw [summit_num P X R p W clip u eyes k v T h U]; swap; · exact ((((a.refl i μ).mono (subset_univ _)).mulM (b.mono (subset_univ _))).smulM _).env
  obtain ⟨p0,p1,p2⟩:= both_pole f a; obtain ⟨q0,q1,q2⟩:= both_pole g b
  exact pole_displaced_limit i s p W clip X.beta X.p.threshold u v k hu (both f) (both g) p0 q0 p1 q1 p2 q2
lemma strata_gram (x : AtSupport g₀ E f) (hu : 0 ≤ u) : 0 ≤ markedRead (chord g₀ • (reflMark i μ f*f)) R (denZ X P R) := by
  rw [summit_num P X R p W clip u eyes k v T h U]; swap; · exact ((((x.refl i μ).mono (subset_univ _)).mulM (x.mono (subset_univ _))).smulM _).env
  obtain ⟨p0,p1,p2⟩:= both_pole f x; exact pole_top_nonnegative i s p W clip X.beta X.p.threshold u v k hu (both f) p0 p1 p2
end YM.CF.Buffered.Heat

#print axioms YM.CF.Buffered.Heat.strata_gram
