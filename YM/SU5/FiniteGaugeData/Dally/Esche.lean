import YM.SU5.FiniteGaugeData.Dally.Korma
/-!
 # Ward cost **per tick**: one-integer-step slots and pure-label read
 -/
noncomputable section
open Metric Filter Function WithLp
open scoped Topology NNReal ENNReal InnerProductSpace
set_option autoImplicit false
namespace YM.CF.Buffered.Afterglow.Hierarchy.Seld.Poin.Galleon.Dai
open _root_.YM Dally Gem Leal Leal.Breve Celeritas Land Mist OS OS.Semigroup Flute Apso
variable {K : Axis → Hilbert} (W : ∀ i : Axis, OS.Semigroup (K i) i)
    {ι : Type} (G : Canopy (K timeAxis) ι) (ω : ∀ i, (K i).space) (A : Tribe G)
variable {n : ℕ} (u : Fin n → ι) (w : Palette G u)
variable (b : SpaceAxis) (x : Points n) (t s : ℝ)
local notation "ₜ" => timeAxis
local notation "☁" => Points n × Palette G u
attribute [local instance] ostensible
abbrev Sale (p : Points n × Palette G u) := ticket W G ω A timeAxis p.1 u p.2
local notation "ℑ" => Sale W G ω A u
def Leak (i : Fin n) (a : Axis) (t : ℝ) := x + t • agent i a
def sojourn (t : ℝ) := (wheelR b x t,vane G u w b t)
@[simp] lemma sojourn_root : sojourn G u w b x 0=(x,w) := by simp [sojourn]
@[simp] lemma Leak_root (i : Fin n) (a : Axis) : Leak x i a 0=x:=by simp [Leak]
lemma sojourn_der : HasDerivAt (sojourn G u w b x) (stride b x, plumeP G u w b) 0 :=
  (engineR b x).prodMk (engineD G u w b)

/- on analytic paint. meter defects at all-axis costable layouts only. -/
def shiver := fderiv ℝ (Sale W G ω A u) (x,w)
def chip : ℂ := shiver W G ω A u w x (stride b x, plumeP G u w b)
def blush (t : ℝ) : ℂ := (∑ i : Fin n,
  ((x i ₜ) • (ℑ (Leak x i b.castSucc t,w) - ℑ (x,w)) -
   (x i b.castSucc) • (ℑ (Leak x i timeAxis t,w) - ℑ (x,w)))) + (ℑ (x,vane G u w b t) - ℑ (x,w))
@[simp] lemma blush_root : blush W G ω A u w b x 0=0:=by simp [blush]
local notation "J" => shiver W G ω A u w x
lemma Nook : chip W G ω A u w b x =
    (∑ i : Fin n, ((x i ₜ) • ((J) (agent i b.castSucc,0)) -
      (x i b.castSucc) • ((J) (agent i timeAxis,0)))) + (J) (0,plumeP G u w b) := by
  let L := LinearMap.inl ℝ (Points n) (Palette G u)
  let F := (J).toLinearMap.comp L
  unfold chip
  rw [show (stride b x, plumeP G u w b) = ((stride b x,0):☁) + (0,plumeP G u w b) from by ext1 <;> simp,
    map_add,payout]; congr 1
  change F (∑ i, ((x i ₜ) • agent i b.castSucc - (x i b.castSucc) • agent i ₜ)) = _
  simp_rw [map_sum,map_sub,map_smul]; rfl

variable {U : Set (Shrine K)} (hp : ∀ b, b ≠ timeAxis → Philos (σ:=Fin n) W ω timeAxis b U)
    (hc : ∀ i, saucer (W i) (ω i)=ω i) (g : Stamp W G A U) (ha : longitude x)
include hp hc g ha
lemma shiver_der : HasFDerivAt ℑ (shiver W G ω A u w x) (x,w) :=
  (terra W G ω A timeAxis x u w hp hc g ha).differentiableAt.hasFDerivAt
lemma rollout : HasDerivAt (ℑ ∘ (sojourn G u w b x)) (chip W G ω A u w b x) 0 :=
  (shiver_der W G ω A u w x hp hc g ha).comp_hasDerivAt_of_eq 0 (sojourn_der G u w b x) (by simp)
lemma echoEv : HasDerivAt (blush W G ω A u w b x) (chip W G ω A u w b x) 0 := by
  have S := shiver_der W G ω A u w x hp hc g ha
  have H (i : Fin n) (a : Axis) : HasDerivAt
      (fun t => ℑ (Leak x i a t,w)-ℑ (x,w)) ((J) (agent i a,0)) 0 := by
    have η : HasDerivAt (Leak x i a) (agent i a) 0 := by
      simpa only [Leak,one_smul] using! (((hasDerivAt_id' (0:ℝ)).smul_const (agent i a)).const_add x)
    exact (S.comp_hasDerivAt_of_eq 0 (η.prodMk (hasDerivAt_const (0:ℝ) w)) (by simp)).sub_const _
  have η : HasDerivAt (fun t : ℝ => ℑ (x,vane G u w b t)-ℑ (x,w)) ((J) (0,plumeP G u w b)) 0 :=
    (S.comp_hasDerivAt_of_eq 0 ((hasDerivAt_const (0:ℝ) x).prodMk (engineD G u w b)) (by simp)).sub_const _
  rw [Nook]
  exact (HasDerivAt.fun_sum (A := fun (i : Fin n) (t : ℝ) =>
    ((x i ₜ) • (ℑ (Leak x i b.castSucc t,w) - ℑ (x,w)) -
     (x i b.castSucc) • (ℑ (Leak x i timeAxis t,w) - ℑ (x,w)))) fun i _ =>
      ((H i b.castSucc).const_smul (x i ₜ)).sub ((H i timeAxis).const_smul (x i b.castSucc))).add η
lemma chip_analytic : AnalyticAt ℝ (chip W G ω A u w b) x := by
  let φ (y : Points n) := (stride b y, plumeP G u w b)
  let F (y : Points n) := shiver W G ω A u w y
  have P : AnalyticAt ℝ F x := ((terra W G ω A timeAxis x u w hp hc g ha).fderiv).comp (f:=fun y : Points n => (y,w))
    (show AnalyticAt ℝ (fun y : Points n => (y,w)) x from analyticAt_id.prod analyticAt_const)
  have Q : AnalyticAt ℝ φ x := ((stride b).analyticAt x).prod analyticAt_const
  let L := ContinuousLinearMap.id ℝ ((Points n × Palette G u)→L[ℝ]ℂ)
  exact (L.analyticAt_bilinear _).comp (P.prod Q)

lemma knack {τ : ℕ → ℝ} (ht : ∀ᶠ i in atTop, 0 < τ i) (hy : Tendsto τ atTop (𝓝 0)) :
    (∀ ε : ℝ, 0 < ε → ∀ᶠ i in atTop, ‖blush W G ω A u w b x (τ i)‖ ≤ τ i * ε) ↔ chip W G ω A u w b x=0 := by
  let f := blush W G ω A u w b x; have f0:f 0=0:= blush_root ..
  let D := chip W G ω A u w b x
  let ℓ (i:ℕ) := (τ i)⁻¹ • f (τ i)
  have B' : Tendsto ℓ atTop (𝓝 D) := by
    convert (echoEv W G ω A u w b x hp hc g ha).tendsto_slope_zero_right.comp
      (show Tendsto τ atTop (𝓝[>] 0) from tendsto_nhdsWithin_iff.mpr ⟨hy,ht⟩) using 1
    ext1 i; simp [ℓ, f]
  have f' (i : ℕ) (h : 0 < τ i) (ε : ℝ) :
      ‖f (τ i)‖ ≤ τ i * ε ↔ dist (ℓ i) 0 ≤ ε := by
    rw [dist_zero_right, show ‖ℓ i‖= ‖f (τ i)‖/τ i by simp [ℓ, abs_of_pos h,div_eq_inv_mul], div_le_iff₀ h,mul_comm]
  constructor
  · intro U
    refine tendsto_nhds_unique B' (Metric.tendsto_nhds.mpr fun ε e=> ?_)
    filter_upwards [ht, U (ε/2) (half_pos e)] with i hi u; exact ((f' i hi _).1 u).trans_lt (half_lt_self e)
  intro z ε e; rw [show D=0 from z] at B'
  filter_upwards [ht, Metric.tendsto_nhds.mp B' ε e] with i hi l; exact (f' i hi ε).2 l.le
#print axioms knack
#print axioms chip_analytic
end YM.CF.Buffered.Afterglow.Hierarchy.Seld.Poin.Galleon.Dai
