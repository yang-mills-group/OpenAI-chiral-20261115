import YM.SU5.Reconstruction.Quartz.Zenith
set_option autoImplicit false
noncomputable section
namespace YM.Quartz.Waltz
open Function Filter Set MeasureTheory Measure Metric Topology
open scoped Topology NNReal ENNReal Complex InnerProductSpace Interval ComplexOrder
open CrossedFrame Clasp Picket Lens Ravin BridgeClub Anvil ConePrice Sail
lemma vat_limited (b C:ℝ)(v:Ba){f:ℕ→ Du→ℂ}{g:Du→ℂ}(p:0<b) (h:∀i,Continuous (f i))(y:∀i t,‖f i t‖≤ C)(q:∀ x,Tendsto (fun n=> f n x) atTop (𝓝 (g x))) : Tendsto (fun i=> vat b v (f i)) atTop (𝓝 (vat b v g)):= by
 refine tendsto_integral_of_dominated_convergence (F:=fun i x=>Blaze b (Largo x-v)* f i x) (fun x=> wallRate b (x-Forge v)*(Real.exp (b*pressure (Eddy v))*C)) (fun i=> (Continuous.mul (show Continuous (fun x=> Blaze b (Largo x-v)) from (by unfold Blaze Largo; fun_prop)) (h i)).aestronglyMeasurable) ((pond b _ p).mul_const _) (fun i=> ae_of_all _ (fun t=>?_)) (ae_of_all _ (fun x=>?_))
 · rw [norm_mul,← mul_assoc, ← toll p]; gcongr; exact y i t
 exact Tendsto.const_mul (Blaze b (Largo x-v)) (q x)
variable {a b:Axis}(p:b≠a) {H E K:Hilbert}(S:OS.Semigroup H a)(C:Clasp K H E)(B W:H.Op)(γ s:ℝ)
local notation "Q"=>path a b
noncomputable def afterP (x y:H) (A:H.Op) (r:Du):ℂ:= inner ℂ x ((A*rateTime (b:=b) S B r) y)
noncomputable def beforeP (x y:H) (A:H.Op) (r:Du):ℂ:= inner ℂ x ((rateTime (b:=b) S B r*A) y)
variable (x y:H)
local notation "XP"=> afterP (b:=b) S B x y
local notation "YP"=> beforeP (b:=b) S B x y
noncomputable def DivYield (d:ℝ≥0)(Z:ℂ→ H.Op)(j:ℝ)(z:ℂ):ℂ:= vat j (crossprice d z) (afterP (b:=b) S B x y (Z z)) - vat j (Largo 0) (beforeP (b:=b) S B x y (Z z))
lemma afterCont (A:H.Op): Continuous (afterP (b:=b) S B x y A):= continuous_const.inner (A.continuous.comp (rateAccess (b:=b) S B _ continuous_const id continuous_id))
lemma beforeCont(A:H.Op): Continuous (beforeP (b:=b) S B x y A):= continuous_const.inner (rateAccess (b:=b) S B _ continuous_const id continuous_id)
noncomputable def blue (F:ℝ):=‖x‖*(F*‖B‖*‖y‖)
lemma blue_back{t:ℝ}(p:0≤t):0 ≤ blue B x y t:=by unfold blue; positivity
lemma blueL(A:H.Op){c:ℝ} (p:‖A‖≤c) (t:Du):‖XP A t‖≤ blue B x y c:= norm_toll x y _ ((norm_mul_le ..).trans (mul_le_mul p (parcel_charge S _ _) (norm_nonneg _) ((norm_nonneg _).trans p))) -- tune clock implicit
lemma blueR(A:H.Op){c:ℝ}(p:‖A‖≤c)(t:Du):‖YP A t‖≤ blue B x y c:= norm_toll x y _ ((norm_mul_le ..).trans (((mul_le_mul (parcel_charge S _ _) p (norm_nonneg _) (norm_nonneg B))).trans_eq (mul_comm ..)))
variable (L:∀ v:E4, boost C (-s) * trans S v= trans S (Picket.move a b (-s) v)* boost C (-s))
variable {M:Set H.Op} (d c:ℝ≥0)
structure Voices (W:H.Op) (d c:ℝ≥0) : Prop where
 wants : ∃ i:ℕ→ H.Op,(∀n,Script S M (i n) d c) ∧ Limited atTop i W
local notation "W'" A:max=> ascend (-s) C A
local notation "c₀"=> (blue B x y c)
variable (v: Worth (b:=b) S C B (scud (d:ℝ) γ) M)(w : Voices S (M:=M) W d c)
include L p v w
lemma inCap (p0:|s|≤3)(u:ℝ)(hu:0<u):
    ‖vat u (crossprice d ((s:ℂ)+(κ:ℂ)*Complex.I)) (XP (ascend (-s) C W))-vat u (Largo 0) (YP (W' W))‖ ≤ capital c₀ d γ * surge u γ:= by
 obtain ⟨f,q,r⟩:= w.wants; have hc(i:ℕ): ‖W' (f i)‖≤(c:ℝ):=(budgeted C (f i) (-s)).trans (q i).pays; let F(i:ℕ):= W' (f i)
 rw[lunar (d:ℝ), show Largo 0 = petal s 0 from ((by rw [petal_zero]; rfl ))]; have hk: Limited atTop F (W' W) := (r.toLeft (Pearl.still atTop (boost C (-s)))).toRight (Pearl.still atTop (star (boost C (-s)))) -- tune
 let Aₗ:= (rateTime (b:=b) S B)
 apply le_of_tendsto' (((vat_limited u c₀ (petal s (d:ℝ)) hu (fun i=>afterCont (b:=b) S B x y (F i)) (fun i=> blueL S B x y (F i) (hc i)) (fun v=> (hk.toRight (Pearl.still _ (Aₗ v))).confirms x y)).sub (vat_limited u c₀ (petal s 0) hu (fun i=>beforeCont (b:=b) S B x y (F i)) (fun i=> blueR S B x y (F i) (hc i)) (fun v=> (hk.toLeft (Pearl.still _ (Aₗ v))).confirms x y))).norm) -- tune comp l :=atTop
 intro i; refine Waltz.floats u s (d:ℝ) γ c₀ hu d.property p0 (blue_back B x y (c.property)) (afterCont ..|>.aestronglyMeasurable) (beforeCont ..|>.aestronglyMeasurable) (blueL S B x y (F i) (hc i)) (blueR S B x y (F i) (hc i)) (fun t T=> ?_)
 exact concordance p S C B (f i) (scud (d:ℝ) γ) s (scud_favorable ..|>.le) v d c (q i) x y L t p0 T
end YM.Quartz.Waltz
