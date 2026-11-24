import YM.SU5.Obstruction.Conditional
/-!
# The flat-link aperture tester is INVERTIBLE after one genuine lift

In the existing local resolution system, with actual one-step calculus. New way to
get product retest gaps on precisely (an) interacting stencil. Use `Noise`, `Finite`
and `Conditional` of a quite different obstruction in the imports: the proof and code below
are adapted from there and `p:pair`, `t:no` strategy in the task references.
-/
set_option autoImplicit false
set_option maxHeartbeats 350000
set_option maxRecDepth 6000
set_option synthInstance.maxSize 24000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.SatinRotation

open Function Filter NormedSpace SU Lat Lattice Cube Finset MeasureTheory RG Wilson Metric
open Buffered
open Buffered.Afterglow Tapestry
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Kronecker Topology ComplexOrder ENNReal Classical
open Rush Scroll Peaks Stencil Tenant Tap Tulip Branch Fir Scree Buffered.Advance Reflect Window Laurent Next.Free Bloch Drapes Spire Lifted Skye Sound Precision Tree Push.SectorMeasure Next.SectorChange Common Fock
open Satin
attribute [local instance] opCStarAlgebra
namespace Clean
variable (ε:ℝ)(p:Lattice.Face ℤ)
local notation "S" => faceSites p

def clear (v : SU.E) := max 0 (ε-SU.group.chord v)
lemma clear_cont : Continuous (clear ε):= continuous_const.max (continuous_const.sub SU.group.continuous_chord)
lemma clear_nonneg (v:SU.E) : 0 ≤ clear ε v:= le_max_left ..
lemma closes (v:SU.E)(h:ε ≤ SU.group.chord v): clear ε v=0 := max_eq_left (sub_nonpos.mpr h)
lemma clear_mass (h:0<ε) : 0< ∫ x:SU.E, clear ε x∂SU.group.probHaar := by
  apply (integral_pos_iff_support_of_nonneg (μ:=SU.group.probHaar) (clear_nonneg ε)
    ((clear_cont ε).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))).2
  exact (clear_cont ε).isOpen_support.measure_pos _ ⟨1, by change clear ε 1≠0; unfold clear; rw [Gauge.chord_one,sub_zero,max_eq_right h.le]; exact h.ne'⟩

variable (K:Calibration) (N:Side)
def yPane (v: Pane N):= clear ε (faceValue v (wrapFace p N))
def yCover (v:LinksC):= clear ε (faceValue v p)
lemma yCover_cont : Continuous (yCover ε p):= (clear_cont ε).comp (show Continuous fun v:LinksC=> faceValue v p from continuous_travel ..)
lemma yPane_env : Envelope (yPane ε p N) := Env.compact ((clear_cont ε).comp (show Continuous fun v:Pane N=>faceValue v (wrapFace p N) from continuous_travel ..))
lemma cover_locus : LocalOn S (yCover ε p):= fun v w h=> congrArg (clear ε) (travel_local p.1 (Lattice.square p.2.val.1 p.2.val.2) v w
  (fun i t s=>h i (List.mem_toFinset.mpr t) (List.mem_toFinset.mpr s)))
lemma wrapped (v:Pane N): yCover ε p (onC N v)= yPane ε p N v:= by
  unfold yCover yPane wrapFace faceValue onC; simp only [travel_at,add_zero]

def apertureMark: Buffered.Family K:= Buffered.scalar K fun x=> (yCover ε p x.1:ℂ)
lemma recognized (w:Bool): InTest K w S false (apertureMark ε p K):=
  .seed (Coeff.fromC w _ (Complex.continuous_ofReal.comp (yCover_cont ε p)) fun x y h=> congrArg Complex.ofReal (cover_locus ε p x y h))
lemma apertureMark_price (m:Side): apertureMark ε p K m= scalarMark (fun u=> (yPane ε p (K.c m) u:ℂ)):=by
  funext x; unfold apertureMark Buffered.scalar scalarMark; simp only [wrapped]
lemma aperture_gauge : Neutral K (apertureMark ε p K):= by
  intro m; rw [apertureMark_price]; intro g t
  simp only [scalarMark, simultaneous, Prod.map,yPane, clear, face_gauge,Gauge.chord_conj, twist_scalar,map_one]

open Py Py.Rate LocalLimit Preparation Journey Vale FullBill
variable {Λ : Preparation} {l : ℕ} (Y : Course Λ (VolumeCape.Dream.Nimbus l))
  (H : Real.exp 1 ≤ Λ.x)
  {a b : ℕ → ℕ} {I : ℕ → Buffered.Family (tent Y H) → ℕ → ℂ}
  {E : ℕ → Buffered.Family (tent Y H) → ℂ}
  {L : Rack Λ l} {B : Clay Λ l} (D : Exhibition Y H a b I E L B)
  (n : ℕ)
local notation "K·" => tent Y H
local notation "i₀" t:max => a (WedgeStage.vol t)
local notation "k₀" t:max => b (WedgeStage.uv t)
local notation "T" => followBox (Λ:=Λ) (l:=l) (faceSites p)

def detector (K:Calibration):Dome K:= ⟨apertureMark ε p K,broadCompile K _ (recognized ε p K true)⟩
lemma det_bay (w:Bool): detector ε p K∈ bay K S w:= recognized ε p K w
lemma det_enclave : detector ε p K∈ enclave K:= aperture_gauge ε p K
def chartIn:= trophy K (detector ε p K) (det_bay ε p K true)
lemma det_badge : badge K S (chartIn ε p K)= detector ε p K:= trophy_at ..
local notation "F"=> detector ε p (K·)
local notation "U" => D.liftD Y H n (detector ε p (K·))
local notation "f·" => chartIn ε p (K·)
def step (i k:ℕ):= advanceCoeff Y n i k (yPane ε p (side Y i n))
def height (B:Clay Λ l) := B S n f·
local notation "ρ" => height ε p Y H n B -- order check
lemma on_chart : D.liftD Y H n (detector ε p (K·)) = badge (K·) T (height ε p Y H n B):= by
  rw [←det_badge]; exact D.fromLocal Y H n _ _
lemma on_sized (i:ℕ): exhibit Y H n i (apertureMark ε p (K·))=scalarMark (fun v=> (yPane ε p (side Y i n) v:ℂ)):= by
  change arrange _ _ _ (apertureMark ε p (K·) _)=_
  rw [apertureMark_price]; exact carry _
where
  carry {m n:Side}(h:m=n): arrange m n h
      (scalarMark (fun v => (yPane ε p m v : ℂ))) =
      scalarMark (fun v => (yPane ε p n v : ℂ)) := by subst n; rfl
local notation "A" i:max k:max=> patternA Y n i k
lemma on_gate (i k:ℕ)(p₀:PairIdx Y n i k) : ascender Y n i k (exhibit Y H n i (apertureMark ε p (K·)))= scalarMark (fun x=>(step ε p Y n i k x:ℂ)):=by
 rw [on_sized]; exact ascend_real Y n i k p₀ (yPane_env ..)
include D
lemma true_price : RealFirst T (height ε p Y H n B) ∧
      ∀ x : LinksC, Tendsto (fun t : WedgeStage => step ε p Y n (i₀ t) (k₀ t) (graft T _ x))
        followStage (𝓝 (scalarPart T ρ x)) := by
  apply scalar_limit T Y H (D.buoy Y H (faceSites p) n (f·)) (n:=n+1) (r:=fun t => i₀ t) (g:=fun t => step ε p Y n (i₀ t) (k₀ t))
  have h : render (faceSites p) (K·) (f·) = apertureMark ε p (K·) := congrArg Subtype.val (det_badge ε p (K·))
  filter_upwards [D.uniformRoad Y H S n] with t ht
  refine ⟨Roomy.seats ht.2.2,?_⟩
  rw [onSpanned _ _ _ _ _ _ ht,present_exhibit,h]; exact on_gate ε p Y H n _ _ ht.1

omit D in
def value (Λ : Preparation)(s:ℕ):=noiseFloor (Course.ceiling Λ s) Λ.K.bind.penalty * (∫ u : SU.E, clear ε u∂SU.group.probHaar)
omit D in
lemma floor_bound (i k:ℕ)(h : PairIdx Y n i k)(hp : Hosp (faceSites p) (side Y i n))
    (V : Pane (side Y i (n+1))) : value ε Λ n ≤ step ε p Y n i k V:= by
  unfold value; rw [← show (patternA Y n i k).kernel = Λ.K.bind from (Y.pilot_steps n i k).2.1]
  exact density_estimate_face (A i k) (wrapFace p (side Y i n)) (wrapFace_admits p (side Y i n) hp)
    (show |patternβ Y n i k| ≤ Course.ceiling Λ n from abs_le.mpr (Y.seated n i k h.2))
    (patternBranches ..) V (clear_cont ε) (clear_nonneg ε)
lemma ascent (x:LinksC): value ε Λ n ≤ scalarPart T (height ε p Y H n B) x:=by
  apply ge_of_tendsto ((true_price ε p Y H D n).2 x)
  filter_upwards [D.uniformRoad Y H (faceSites p) n, D.uniformRoom Y H (faceSites p) n] with t ht hr
  exact floor_bound ε p Y n _ _ ht.1 (Roomy.seats hr) _

omit D
variable (w:0<ε)
include w in
lemma pos_value : 0 < value ε Λ n:= mul_pos (noiseFloor_pos _ _) (clear_mass ε w)

abbrev reciprocal (B:Clay Λ l) (x:LinksC):=(scalarPart T (height ε p Y H n B) x)⁻¹
local notation "ψ" => reciprocal ε p Y H n B
include D w
lemma money (x:LinksC): ‖ψ x‖ ≤ (value ε Λ n)⁻¹:= by
  have t:= ascent ε p Y H D n x; have hp:= pos_value (Λ:=Λ) ε n w
  rw [Real.norm_of_nonneg (inv_pos.mpr (hp.trans_le t)).le]; exact inv_anti₀ hp t
lemma recip_env : Envelope (reciprocal ε p Y H n B):=
  ⟨(scalarPart_env T ρ).meas.inv, _,money ε p Y H D n w⟩
lemma recip_test : InTest (K·) true T false (Buffered.scalar (K·) fun x=> (ψ x.1:ℂ)):=
   .seed ⟨fun _ => by contradiction, Env.along (envelope_ofReal (recip_env ε p Y H D n w)) measurable_fst,
    fun x y h _ => congrArg Complex.ofReal (congrArg Inv.inv (scalarPart_locus T ρ x.1 y.1 h))⟩
def undoLift (w:0<ε) (D' : Exhibition Y H a b I E L B): Dome (tent Y H):=
  ⟨Buffered.scalar (K·) (fun x=>(ψ x.1:ℂ)),broadCompile (K·) T (recip_test ε p Y H D' n w)⟩
local notation "Vw"=> undoLift ε p Y H n w D
lemma undo_bay : undoLift ε p Y H n w D ∈ bay (K·) T true := recip_test ε p Y H D n w
lemma undo : U * (undoLift ε p Y H n w D) = 1:= by
  apply Subtype.ext
  change (U).val * Buffered.scalar (K·) (fun x=>(ψ x.1:ℂ))=1
  rw [on_chart,domTag,render_real (K·) T (true_price ε p Y H D n).1]
  funext m x; simp only [scalar,reciprocal,Pi.mul_apply, Algebra.smul_mul_assoc,one_mul,smul_smul, ← Complex.ofReal_mul,Pi.one_apply]
  rw [mul_inv_cancel₀ ((pos_value (Λ:=Λ) ε n w).trans_le (ascent ε p Y H D n _)).ne',Complex.ofReal_one,one_smul]
lemma undo_neutral : undoLift ε p Y H n w D∈ enclave (K·):=by
  apply (colorFixed (K·)).mpr
  intro R
  let u := pennant (K·) R
  have ht : U * Vw = 1 := undo ε p Y H D n w
  have hk : u U = U := (colorFixed (K·)).mp (D.riseGauge Y H n (det_enclave ε p (K·))) R
  have hp : U * u Vw = 1 := calc
    _ = u U * u Vw := by rw [hk]
    _ = _ := by rw [← map_mul, ht, map_one]
  change u (Vw)= _
  calc
    _ = (Vw * U) * u Vw := by rw [mul_comm (Vw),ht,one_mul]
    _ = _ := by rw [mul_assoc,hp,mul_one]
end Clean
end YM.CF.SatinRotation

#print axioms YM.CF.SatinRotation.Clean.undo
#print axioms YM.CF.SatinRotation.Clean.undo_neutral
