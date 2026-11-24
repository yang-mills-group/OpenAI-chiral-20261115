import YM.SU5.Reconstruction.AllGrades.Shed
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option quotPrecheck false
noncomputable section
namespace YM.ConePrice.Session
open Function Set Filter MeasureTheory Spectral Analysis InnerProductSpace
open scoped Topology NNReal ENNReal ComplexOrder InnerProductSpace BigOperators
open YM.Multiplier Chirp CrossedFrame OS Semigroup Boundary Probe CF.Buffered.Afterglow.Tower MeshClock Germ SelectionAnalysis ConePrice Real Picket Roy
variable {H W:Hilbert} {a: Axis} {Γ: AddSubgroup ℝ} (K: OS.Semigroup H a)(T:Germ.Alliance (CF.Buffered.Afterglow.Tower.Trans a) Γ H)(S:OS.Semigroup W a)
local notation "U" j:max v:max=> (T.crew j).play v

local notation "S₀"=> Coupon a Γ
/-! # Native liquidity from inherited squared prices. -/
variable (i:CF.Buffered.Afterglow.Tower.Trans a) (x:H)
local notation "w"=>T.crew i
local notation "UP" v:max=> (T.crew i).play v x
local notation "kP" v:max => inner ℂ x (UP v)
local notation "A"=> ‖x‖^2
open scoped ComplexConjugate
variable (P:(Lore K T x)^2∈ Coupon.Population S Γ)(e0:Forward S)
private lemma conjugates (v:Γ) : (kP (-v))=conj (kP v):=by
 rw [(T.crew i).shift_g H (-v),neg_neg,inner_conj_symm]
-- estimate written with division for nonzero. Variance.
lemma corner (v:Γ)(h:0< ‖x‖): dist (UP (v+v)) x ≤ 2*Real.sqrt (‖x‖^2 - (((kP v)^2).re)/(‖x‖^2)) :=by
 let b:= kP v; let r(z:Γ):=kP z
 let c:= b.re/(A); let d:= A-(b^2).re/A
 have hm:0<A:= pow_pos h _; have hr:c*A=b.re:= div_mul_cancel₀ _ hm.ne'
 have ht:(b^2).re≤ b.re^2:=by rw [pow_two b, Complex.mul_re]; nlinarith [sq_nonneg b.im]
 have hb (v':Γ)(p: (r v').re = b.re):dist ((T.crew i).play v' x) ((c:ℂ) • x) ≤ Real.sqrt d:=by
    let y:=(T.crew i).play v' x; have he:‖y‖= ‖x‖:= (T.crew i).wins H v' x; rw [dist_comm,dist_eq_norm]; apply Real.le_sqrt_of_sq_le
    rw [norm_sub_sq (𝕜:=ℂ),inner_smul_left,norm_smul,Complex.norm_real,Real.norm_eq_abs]; change (|c| *‖x‖)^2- 2*(conj _ * r v').re+‖y‖^2 ≤ _; rw [he,Complex.conj_ofReal, Complex.re_ofReal_mul,p, mul_pow,sq_abs]; unfold d
    have h': (b^2).re/A ≤ c*b.re:=by apply (div_le_iff₀ hm).mpr; rw [mul_right_comm, hr, ← pow_two]; exact ht
    nlinarith [h',show c^2*A=(b.re)*c from (by rw [pow_two c, mul_assoc,hr,mul_comm])]
 have h₁:=hb v rfl; have h₂:=hb (-v) (by unfold r b; rw[conjugates]; exact Complex.conj_re _)
 have h3:dist (UP (v+v)) x=dist (UP v) (UP (-v)):=by rw [← (T.crew i).rigid H (-v), (T.crew i).paved]; rw [show -v+(v+v)=v by abel]
 rw [h3]; exact (dist_triangle _ ((c:ℂ) • x) _).trans (by linarith [dist_comm ((c:ℂ) • x) (UP (-v))])
variable (Z:∀ (v:Γ) (s:ℝ≥0), ((T.crew i).play v).comp (K.E s)=(K.E s).comp ((T.crew i).play v))
include P Z e0
-- full continuity on double.P for now (larger possible extra twist suppressed later).
theorem aunt_doubled : ContinuousAt (fun v:Γ => UP (v+v)) 0:=by
 rcases eq_or_ne x 0 with rfl|h
 · simp; exact continuousAt_const
 let z(v:Γ):= ((kP v)^2).re
 have he:= wet_progress K T S i x Z P e0; change Tendsto z (𝓝 (0:Γ)) (𝓝 (A^2)) at he
 unfold ContinuousAt; simp only [zero_add,(T.crew i).play_zero,ContinuousLinearMap.id_apply]; apply tendsto_iff_dist_tendsto_zero.mpr
 have h0:0< ‖x‖:= norm_pos_iff.mpr h; let d(v:Γ):= A-z v/A
 have hd:Tendsto d (𝓝 (0:Γ)) (𝓝 0):=by
    have he:= (tendsto_const_nhds (x:=A)).sub (he.div_const A); rw [show A-A^2/A=0 from (by rw [pow_two (A), mul_div_cancel_right₀ _ (by positivity), sub_self])] at he; exact he
 refine squeeze_zero (fun _=> dist_nonneg) (fun v=>corner T i x v h0) ?_; simpa [d,z] using ((Real.continuous_sqrt.continuousAt.tendsto.comp hd).const_mul 2)
end YM.ConePrice.Session
#print axioms YM.ConePrice.Session.aunt_doubled
