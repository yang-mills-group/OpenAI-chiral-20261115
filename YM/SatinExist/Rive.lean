import YM.SatinExist.EdgePrice
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv

/-! ## Read in any orientation. λ complex path from Euclidean to scaled real-time.
    Convergence concerns the **one-field vacuum** and its distributions only. -/

set_option autoImplicit false
set_option maxHeartbeats 260000
noncomputable section
namespace YM.SatinJets
open Function Filter Metric InnerProductSpace Set Complex MeasureTheory Measure
open Analysis Boundary Spectral OS.Semigroup LineDeriv
open scoped NNReal ENNReal Topology BigOperators InnerProductSpace ComplexOrder Classical
variable {H : Hilbert}{j:Axis} (S : OS.Semigroup H j) (n:ℕ)
local notation "R" => StampPower S
local notation "F_" => S.F

-- lane analyt F; continuous even to boundary (extend to all ℂ using clamp;
-- not asserting complex F itself there).
def oar(z:ℂ):H.Op := (S.edge (-z.im)).comp (S.E z.re.toNNReal)
variable (z:ℂ)
lemma oar_in (p:z∈inside): oar S z = S.F z:=by
 let r:= z.re.toNNReal; have h:0<z.re:=p; have ht:0<r:= Real.toNNReal_pos.mpr h
 unfold oar; rw [←S.roots_heat ht,S.along (dur.mpr ht)]; congr 1; apply Complex.ext <;> simp [sideways, duration]; try exact Real.coe_toNNReal z.re h.le
lemma oar_wash (x:H): Continuous (fun z:ℂ=> oar S z x):= S.cont_edge _ _ ((S.continuousE _).comp (continuous_real_toNNReal.comp continuous_re)) continuous_im.neg
lemma oar_cost (x:H): ‖oar S z x‖ ≤ ‖x‖:= by
 rw [oar, ContinuousLinearMap.comp_apply, S.life]
 exact ((S.E _).le_opNorm _).trans (mul_le_of_le_one_left (norm_nonneg _) (S.shrinks _))
lemma oar_thermal (a:ℝ): oar S ↑a=S.E a.toNNReal:=by simp [oar,S.birth]
lemma oar_side (t:ℝ): oar S (sideways t)= S.edge t := by simp [sideways,oar,S.eZero,Complex.mul_im]

-- time typed as σ*p[j] for branch on both test boxes
variable (σ:ℝ)
def waveR (S:OS.Semigroup H j)(σ:ℝ)(z:ℂ)(p:E4):H.Op:= (S.U (SEP j p)).comp (oar S (z*(↑(σ*p j):ℂ)))
noncomputable def fareR (f:Probe E4)(x:H)(z:ℂ):H:= ∫ p:E4,f p • waveR S σ z p x
lemma viewR (x:H) : Continuous (fun (v:ℂ × E4)=> waveR S σ v.1 v.2 x):=
 S.cont_cross _ _ ((oar_wash S x).comp (continuous_fst.mul (by fun_prop))) ((SEP j).continuous.comp continuous_snd)
variable (x:H)
lemma waveR_le (p:E4): ‖waveR S σ z p x‖ ≤ ‖x‖:= by rw [waveR, ContinuousLinearMap.comp_apply, S.unitary]; exact oar_cost ..

variable (f:Probe E4)
lemma fare_pay (p:E4): ‖f p • waveR S σ z p x‖ ≤ ‖f p‖*‖x‖:= by rw [norm_smul]; exact mul_le_mul_of_nonneg_left (waveR_le ..) (norm_nonneg _)
lemma fare_int : Integrable (fun p:E4=>f p • waveR S σ z p x):=by
 have he : Continuous (fun p:E4=>waveR S σ z p x):= (viewR S σ x).comp (by fun_prop : Continuous fun p:E4=>(z,p))
 exact (f.integrable.norm.mul_const ‖x‖).mono' (f.continuous.smul he|>.aestronglyMeasurable) (Eventually.of_forall (fun p=>fare_pay S z σ x f p))
lemma fare_plus (g:Probe E4):fareR S σ (f+g) x z=fareR S σ f x z +fareR S σ g x z:= by simp only [fareR,_root_.add_apply,add_smul]; rw [integral_add (fare_int ..) (fare_int ..)]
lemma fare_smul (c:ℂ):fareR S σ (c • f) x z= c • fareR S σ f x z := by simp only [fareR,_root_.smul_apply,smul_eq_mul,mul_smul,integral_smul]
lemma fareR_co : Continuous (fareR S σ f x):=by
 apply continuous_iff_continuousAt.mpr; intro z
 refine tendsto_integral_filter_of_dominated_convergence
    (fun p:E4=>‖f p‖*‖x‖) (Eventually.of_forall (fun i=>(fare_int S i σ x f).1)) (Eventually.of_forall fun i=> Eventually.of_forall (fare_pay S i σ x f)) (f.integrable.norm.mul_const _) (Eventually.of_forall fun p=> ?_)
 exact ((((viewR S σ x).comp (by fun_prop : Continuous (fun v:ℂ=>(v,p)))).tendsto z).const_smul (f p))

def RollCost (S:OS.Semigroup H j)(σ:ℝ)(z:ℂ)(f:Probe E4):H.Op:= LinearMap.mkContinuous (σ:=RingHom.id ℂ) {
   toFun x:= fareR S σ f x z
   map_add' x y:=by unfold fareR; simp only [map_add,smul_add]; rw [integral_add (fare_int ..) (fare_int ..)]
   map_smul' c x:=by unfold fareR; simp_rw [map_smul,smul_comm _ c,integral_smul]; rfl
 } (∫ p:E4,‖f p‖) (fun x=> show ‖fareR S σ f x z‖ ≤ _ from
      (norm_integral_le_integral_norm _).trans (by rw [← integral_mul_const]; exact integral_mono (fare_int .. |>.norm) (f.integrable.norm.mul_const _) (fare_pay S z σ x f)))

section turns
def pluck (j:Axis) := lineDerivOpCLM ℂ (Probe E4) (basis j)
lemma pluck_dl (p:E4): HasLineDerivAt ℝ f (pluck j f p) p (basis j):=(f.hasFDerivAt p).hasLineDerivAt _

variable {z σ}
lemma pulse_mark {y:H}(u:z∈inside)(t:∀ w:ℂ, w∈inside→ deriv S.F w x= S.F w x-S.F w y)(p:E4)(d:0<σ*p j): HasLineDerivAt ℝ (fun p:E4=> waveR S σ z p x) ((z*(σ:ℂ)) • waveR S σ z p (x-y)) p (basis j):=by
 let a:ℝ→E4:= fun i=> p+i • basis j; let K:= S.U (SEP j p); have he(i:ℝ): SEP j (a i) = SEP j p:=by
    unfold a; rw [map_add,map_smul,show SEP j (basis j)=0 from Subtype.ext (by simp [SEP]),smul_zero,add_zero]
 let A(i:ℝ):= z*(↑(σ*(a i j)):ℂ); have hb(i:ℝ): A i= z*(σ:ℂ)* (↑(p j):ℂ) + z*↑σ*(i:ℂ):=by
    unfold A a; push_cast; simp; ring
 let Z:=z* (↑(σ*p j):ℂ); have hP: A 0=Z:=by simp [A,a,Z]
 have v:Z∈ inside:=show 0< Z.re from (by unfold Z; rw [mul_re,ofReal_re,ofReal_im,mul_zero,sub_zero]; exact mul_pos u d)
 have hA: HasDerivAt A (z*(σ:ℂ)) 0:=by
    rw [funext hb]; simpa using! (((hasDerivAt_id' (0:ℝ)).ofReal_comp.const_mul (z*(σ:ℂ))).const_add (z*(σ:ℂ)*(↑(p j))))
 let f(w:ℂ):= K (S.F w x)
 have ht: HasDerivAt f (K (S.F Z (x-y))) (A 0):=by
    rw [map_sub (S.F Z), ← t Z v,hP]; exact K.hasFDerivAt.comp_hasDerivAt Z ((ContinuousLinearMap.apply ℂ H.space x).hasFDerivAt.comp_hasDerivAt Z ((S.localHeat Z v).differentiableAt.hasDerivAt))
 have hx: (fun i=> waveR S σ z (a i) x) =ᶠ[𝓝 0] (f ∘ A):= ((hA.continuousAt.tendsto).eventually (hP.symm ▸ open_inside.mem_nhds v)).mono fun i hi=> by
    dsimp only; unfold waveR; rw [he]; change K (oar S (A i) x)=_; rw [oar_in S (A i) hi]; rfl
 unfold HasLineDerivAt; rw [waveR]
 change HasDerivAt (fun i=> waveR S σ z (a i) x) ((z*(σ:ℂ)) • waveR S σ z p (x-y)) 0
 refine ((ht.hasFDerivAt.restrictScalars ℝ).comp_hasDerivAt 0 hA).congr_of_eventuallyEq hx |>.congr_deriv ?_
 unfold waveR; rw [oar_in S Z v]; simp; rfl -- inspect

variable (σ z)
private lemma wave_inv (y:H)(u:z∈inside)(t:∀ w:ℂ, w∈inside→ deriv S.F w x= S.F w x-S.F w y) (hp:∀ p:E4,p∈tsupport f→ 0<σ*p j):
   (z*(σ:ℂ)) • fareR S σ f y z=(z*(σ:ℂ)) • fareR S σ f x z + fareR S σ (pluck j f) x z:=by
 let c:=z*(σ:ℂ)
 let g(p:E4):=c • waveR S σ z p (x-y); let a:=fare_int S z σ x f; let b:=fare_int S z σ y f; let h:= fare_int S z σ x (pluck j f)
 let A(p:E4):= f p • waveR S σ z p x; let B(p:E4):= f p • waveR S σ z p y
 have Hx(p:E4): f p • g p = c • (A p-B p):=by unfold g A B; rw [← smul_sub, map_sub, smul_comm]
 have Hx': Integrable (fun p:E4=> f p • g p):=by simp_rw [Hx]; exact (a.sub b).smul c
 have he:(∫ p:E4,f p • g p)=- fareR S σ (pluck j f) x z:= integral_bilinear_hasLineDerivAt_right_eq_neg_left_of_integrable (B:=ContinuousLinearMap.lsmul ℝ ℂ) h Hx' a (fun p _=> pluck_dl f p) (fun p v=>pulse_mark S x u t _ (hp p v))
 let K(v:H):=fareR S σ f v z; let Z:= fareR S σ (pluck j f) x z
 simp_rw [Hx,integral_smul] at he; rw [integral_sub (f:=A) (g:=B) (μ:=volume) (show Integrable A volume from a) (show Integrable B volume from b) ,smul_sub] at he; change c • K x-c • K y= - Z at he; change c • K y=_; have ht: c • K y - c • K x= Z:= by rw [← neg_sub,he, neg_neg]
 rw [sub_eq_iff_eq_add'] at ht; exact ht

/-- Recursively promote derivative estimates for the same test, no Fourier phases needed at the edge.
 Even on all of ℂ define by continuous extension (clamping); identity only on Re z ≥ 0. -/
def dupes (j:Axis)(z σ:ℂ)(n:ℕ): Probe E4 → Probe E4:= match n with
 | 0=>id
 | n+1=>fun f=> (z*σ) • dupes j z σ n f + pluck j (dupes j z σ n f)
private lemma scales_foot (n:ℕ): tsupport (dupes j z σ n f) ⊆ tsupport f :=by
 induction n with
 | zero=> exact Subset.rfl
 | succ n ih=>
   let g:= dupes j z σ n f; let a:= z*(σ:ℂ)
   rw [dupes]; refine (tsupport_add (fun p:E4=>a • g p) (pluck j g : E4 → ℂ)).trans ?_; exact union_subset ((tsupport_smul_subset_right ..).trans ih) ((SchwartzMap.tsupport_lineDerivOp_subset ..).trans ih)

lemma pulse_pad (u:z∈inside)(hp:∀ p:E4,p∈tsupport f→ 0<σ*p j):
    ((z*(σ:ℂ))^(n+1)) • fareR S σ f x z = fareR S σ (dupes j z σ (n+1) f) (R n x) z:=by
 let c:=z*(σ:ℂ)
 induction n with
 | zero=>
   rw [dupes, dupes,fare_plus,fare_smul]; rw [Nat.zero_add,pow_one]; exact wave_inv S z σ (R 0 x) f x u (interest_base S x) hp
 | succ n ih=>
   let f':= dupes j z σ (n+1) f; rw [pow_succ', mul_smul,ih]; change c • fareR S σ f' (R n x) z = _; rw [dupes, fare_plus,fare_smul]; exact wave_inv S z σ (R (n+1) x) f' (R n x) u (interest_higher S n x) (fun p v=> hp _ (scales_foot z σ f _ v))

end turns
end YM.SatinJets
