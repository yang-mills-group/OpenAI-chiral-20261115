import YM.SU5.FiniteGaugeData.Signal.Aquarius
import YM.SU5.FiniteGaugeData.Reliance.Expenditure
/-! # Leftover of the shutter on a high-floor mask -/
set_option autoImplicit false
set_option linter.flexible false
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 24000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Signal
open Function Filter NormedSpace MeasureTheory Finset Lattice RG Wilson Fock Lat Cube SU Scroll Spire Tulip
open Window Mir Skye Scree Rush Dial Laic Thera Nacre Drapes Paige Vault Peaks Cascade Hive
open Buffered Buffered.Afterglow Buffered.Advance Reef Hom Tenant Branch Buffered.Concord Buffered.Afterglow.Satin Lifted
open MeasureTheory Push.SectorMeasure Girt
open scoped Topology ContDiff InnerProductSpace BigOperators Matrix MatrixOrder ComplexOrder Kronecker Classical Matrix.Norms.L2Operator ComplexConjugate Pointwise
attribute [local instance] opCStarAlgebra
open Supplies Sparkle Sparkle.Condense Sparkle.Portage Sparkle.Circuit Pastel Momentum Furnace
open Scherzo Kinetic Play Py Py.Rate LocalLimit Preparation Skyscraper IgnoreFog Vale Period
open Buffered.Reliance Buffered.Reliance.ShortWave Afterglow Afterglow.Journey
namespace Boon
variable {n m:Side}{z p a:ℝ} (v:Cover)(d:ℕ) (g:ℝ)
variable (K:Calibration)
def paneOff (S:Support (More n)) : Mark n := toMark (maskT S g (fun _=>1))

def blackout (S:Support (More n)) : Mark n:=1-paneOff g S
lemma sits (S:Support (More n)): AtSupport false (inspected S) (paneOff g S):=by
 apply AtSupport.fromEval; exact mask_env _ _ (Girt.rite_c _); exact mask_local _ _ (fun _ _ _=> rfl) le_rfl
 intro x; unfold maskT; by_cases p:Healthy g S x; · rw [Set.indicator_of_mem p]; exact Reed.Fine.one
 rw [Set.indicator_of_notMem p]; exact Reed.Fine.empty _
lemma safe(S:Support (More n)): AtSupport false (inspected S) (blackout g S):=by
 rw [blackout,sub_eq_add_neg,←neg_one_smul ℂ]; exact AtSupport.addM (AtSupport.oneM _) ((sits g S).smulM _)
lemma forehead (p:0 ≤ z) : Apt z (ShortWave.extinguish z g 1) (planar n v (d+4)) (blackout g (planar n v d)):=by
 intro i; by_cases h:Healthy g (planar n v d) i.1; · rw [blackout,Pi.sub_apply]; unfold paneOff toMark maskT; rw [Set.indicator_of_mem h]; change ‖(1:FC _)-1‖≤_; rw [sub_self,norm_zero]; unfold ShortWave.extinguish; positivity
 have t: ‖blackout g (planar n v d) i‖=1:= by change ‖(1:_)-maskT (planar n v d) g (fun _=> (1:FC _)) i.1‖=1; rw [maskT,Set.indicator_of_notMem h]; simp
 obtain ⟨j,u,b⟩:= Finset.not_disjoint_iff.mp h; obtain ⟨f,k,b⟩:= (flags_spec ..).1 b; rw [t]; have hv:f.1∈planar n v (d+4):= by
    apply (bay_mem _).2; refine (separation_triangle _ j f.1).trans ?_; rw [separation_comm j]; exact Nat.add_le_add ((bay_mem _).1 u) ((Work.E01.sep_touched _ _ k).trans (by omega))
 unfold ShortWave.extinguish; rw [one_mul,←Real.exp_add]; apply Real.one_le_exp; have he:= (lobe_paid z f i.1 _ p hv).trans' (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left b.le p) (inv_pos.mpr signs_pos).le); linarith only [he]
-- native spelling meter
abbrev fares {n:Side} (K:Calibration)(m:Side)(e:K.c m=n)(L:Loom n)(X:Mark n→ℂ) := ∃ C:ℝ, Metered K m (e.symm ▸ L) (fun f=> X (e ▸ f)) C
variable {K}{L:Loom n}{X:Mark n→ℂ}{e:K.c m=n}(M:fares K m e L X)
include M
lemma addition(f f': Mark n) (p:Envelope f)(u:Envelope f') : X (f+f')=X f+X f':=by subst n; exact M.choose_spec.sum f f' p u
lemma balance : X 1 = 1:= by subst n; exact M.choose_spec.unit
lemma nullX : X 0=0:=by subst n; simpa using M.choose_spec.mult 0 (0:Mark _)
lemma litLeft {S:Support (More n)} (p':0 ≤ a)(u:∀ (f:Mark n)(S':Support (More n))(v:ℝ),Apt z v S' f→ ‖X f‖≤ v*Real.exp (a*(m.val:ℝ)^4)){d:ℕ}(f:Mark n) (h:Apt z p S f)(v:Narrowed S d) (wx:AtSupport false S f):
    ‖X f‖ ≤ p*magnified K a d:=by subst n; exact Buffered.Reliance.shelter M.choose_spec (show Gross («K»:=K) _ X z a from ⟨p',fun h _=>u _ _ _ h⟩) v h wx
-- sign.
local notation "σ"=> planar n v d
local notation "Ψ"=> glow z (planar n v (d+4))
lemma refunded(p:0≤z)(w:0 ≤ a)(h:∀ f S' t,Apt z t S' f→‖X f‖ ≤ t*Real.exp (a*(m.val:ℝ)^4)) :
    ‖1-X (paneOff g (planar n v d))‖ ≤ extinguish z g 1 * magnified K a (2*(d+4)):=by
 let f:= paneOff g σ; let y:= blackout g σ
 have hv: 1=y+f:=by unfold y blackout f; abel
 have ht:X 1=X y+X f:= (congrArg X hv).trans (addition M y f (safe g σ).env (sits g σ).env)
 rw [balance M] at ht; change ‖1-X f‖ ≤_; conv_lhs=> rw [ht,add_sub_cancel_right]
 exact litLeft M w h y (forehead v d g p) (extent v (d+4) _) ((safe g σ).mono (rental ..)) -- `r` argument explicit tune
omit M
lemma replenish (P:Preparation)(W:Cashbox P) (u:0<g)(a:ℝ): Tendsto (fun s=> extinguish (Universum.slope P s) g a) atTop (𝓝 0):=by
 have he : Tendsto (fun s:ℕ=> extinguish (Universum.slope P s) g 1) atTop (𝓝 0):=by
    apply squeeze_zero' (Eventually.of_forall fun v=> by unfold extinguish; positivity) (g:=fun s=> extinguish (Universum.slope P s) (shutters P s 1) 1); swap
    · simpa using estimate P 0 1 (by norm_num)
    filter_upwards [(shrinks P 1).eventually (ge_mem_nhds u)] with s p; unfold extinguish; simp only [one_mul]; exact Real.exp_monotone (neg_le_neg (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left p (Universum.slope_n P s W).le) (inv_pos.mpr signs_pos).le))
 simpa only [mul_zero,extinguish,one_mul] using he.const_mul a
end Boon
end YM.CF.Signal
#print axioms YM.CF.Signal.Boon.refunded
