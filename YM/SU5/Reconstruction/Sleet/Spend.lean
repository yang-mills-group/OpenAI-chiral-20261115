import YM.SU5.Reconstruction.Sleet.Frostline
import YM.SU5.Reconstruction.Trap.Rebate
import YM.SU5.Reconstruction.FirstWindows.MovingKets
/-! # Actual Wick-power test cost requirement and analytic pipeline. -/
set_option autoImplicit false
noncomputable section
namespace YM.ConePrice.Storm
open Set Filter Metric Function MeasureTheory Spectral Analysis
open scoped Topology ComplexOrder NNReal ENNReal InnerProductSpace Real Classical ComplexConjugate
open Complex CF.Buffered.Afterglow.Tower MeshClock Germ SelectionAnalysis OS Semigroup
variable {Γ : AddSubgroup ℝ} (d:Dense (Γ:Set ℝ))
-- positive requests at dense address
abbrev Shard(Γ:AddSubgroup ℝ) := {x:Γ // 0<(x:ℝ)}
def thermal (s:Shard Γ):ℝ:= s.val.val
lemma thermal_pos(s:Shard Γ):0<thermal s:=s.property
include d in
lemma thermal_course: Motion (@thermal Γ) := by
 refine ⟨thermal_pos, fun x e=>?_⟩
 have he(n:ℕ):∃ u:Shard Γ, dist (thermal u) x < (1/(ice n)) := by
    let W:= Ioi (0:ℝ)∩ Metric.ball x (1/(ice n)); have hn:0<1/ice n:=by have :=heatk n; positivity
    obtain ⟨y,p,q⟩:= d.exists_mem_open  (show IsOpen W from isOpen_Ioi.inter Metric.isOpen_ball) ⟨x,e,Metric.mem_ball_self hn⟩
    exact ⟨⟨⟨y,p⟩,q.1⟩, Metric.mem_ball.mp q.2⟩
 choose s b using he; refine ⟨s,(tendsto_iff_dist_tendsto_zero).mpr (squeeze_zero (fun _=> dist_nonneg) (fun i=> (b i).le) ?_)⟩
 have ht:Tendsto ice atTop atTop:= tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop
 simpa [one_div,Function.comp_def] using tendsto_inv_atTop_zero.comp ht

variable {H:Hilbert} {a:Axis} (S:OS.Semigroup H a)(X:Players Γ H)
  (g:∀ (u:Γ)(t:ℝ≥0),(X.play u).comp (S.E t)=(S.E t).comp (X.play u))
local notation "ℜ"=> Real.toNNReal
-- displacement s≥0 along a, v in spectator direction of Players. Don't assume lives for f.
def radiation (f:H)(s v:Γ):= inner ℂ f (S.E (Real.toNNReal (s:ℝ)) (X.play v f))
-- offset λ in a only, follow positive n1 first, independent scalar accounts along tilted ray.
def tiltTest (f:H)(ℓ:Γ)(t s:Shard Γ):= radiation S X f (ℓ+t.val+s.val) (t.val-s.val)
-- *one* tilted ray, plus offset ℓ as large as desired. No symmetry assumptions or direction costs for OTHER ray.
def Reflex (f:H) (ℓ:Γ)(C:ℝ):Prop:=∀ y:Shard Γ,Voucher thermal (fun x=> tiltTest S X f ℓ x y) C

variable (f:H)
include g in
lemma radiation_turn(s v:Γ): radiation S X f s (-v)=conj (radiation S X f s v):= by
 unfold radiation; rw [inner_conj_symm]; let Z:=(ℜ (s:ℝ)); conv_rhs=>lhs; rw [show S.E (Real.toNNReal (s:ℝ)) (X.play v f)= (X.play v) (S.E Z f) from (DFunLike.congr_fun (g v Z).symm f)]
 -- want inner f E (U- ...)= inner E f (U- ...); compare adj
 rw [show inner ℂ f (S.E Z (X.play (-v) f))=inner ℂ (S.E Z f) (X.play (-v) f) from ?_]
 · rw [X.shift_g H, neg_neg] -- X.shift_g v x y, yes
 nth_rw 1 [← S.sym Z]; exact ContinuousLinearMap.adjoint_inner_right _ _ _
include g in
lemma tilt_turn (ℓ:Γ)(s t:Shard Γ): tiltTest S X f ℓ s t= conj (tiltTest S X f ℓ t s):=by unfold tiltTest; rw [show s.val - t.val= -(t.val - s.val) from by abel, add_right_comm, radiation_turn S X g]
include g d in
lemma Reflex.weather {ℓ:Γ}{C:ℝ}(p:Reflex S X f ℓ C):∃ (F:ℝ→ℂ→ℂ)(G:ℂ→ℝ→ℂ),Squall C F G ∧ ∀ x y:Shard Γ, F (thermal x) (thermal y)= tiltTest S X f ℓ x y ∧ G (thermal x) (thermal y)= tiltTest S X f ℓ x y:=by
 apply preordained (thermal_course d) _ ?_ p; intro x; rw [show tiltTest S X f ℓ x = (fun y=> conj (tiltTest S X f ℓ y x)) from funext fun _=> tilt_turn S X g ..]; exact Voucher.reflected thermal (fun y=> tiltTest S X f ℓ y x) C (p x)
end YM.ConePrice.Storm
