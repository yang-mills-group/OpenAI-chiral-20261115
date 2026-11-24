import YM.CF.BProof.Release.Cut

/- formula for each angular p. Noise still inside, and weights share the same U with all
observers. Strong identity; avoids truncating fermionic factors in severe sectors.
At use, F includes left gauge weight but not heavy, nor Mark cancellations.
-/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BProof.Release
open Function Filter RG Wilson Lattice Finset Work Micro MeasureTheory Mag Angular Angular.Yard Charge Charge.Form Matrix Gauss Roll Precision Locale hot Law
open scoped Topology BigOperators Classical ENNReal Matrix MatrixOrder InnerProductSpace Matrix.Norms.L2Operator
local notation "G"=> SU.group
variable {s:Side}(Y:Yard s)(T:PathData G){c:Clip}{M:ℕ}(θ κ:ℝ)(y:ℝ){R q w:ℝ}(X:Beam c R Y.short M y) (H:Room Y M)(u:T.Bounds c w R q)(h: θ∈Set.Icc (1/2) 2)(K:Chart G)(P:Pub G)
variable (a:Book K P Y κ X)(Z:Finset Y.Col)(r:BudgetPoint)(β:ℝ)
variable (S:Hall s)(p:Y.Glyph)
variable {F:Type}[NormedAddCommGroup F][NormedSpace ℝ F][MeasurableSpace F][BorelSpace F][SecondCountableTopology F][CompleteSpace F]
abbrev probe := Y.FaceS
abbrev suit (f:Config G s→Y.FaceS→ F)(U:Config G s)(u:Y.FaceS) := Real.exp (-big Y c r T M β U) • f U u
def wage (f:Config G s→ Y.FaceS→ F)(V:House Y) := let U:= issue Y V; let x:=Y.sweepLabel y S U p; if Y.accepted y S U p then (∫ W, suit (M:=M) (c:=c) Y T r β f (Y.play y S U x W) x ∂Measure.pi (fun _:Bond s=> cloud G (xi y))) else 0
include u
lemma suited (f : Config G s→ Y.FaceS→ F)(k:Envelope (uncurry f))(kβ:0≤β): Envelope (uncurry (suit (c:=c) (M:=M) Y T r β f)) := by
 let a(U : Config G s):= big Y c r T M β U; have he(U : Config G s): 0≤a U:= sum_nonneg fun i _=> heavy_pos c r T M β U i kβ; have ht: Measurable a:= Finset.measurable_sum _ fun i _=> heavy_c c r T M β i u
 obtain ⟨C,g⟩:=k.cost; refine ⟨(Real.measurable_exp.comp (ht.neg.comp measurable_fst)).smul k.meas,C,?_⟩; intro x; unfold uncurry suit; rw [norm_smul,Real.norm_of_nonneg (Real.exp_pos _).le]; apply le_trans (b:=1*‖uncurry f x‖) (mul_le_mul_of_nonneg_right (Real.exp_le_one_iff.mpr (neg_nonpos.mpr (he _))) (norm_nonneg _)); simpa using g x
abbrev Cloud (s:Side)(y:ℝ):= Measure.pi fun _:Bond s=> cloud G (xi y)
lemma squall_pay (f:Config G s→Y.FaceS→ F)(p:Y.Glyph)(k:Envelope (uncurry f))(kβ:0≤β)(hp:xi y≤1) : Envelope (wage (c:=c) (M:=M) Y T y r β S p f) := by
 haveI:= cloud_unit G (xi y) (coin_pos ..) hp
 let W(V:House Y):= Y.sweepLabel y S (issue Y V) p
 have hx: Measurable W:= (sweepLabel_m ..).comp (issue_c Y)
 let q : House Y × Config G s→F:=fun x=>suit (M:=M) (c:=c) Y T r β f (Y.play y S (issue Y x.1) (W x.1) x.2) (W x.1); let V(U:House Y):= ∫ w,q (U,w) ∂Cloud s y
 have hb:= Law.pull (suited (M:=M) Y T u r β f k kβ) (((Y.play_m y S).comp ((((issue_c _).prodMk hx).comp (measurable_fst (β:=Config G s))).prodMk measurable_snd)).prodMk (hx.comp measurable_fst)) -- universe
 have ha:Envelope V:= Law.fund (Cloud s y) (show Envelope q from hb); obtain ⟨C,hC⟩:=ha.cost; refine ⟨ha.meas.ite (by exact (issue_c Y) (Y.accepted_m y S p)) measurable_const,C,?_⟩; intro i; unfold wage; dsimp only; split; exact hC _; rw [norm_zero]; exact (norm_nonneg _).trans (hC i)
include H a h
/-- cost removal in each wing after selecting accepted Y. -/
def gain (f:Config G s→Y.FaceS→ F)(V: House Y)(w:hot.Field Y):= let x:=Function.uncurry w; let L:= γ Y T θ y X Z x V; let U:=issue Y L; let a:=Y.sweepLabel y S U p; if bed Y κ y L=Z then if Y.accepted y S U p then (∫ W, let U':= Y.play y S U a W; Real.exp (cut P Y T θ y X r β Z x U') • f U' a ∂Cloud s y) else 0 else 0
abbrev pixels (Y:Yard s)(y:ℝ) := Measure.pi fun _:Y.Col=> Day.mark (trunc y) (Roll.Place Y)
variable (f:Config G s→ Y.FaceS→ F)(k:Envelope (uncurry f))(kβ:0≤β)(hp:xi y≤1)(kθ:θ=β*g y^2)
include k kβ hp kθ
lemma stanza :
    (∫ x,Y.selected y S p (Y.selcost y S (suit (M:=M) (c:=c) Y T r β f)) (Y.squash x) ∂prior G s)=
      Real.exp (outcost P Y T θ y X r β) • ∑ Z:Finset Y.Col,∫ v,∫ w,gain Y T θ κ y X P Z r β S p f v w ∂pixels Y y ∂lobby Y := by
 let L:= wage (M:=M) (c:=c) Y T y r β S p f; let C:= Real.exp (outcost P Y T θ y X r β)
 have hg: Envelope L:= squall_pay Y T y u r β S f p k kβ hp
 have hU(x:Config G s): L (enters Y x)= if Y.accepted y S x p then ∫ W,suit (M:=M) (c:=c) Y T r β f (Y.play y S x (Y.sweepLabel y S x p) W) (Y.sweepLabel y S x p) ∂Cloud s y else 0 := by
    unfold L wage; simp_rw [Y.accepted_eq y S _ (issue_enter Y x) p, Y.sweepLabel_eq y S _ (issue_enter Y x) p]; split_ifs; simp_rw [play_enter]; rfl
 rw [Y.replay y S p _ (suited Y T u r β f k kβ) hp]; simp_rw [show ∀ x, _ = L (enters Y x) from fun x=>(hU x).symm] -- tune
 rw [Law.apply_pres (visits Y) hg.meas]; let l(Z:Finset Y.Col):= Sky.chunk Y κ y Z L
 have he(x:Locale.House Y): L x=∑ Z,l Z x:=by unfold l Sky.chunk; simp [eq_comm]
 simp_rw [he] -- risk recursive when he RHS L! uses l; unfold simp only
 rw [integral_finsetSum]; swap; · intro i _; exact Law.pay (Sky.chunk_pay Y κ y i L hg)
 rw [Finset.smul_sum]; apply sum_congr rfl; intro i hi; unfold l; change (∫ x,Sky.chunk _ _ _ i L x ∂lobby Y)=C • _
 rw [Sky.fund K P Y T θ κ y X H u h a L hg i,← integral_smul]; apply integral_congr_ae; apply Eventually.of_forall; intro V; dsimp only; rw [← integral_smul,←integral_smul]; apply integral_congr_ae; apply Eventually.of_forall; intro w
 let W:=Sky.reach Y T θ y X i V (Function.uncurry w); change _ • (_ • Sky.chunk Y κ y i L W)=C • gain Y T θ κ y X P i r β S p f V w; unfold gain Sky.chunk L wage γ; dsimp only; split_ifs; swap; · simp
 · let U:=issue Y W; let b:=Y.sweepLabel y S U p
   change _ • (_ • (∫ v,suit (M:=M) (c:=c) Y T r β f (Y.play y S U b v) b ∂Cloud s y))= C • _; rw [← integral_smul,← integral_smul,← integral_smul]; apply integral_congr_ae; apply Eventually.of_forall; intro i'; unfold suit; dsimp only; rw [← mul_smul,← mul_smul,cancels P Y T θ y X H u h r β _ _ _ kθ,mul_smul] -- tune
 simp
end YM.CF.BProof.Release
