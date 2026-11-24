import YM.CF.BPress.Sea.Butter
/-! eq:B-primary Ward. imaginary log package price after W + Teller. -/
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.BPress.Nougat
open Function Finset NormedSpace MeasureTheory Filter Metric Lattice Wilson Branch Fock Pec Spin SpinSign Spin.Pledge Pledge.Costs Cube Lat SU Spin.Paint Nacre Laic Font Push.AbsoluteSums.Paths Tulip Tenant Dial Scroll Thera
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators InnerProductSpace ContDiff Classical YM.CF.BPress.Vesper
attribute [local instance] opCStarAlgebra
variable {B m L N :Side}{q d a b K κ r:ℝ}
open Jet Spire Phase.Sample Brace Phase Kea Pic Sods Broc Ledger
namespace Voice
local notation "M" => Domain m B
local notation "P" => pWorks m B d r
abbrev Harmony(m B:Side)(d r:ℝ) := ↥(Brace.Chord m B d r)
variable {f:Harmony m B d r→ℂ} {C:ℝ} {T:Support (Domain m B)}
local notation "ζ"=> (Harmony m B d r)
lemma soloH (H:Shell.plot q r d κ K)(x y:Harmony m B d r)(u:Shell T y.val.2 x.val.1 x.val.2 a)(hf : Flash (pWorks m B d r) (partQ m B d r 1 K) 1 T f C) (p: y.val.1=1)(b: Slow 1 (hook y.val.2) q)(c:0<a)(t:a ≤κ): ‖f x-f y‖ ≤ C*a:=by -- tune x binder
 obtain ⟨F,W,E,Z,hu,g,v⟩:=H.spot u b c t; let A:=ball (0:ℝ) (2*a); let k(w:ℝ):Harmony m B d r:= if h:w∈ A then ⟨(F w,W w), (v w h).2.1,(v w h).2.2.2⟩ else x; have ht(g:ℝ)(p:g∈ A) :(k g).val=(F g,W g):=by unfold k; rw [dif_pos p]; --
 have hc:0∈A:=mem_ball_self (by positivity); have ha:a ∈ A:=mem_ball_zero_iff.mpr (by rw [Real.norm_of_nonneg c.le]; linarith)
 have hm : (partQ m B d r 1 K).test ℝ A k:=by
    intro x t; have X:=v x t; refine ⟨fun i=> (X.1 i).germ ?_,fun i=>(X.2.2.1 i).germ ?_⟩ <;> filter_upwards [(isOpen_ball.mem_nhds t)] with _ p <;> rw [ht _ p]
 have htc:= town (f ∘ k) A (convex_ball 0 _) ha hc (hf.plot ℝ A isOpen_ball k hm); rw [Function.comp_apply,Function.comp_apply,show k 0=y from (Subtype.ext (by rw [ht 0 hc, E, Z,←p])),hf.reads (k a) x (show (pWorks m B d r).rel T (k a) x from ?_),sub_zero,abs_of_pos c] at htc; exact htc
 change Agrees _ _ _∧ AgreeF _ _ _; rw [ht a ha]; exact ⟨hu,g⟩ -- tune tactic order
abbrev applause (F:Duet m B): Harmony m B d r→ℂ:=fun x=>Spire.hum m B F x.val.1 x.val.2
structure Hymn (m B:Side)(d r:ℝ) where
 w : Support (Domain m B)→ℝ
 piece: Support (Domain m B)→ Harmony m B d r→ℂ
structure Solo (H:Hymn m B d r)(F:Duet m B)(K a b:ℝ):Prop where
 duet : ∀ i:Support (Domain m B), Flash (pWorks m B d r) (partQ m B d r 1 K) 1 i (H.piece i) (H.w i)
 bills: Cash id H.w a b
 prime:∀ x:Harmony m B d r, Spire.hum m B F x.val.1 x.val.2=∑ i,H.piece i x -- Harmony inference
namespace Solo
variable {H:Hymn m B d r}{F:Duet m B} (p:Solo H F K a b)
lemma voiceSpin(h:Screen (pWorks m B d r) (partQ m B d r 1 K) 1 (applause F) a b):∃ H:Hymn m B d r,Solo H F K a b:=by
 obtain ⟨M',X,f,g,q⟩:=h; let H:Hymn m B d r:=⟨X,M'⟩
 refine ⟨H,f,⟨fun i=>(f i).pos, fun i=>?_⟩, q⟩; refine ⟨fun j=>?_, (hasSum_fintype _).summable,?_⟩; unfold Ledger.score; split; exact mul_nonneg (Real.exp_pos _).le ((f _).pos); exact le_rfl
 rw [tsum_fintype]; apply le_trans _ (g i); change _ ≤ hitE ..; unfold hitE hit0; rw [sum_filter]; exact le_rfl -- tune `class.Dec`
end Solo
end Voice
end YM.CF.BPress.Nougat
