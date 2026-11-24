import Anomaly.Gab.Oval
/-!
 knob. Inputs $K,C$ from $works$. Pe basis assumed pre-early supplied (=pulseCost).
 Choose A, ε (for τ-kit) and rents before L & know the actual values on appointment.Ready. 
 -/
set_option autoImplicit false
set_option maxHeartbeats 700000
set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 24000
noncomputable section
namespace YM.CF.Py
open Function Module NormedSpace Filter Metric Finset
open Moto Hove Oath Haro Bake Fock Roots Rive Neon
open Lattice Wilson RG Lat Tune QuadClock Cube Scree
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Matrix.Norms.L2Operator Classical
attribute [local instance] opCStarAlgebra
variable {I E:Type}[Fintype I][NormedAddCommGroup E][NormedSpace ℂ E][FiniteDimensional ℂ E] {B:Basis I ℂ E} {m:ℕ}(pκ:SketchA B m) {L:Side}{H w Q A K C v0 v1 v2 ε T:ℝ}
namespace SketchA
variable {u f δ q b a U d:ℝ}
variable (g:0<q)
abbrev poledC (I:Type) [Fintype I]:= (Fintype.card (Sum I Unit):ℝ)
-- A for principal requires restore.Term C with μ.Pe. use Pe influx Gq (uniform Expr.Gamma), S bills.Q.Ct ≤ |gaugeStone Γ| q, representing Costs.
abbrev princeY(B:Basis I ℂ E)(K f μ:ℝ):= (fareZ B ((ρθ (ρZee B))*f) μ K)
abbrev prince_T(B:Basis I ℂ E)(K f μ:ℝ):= princeY B K f μ * βSize (ρZee B)
abbrev supplyT(B:Basis I ℂ E)(b c:ℝ):= poledC I * ρθ (ρZee B)*(1+|b|) * |c|
abbrev ariseS(B:Basis I ℂ E)(K f u b c J:ℝ):ℝ:=4+4*(|J|+|prince_T B K f u| + |supplyT B b c| * βSize (ρZee B))
abbrev δrails(B:Basis I ℂ E)(c f μ a b:ℝ) := (min 1 (1 / (1+|princeY B c f μ| + |supplyT B a b|)))
lemma railLight (B:Basis I ℂ E)(c f μ a b:ℝ): 0<δrails B c f μ a b:=by unfold δrails; exact lt_min zero_lt_one (one_div_pos.mpr (by positivity))
lemma railLow(B:Basis I ℂ E)(c f μ a b:ℝ):δrails B c f μ a b≤1:= min_le_left ..
-- choose A high enough for main and gaps. Add |J| for variants.Arbitrary.K.Entry.G.Se.Proof pre-L.
structure Boots (P:ArmorK)(K C f ε T u a b c:ℝ)(L:Side) :Prop where
 up:ScaleKit pκ K C P.g0 P.g1 P.g2 a T u f ε L
 hP:0 ≤ a
 pay: |prince_T B K f u| + |supplyT B b c| * βSize (ρZee B) + 1 ≤ a/2
 tire: Raise_L m L * (billGap a C K *((L.val:ℝ)⁻¹)^(m+1)) ≤ δrails B K f u b c * min (1/2:ℝ) (a/4)
 dreams : knotLove B (ρθ (ρZee B)*f) * (L.val:ℝ)^m ≤ (L.val:ℝ)^((m:ℝ)+tiny)
lemma withA {P:ArmorK}{K C u f ε T a b c:ℝ}(H:Next_L (fun L=>ScaleKit pκ K C P.g0 P.g1 P.g2 a T u f ε L))(v:0<a)(p: |prince_T B K f u|+|supplyT B b c| * βSize (ρZee B)+1≤a/2): Next_L (fun L=> Boots pκ P K C f ε T u a b c L):=by
 filter_upwards [H,γrise m (billGap a C K) (δrails B K f u b c * min (1/2:ℝ) (a/4)) (mul_pos (railLight ..) (lt_min (by norm_num) (by positivity))), grows_E m (knotLove B (ρθ (ρZee B)*f))] with n e r s L x; exact ⟨e L x,v.le,p,r L x,s L x⟩
lemma ariseK(B:Basis I ℂ E)(K f u b c J:ℝ): let A:=ariseS B K f u b c J; 0<A∧|prince_T B K f u|+|supplyT B b c| * βSize (ρZee B)+1 ≤ A/2:=by
 intro A; have hx:= front_pos (ρZee B); unfold A ariseS
 constructor <;> linarith only [mul_nonneg (abs_nonneg (supplyT B b c)) hx.le,abs_nonneg (prince_T B K f u),abs_nonneg J]
variable (P:ArmorK)
structure Braze (P:ArmorK)(K C u:ℝ)(b c J:ℝ) where
 m0:ℝ
 f:ℝ
 T:ℝ
 up: Next_L (fun L=> Boots pκ P K C f m0 T u (ariseS B K f u b c J) b c L)
def prep3 (b c J:ℝ) :Braze ιBuild3 P K C μ₃ b c J:=by
 let q:= hitch P.g0 P.g1 P.g2 C K; let f:=q.choose_spec; let k:= f.choose_spec; let Q:= k.choose_spec; let a:= ariseS Bθ K k.choose μ₃ b c J
 have hp:= ariseK Bθ K k.choose μ₃ b c J
 exact ⟨q.choose,k.choose,f.choose,withA ιBuild3 (Q.2.2.2 a hp.1.le) hp.1 hp.2⟩
def prep4 (b c J:ℝ) :Braze ιBuild4 P K C μ₄ b c J:=by
 let q:= process P C K; let f:=q.choose_spec; let k:= f.choose_spec; let Q:= k.choose_spec; let a:= ariseS Gior K k.choose μ₄ b c J
 have hp:= ariseK Gior K k.choose μ₄ b c J
 exact ⟨q.choose,k.choose,f.choose, withA ιBuild4 (Q.2.2.2 a hp.1.le) hp.1 hp.2⟩
end SketchA
end YM.CF.Py
