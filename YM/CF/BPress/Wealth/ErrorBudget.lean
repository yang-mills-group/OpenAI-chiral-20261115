import YM.CF.BPress.Wealth.Cover
/-! Active Taylor & purchase in y. Frame labels ignored for H severe charges pricing; no decoupling of templates. Dependence via column/ticket lemmas. Output adaptive controls usable on all sector fields accepted. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BPress.Wealth
open Function Filter MeasureTheory LocalH Lattice Wilson RG Precision Grid Push.AbsoluteSums Branch Ledger Cube Bands Tunnel Pressure Finset
open scoped Topology BigOperators Classical Matrix Matrix.Norms.Frobenius InnerProductSpace ContDiff
open SU Gauge
attribute [local instance] Gauge.frobInner
variable {s:Side}{B:BandWidth}(X:Bands s B)(M:ℕ)(R:PathData group)(d:Clip)(p:BudgetPoint)(β y:ℝ)(S:Finset X.Hcols) {Φ:Sheet.Atlas} {σ C Λ:ℝ}

def tailbudget (D ζ C:ℝ)(M:ℕ) := (d.direct * (3*(1+4*D)*ζ)+chPrice*(3*((1+ζ+4*D)*C)*((2*stretch ζ M+ζ)*C)))
def tin (D ζ C:ℝ) := 2*y*tailbudget d D ζ C M* finer y*temp y
lemma tin_pl (t:ℝ→ℕ)(h:PL fun i=> (t i:ℝ))(ζ D:ℝ) : PL fun i=> tailbudget d D ζ C (t i):=by
 unfold tailbudget; apply (PL.const _).add; apply (PL.const _).mul; apply (PL.const _).mul; refine PL.mul (PL.add ?_ (PL.const _)) (PL.const _); unfold stretch; exact ((PL.const _).mul ((((PL.const _).mul h).mul (PL.const _)))) -- tune defeq
lemma tin_npl (t:ℝ→ℕ)(h:PL fun i=> (t i:ℝ))(ζ D:ℝ) : NPL fun i=> tin (M:=t i) d (y:=i) D ζ C:= by
 convert ((finer_full.mul (tin_pl d (C:=C) t h ζ D)).const_mul 2) using 1; ext; unfold tin; ring
structure Poise (B:BandWidth) (W:Sheet.Atlas) (d:Clip) (D κ C ζ y:ℝ) (M:ℕ):Prop where
 plusD : 0<D
 dividend : Dividend D κ ζ y
 high : High B M
 kap : 0<κ
 chart : κ*temp y< W.δ
 pays : W.C*κ ≤ D
 pores : xi y ≤ κ*temp y/2
 curry : (counted M B.D:ℝ)* stipend d ζ D C*mA y≤sever d κ B.D*temp y

lemma poise (G:GapSize)(κ:ℝ)(g:0<κ)(t:κ≤1/16)(v:ℝ→ℕ)(h:PL fun i=>(v i:ℝ))(f:∀ᶠ i in atTop,1≤ v i)(C:ℝ)(Q:Sheet.Atlas): ∃ D ζ :ℝ, ∀ᶠ y:ℝ in atTop, Poise (G.select y) Q d D κ C ζ y (v y):=by
 let D:= Q.C*κ; have hD:= mul_pos Q.span g; obtain ⟨ζ,s,Z⟩:= weak_dividend D κ hD g t; let n:= G.blank.val+2*G.collar; have hn:0 < n:=Nat.add_pos_left G.blank.property _; let P:= sever d κ n; have hP:0<P:= half_pos (loss_pos d (by unfold severeP; positivity : 0<severeP κ n)) -- tune `u`.
 have e : NPL (fun i=>(counted (v i) n:ℝ)*stipend d ζ D C*(mA i/temp i)):= (((counted_PL n v h).mul (PL.const _)).times m_sub)
 refine ⟨D,ζ,?_⟩; filter_upwards [Z,high_purchase G v h f,(npl_temp.const_mul κ).drop.eventually (gt_mem_nhds Q.size), (x_sub.drop).eventually (ge_mem_nhds (half_pos g)), e.drop.eventually (ge_mem_nhds hP)] with y i w z a q; refine ⟨hD,i,w,g,z,le_rfl,?_,?_⟩; have ht:=temp_pos i.young; exact ((div_le_iff₀ ht).mp a).trans_eq (by ring)
 change (counted (v y) n:ℝ) *stipend d ζ D C* _ ≤ P*temp y; apply (div_le_iff₀ (temp_pos i.young)).mp; rw [mul_div_assoc]; exact q

variable {X M β y} {K:Bills X E}{U V:Micro s}{κ ζ D:ℝ}
-- severe price & regular error after exact substitution Wb for severe 0
variable (H:R.Bounds d σ C Λ)(g:Poise B Φ d D κ C ζ y M) (hp:Checks M p d) (e:p.threshold=temp y) (t:β∈ Set.Icc (y/2) (2*y))(f:Mission X y K V U)(d':ToneNoise y V)
def perturb (W:Sheet.Atlas)(X:Bands s B)(κ y:ℝ)(K:Bills X E):= canon X (softAl X κ y K W)
include g H t f d' hp e
lemma reg_error (i:Root s)(p':i∈ (Wealth.Θ X M (chosen X κ y K))): |error M R d p β y (perturb Φ X κ y K) U i| ≤ tin (M:=M) d (y:=y) D ζ C :=by
 obtain ⟨a,b⟩:= (mem_filter.mp p').2; have ht:= license a g.high f d' g.dividend b Φ g.chart g.pays g.plusD.le; unfold tin
 let x:= g.dividend.young; refine le_trans (theorem_box M R H g.dividend g.plusD e (show 0 ≤ β from le_trans (by positivity : 0≤ y/2) t.1) hp i ht) ?_; dsimp only [tailbudget]; -- tune `Wealth.Θ` shadow
 gcongr <;> first| exact t.2 | positivity [finer_pos x, temp_pos x, g.plusD,g.dividend.posC,chPrice_pos,budget_nonneg H.four,d.quadratic_pos,stretch_pos M g.dividend]
lemma storm_at (i:X.Hcols)(v:i∈chosen X κ y K): pays X M R d p β y (chosen X κ y K) (perturb Φ X κ y K) U i ≤ -(sever d κ B.D * β * (temp y)^2) := by
 apply storm X M R d p β y _ H g.dividend g.high g.plusD g.kap _ e f d' g.pores g.curry _ i v; exact le_trans (by positivity [g.dividend.young] :0≤y/2) t.1
 intro i; apply raw_le ?_ (softAl X κ y K Φ) _; positivity [g.plusD,temp_pos g.dividend.young]; intro i; exact (soft_bounds κ y Φ g.chart g.dividend.branch K i).trans (by rw [←mul_assoc]; exact mul_le_mul_of_nonneg_right g.pays (temp_pos g.dividend.young).le)
end YM.CF.BPress.Wealth
