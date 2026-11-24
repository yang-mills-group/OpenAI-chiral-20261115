import YM.CF.BPress.Spark.Hubs
/-! eq:B-Oexpect Reader configurations. Leave on any Actor. Universe parameter ℝ$ν_t$: memo Baton anchors. Promote on true history after pre-height purchase, x sufficiently large. -/
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.BPress.Engine
open Function Filter NormedSpace MeasureTheory Finset Complex Lattice Branch Ledger Push.AbsoluteSums Palmer Fock Pastry Pine Pine.EdgeD Pf Vesper Spin Spin.Pledge Spin.Stride Currency Spin.Cellar Spin.Cellar.Pass Spin.Basement Pine.Story -- check: Spark not available due Palmer.Spark. don't open Palmer.
open Spark -- ambiguous: namespace current?
open Cube Lat SU Spin.Paint Skye Girt Scree Tulip Tenant Pf.RealBook --
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators InnerProductSpace Classical YM.CF.BPress.Vesper
attribute [local instance] opCStarAlgebra
variable {N:Side}{D:Type}
structure Actor (N:Side)(D:Type) where
 seat : D→ Support N
 A: Raw D (Single N)
 M: Raw D (Single N)
 H: D → ℝ → Paint (More N)
 H': D→ ℝ → Paint (More N)
local notation "σ_" => Support (More N)
namespace Actor
variable (G:Actor N D)
abbrev col(i:D):= coupling ∘ G.H i
abbrev col'(i:D):= coupling ∘ G.H' i
abbrev keys(u:Bool)(i:D):= Locks (G.seat i) u
abbrev KG(i:D):= G.H i 2
abbrev spinLoan:= Spark.δLoan (keys G true) (keys G false) G.A G.M G.col

end Actor
variable (P:Form N D) (G:Actor N D)
variable [TopologicalSpace D]
structure price_spin (A: Actor N D) (R B F H : Pledge)(ε r:ℝ):Prop where
 gates : RealBook.Stoke (A.keys true) (A.keys false) A.A A.M A.col A.col' P.stage R B F H ε r quota -- variation charge irrelevant; assumed to make additional Crew support
 t : ∀ x, MatPlan (A.KG x)
variable {μ g q r ε h:ℝ}
variable (W:Pledge)
abbrev StarAmt:=1+ χPay W
lemma star_le : 1≤ StarAmt W:= le_add_of_nonneg_right (by unfold χPay; have he:= W.bought; positivity)
structure Perk (W:Pledge)(B:ℕ)(μ g q:ℝ):Prop where
 upl : Slogan (W.rate/2) μ (δPort B) (highP (StarAmt W) g B q)
 he : 0≤g
namespace Perk
open Pressure
variable {W}
lemma slow(B:ℕ)(S:Perk W B μ g q): μ ≤ δPort B:= by
 let t:= S.upl; refine le_trans ?_ (t.cap.trans (min_le_left ..)); have he:= S.upl.v; unfold Ξ; linarith
-- $regular_κ` includes all digits.
abbrev price (W:Pledge)(g q:ℝ)(B:ℕ):= logArc (W.rate/2) (highP (StarAmt W) g B q) + aPort B (2*q)
def κPort (W:Pledge)(B:ℕ):= min (δPort B) (W.rate/2)/4
lemma harvest (u:ℝ→ℝ)(P:NPL u)(q:∀ᶠ x in atTop,0≤u x)(W:Pledge): PL (fun x=>(κPort W (radiusB x))⁻¹)∧ NPL (fun x=> price W (BPress.g x) (u x) (radiusB x))∧ ∀ᶠ x in atTop,Perk W (radiusB x) (κPort W (radiusB x)) (BPress.g x) (u x) :=by
 let Q:=fun x=> highP (StarAmt W) (BPress.g x) (radiusB x) (u x); have ht: ∀ᶠ x in atTop,0<Q x:= (q.and (eventually_gt_atTop 0)).mono (fun x h=> high_pos (star_le W) (g_pos h.2) h.1 _)
 obtain ⟨h,e,p⟩:= art Q (fun x=>δPort (radiusB x)) (high_at _ P) ht (Eventually.of_forall fun _=>beam_p _) βPol.1 (half_pos W.pos)
 refine ⟨h,e.add (((βPol.2.pow 4).times (P.const_mul 2)).mul (PL.const τPort)),?_⟩; filter_upwards [p, eventually_gt_atTop 0] with x p u; exact ⟨p,(g_pos u).le⟩ -- tune `art` in Story or Pine
end Perk
open Perk
abbrev Tokens (N:Side):=Token (LocB N) N
abbrev TokensF (N:Side):=Token (Force N) N
structure Till (P:Form N D)(F: GramM N) where
 line: Tokens N
 gaze: TokensF N
 γ: Shimmer P.stage → ℝ
 e: D→ Shimmer P.stage →ℂ
structure Store (W:Pledge)(F:GramM N)(h ε r g q μ:ℝ)(T:Till P F):Prop where
 Tclock: Perk W F.p.B μ g q
 right: Payer post0 earth T.line (StarAmt W) (2*q) F.p.B
 fg: Payer post1 harbor T.gaze (StarAmt W) q F.p.B
 rit: RegTag F T.line (h:=h)
 ent: FTag F T.gaze (h:=h)
 pfo: Offered W (P:=P.stage) (F:=G.spinLoan) T.e T.γ
 key: ∀ x, Issued (G.keys true x) (G.keys false x) (G.A x) (G.M x) (G.col x) (G.col' x) r ε
 prices: ∀ x, MatPlan (G.KG x)
 prom: Prom F
-- choices before $x$ use Pledge→
variable (s t u v: Pledge)
structure Treasury (s t u v W:Pledge)(ε r:ℝ):Prop where
 shelves(T:Actor N D) : price_spin P T s t u v ε r→∀ a b,W.Costs P.stage (T.spinLoan a b) -- not use this shape; change ∀ {N D}. drop
lemma prechoice (p:0<ε)(k:0≤r)(q:r<1): ∃ W:Pledge,∀ {N:Side}{D:Type}[TopologicalSpace D]{P:Form N D}, Treasury P s t u v W ε r:=by
 obtain ⟨W,w⟩:=penny Form.paid p k q s t u v; refine ⟨W,?_⟩; intro N D _ P; exact ⟨fun x h=> w h.gates⟩
lemma accounting {F:GramM N}{κ z:ℝ}(S:Treasury P s t u v W ε r)(X:price_spin P G s t u v ε r)(L:Perk W F.p.B μ g q)(H:YM.CF.Graph.Ledger h q q κ z F)(p:0 ≤ q)(R: StarAmt W ≤ h)(k:F.p.supportExponent=1): ∃ T:Till P F, Store P G W F h ε r g q μ T:=by
 obtain ⟨U,w,l⟩:= crown_earn W (S.shelves G X); obtain ⟨A,e,x⟩:= treasure H k (star_le W) p R; obtain ⟨B,g,t⟩:= gems H k (star_le W) p R; exact ⟨⟨A,B,w,U⟩,L,e,g,x,t,l,X.gates.peak,X.t,warmth _ H⟩ -- tune order
end YM.CF.BPress.Engine
