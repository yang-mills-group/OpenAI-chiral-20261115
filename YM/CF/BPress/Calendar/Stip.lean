import YM.CF.BPress.Calendar.Keep
/-! Mapped costs elementary remains NPL. uses only requirements actually proved over poses. -/
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 20000
noncomputable section
namespace YM.CF.BPress.Calendar
open Function NormedSpace Metric Finset MeasureTheory Filter Lattice RG Precision Pressure
open Cube Py Vale Vale.Grace Paige Scree Skye Fixed Dial Spire SU Wilson
open Net Hazel Chrono Sugar Lilac Grid Mount Recital Habitat Driver Meadow Meadow.Tent Meadow.Frame Meadow.Stamps Locale
open Wealth Weave Port Honey Before Between Recipe RG.PathData Branch LocalH Next.SectorChange Peel Spine Mosaic
open scoped Topology BigOperators Classical Matrix Matrix.Norms.Frobenius InnerProductSpace
attribute [local instance] Gauge.frobInner
variable {m s B:Side} {K:Teller SU.group}{R:Patch}{L:ChartRatio SU.group}
  {V: Grace K R L} {d x h p:ℝ} {U:Grasp V.U B d}{W:GivenX V U} {Mstar:Side} {J:Robes Mstar V W}
variable {P:Before V p}{X:P.Between d J.n} {f: Angel X}{E:Earning X}
namespace Around
open Currencies Pulse Stripe Manna
variable (G:Curb f E)
abbrev volume_k (y:ℝ) := (G.width y).val
-- Keep exact equality: no absolute monotonic issues.
-- costs use f.μ.L.Work.B and r(x). Ysp.Λ(x).
def BL(x:ℝ) := d0 1 (volume_k G x) 1 |lPay (ellK X) f.P_ f.Jc x+rMaxV (ellK X) (hunger f x) x|
def BJ(x:ℝ) := expense 4 (μMode f E x) (volume_k G x^3) (estate 2)* f.P_.jq x (ellK X)
def BE(x:ℝ) := d0 2 (volume_k G x) (counted (f.r x) (ellK X)) |Wealth.tin (f.r x) K.top.clip x f.η f.ζ K.top.paths|
def BK(x:ℝ):= expense 4 (μMode f E x) (volume_k G x^3*((ellK X)+2*X.z.M+1)) (constant 40)
def Burn(x:ℝ):= (((BL G x + BJ G x)+ BE G x) + BK G x * f.k x+ BK G x * Between.stipend E x) + (mie (BK G x) (value E) (small x) + BK G x * (Stripe.shadow (small x) (sbo f x)*(value E).price))
lemma rate_Exp {t:ℝ}(h:0<t): NPL fun i=>Real.exp (- (t*(small i:ℝ))) :=by
 constructor; intro m; simp_rw [small_l, ← neg_mul]; have he:= (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (m:ℝ) t h).comp lscale_late
 simp only [Real.rpow_natCast] at he; exact he
private lemma brushN {p:ℝ→ℝ}(v:NPL p) : NPL fun i=> |p i|:=v.mono <| Eventually.of_forall fun i=> by rw [abs_abs]
private lemma n0pl (b _s:ℕ)(r:ℝ→ℕ)(a:ℝ→ℝ)(h:PL fun i=>(r i:ℝ))(p:NPL a): NPL fun i=> d0 b (volume_k G i) (r i) (a i):=by
 unfold d0; simp only [Nat.cast_mul,Nat.cast_pow]; exact (((PL.const _).mul (G.PL.pow 3)).mul h).times (p.const_mul _)
lemma wages : NPL (Burn G):=by
 have hu : NPL (BL G):= n0pl G 1 1 _ _ (PL.const _) (brushN ((lprice _ _ _).add (tax_arg _ _ (hu_pl f))))
 have hb : NPL (BE G):= n0pl G 2 1 _ _ (counted_PL _ _ f.broad) (brushN (tin_npl K.top.clip _ f.broad f.ζ f.η))
 have ht : NPL (BJ G):= (ePL 4 _ (core_pl f E) _ (by simp only [Nat.cast_pow]; exact G.PL.pow 3) _).times f.shot
 have hx : PL (BK G):= ePL 4 _ (core_pl f E) _ (by simp only [Nat.cast_mul,Nat.cast_pow]; exact (G.PL.pow 3).mul (PL.const _)) _ -- tune
 let a:= sbo f; have hs:= sb_pl f; have hs': NPL (fun x=>Stripe.shadow (small x) (sbo f x)):=by
    unfold Stripe.shadow; apply NPL.add _ (hs.const_mul _); apply NPL.add; exact ((PL.const 4).mul small_PL).times hs; exact small_PL.times (((hs.const_mul _).add (hs.const_mul _)).add ((hs.const_mul _).mul (PL.const _))) -- tune capa reducibility
 unfold Burn; refine ((((hu.add ht).add hb).add (hx.times f.thin)).add (hx.times (broad E).2.1)).add ((hx.times ((rate_Exp (half_pos (value E).pos)).mul (PL.const _))).add (hx.times (hs'.mul (PL.const _)))) -- ambiguity .times
-- daily.Small utilities
abbrev depth(X:P.Between d J.n)(x:ℝ):ℕ:= ellK X+2*spanN X x+1
lemma dp : PL fun i=>(depth X i:ℝ):=by unfold depth; simp only [Nat.cast_add,Nat.cast_mul]; exact ((PL.const _).add ((PL.const _).mul span_pl)).add (PL.const _)
structure Warmth (x:ℝ):Prop where
 pace : Pocket G x
 mud : Burn G x ≤1/16384
 youth : Stripe.shellQ (sbo f x) ≤ E.t
 size : (depth X x:ℝ)* Stripe.blur (small x) (value E)≤ X.strength/16
 road: treasure E x
lemma warm : ∀ᶠ x:ℝ in atTop, Warmth G x :=by
 have ht:0<X.strength/16:=(by positivity [X.wage]); filter_upwards [Pocket.hobby G,(wages G).drop.eventually (ge_mem_nhds (show (0:ℝ)<1/16384 by norm_num)), ((sb_pl f).const_mul ClipSize).drop.eventually (ge_mem_nhds E.mono.high), ((dp (X:=X)).times ((rate_Exp (value E).pos).mul (PL.const (2*(value E).price)))).drop.eventually (ge_mem_nhds ht),(broad E).1] with x p d k' s h; exact ⟨p,d,k',s,h⟩
namespace Warmth
variable {G} (g: Warmth G x)
end Warmth
end Around
end YM.CF.BPress.Calendar
