import YM.CF.BPress.Calendar.Magnate
/-! Wage upper and gvol.Pref. Absorb as a fixed power. Still no period dependence. -/
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
variable {P:Before V p}{X:P.Between d J.n} {f: Angel X} (E:Earning X)
namespace Around
open Currencies Pulse Manna Manna.Budget Huon Stripe Contour Rates Pilot Mount.Silhouette
local notation "Λ"=> era X x
-- sup cost poly including xRΦ etc
abbrev payρ(f:Angel X)(x:ℝ):= Pole f.P_ K.top.clip L (value E) (ellK X) K.top.paths x
lemma paysH : ∃ A:ℝ,0<A ∧ ∀ᶠ x:ℝ in atTop,payρ E f x ≤ A*x^2:=by
 let K':=job_p (ellK X) L f.charge; have he:=K'.add ((PL.const (portDim (ellK X):ℝ)).mul (trace_pl f.P_)); let F (x):= |Real.log (job_m (ellK X) L x)|+(portDim (ellK X):ℝ)* traceTab (f.P_.low x) f.P_.upper+(((value E).price+1)+Real.log 2); let a(i:ℝ):= payρ E f i; let f₀:=(rootsCount*payC K.top.clip 2 K.top.paths:ℝ); have ht : PL F:= he.add (PL.const _); have hp:= ht.times pli; refine ⟨|f₀|+1,by positivity,?_⟩; filter_upwards [eventually_gt_atTop (1:ℝ), hp.drop.eventually (ge_mem_nhds zero_lt_one)] with x hx p; change F x * x⁻¹ ≤ _ at p; have v:0<x:=(by linarith); rw [← div_eq_mul_inv] at p; have hu:= (div_le_one v).1 p; unfold payρ Pole; apply le_trans ?_ ((mul_le_mul_of_nonneg_left (by nlinarith only [hx] : x≤x^2) (by positivity :0≤|f₀|+1))); change f₀*x + _ + _ + _≤_; unfold F at hu; nlinarith only [hu, le_abs_self f₀,v]

lemma logHead :∃ a:ℝ,0<a∧ ∀ᶠ x:ℝ in atTop, ∀ (m B:Side) (A:Bands (More (mid m B)) (era X x))(T:GramM (mid m B))(i:A.Index)(R':Recipe (A:=A) T),T.funds=K.top.clip→R'.C=K.top.paths→T.beta∈ Set.Icc (x/2) (2*x)→ 25* quoteN (y:=x) A i * cashmark R' (f.k x) (value E) (Between.stipend E x) i ≤ Real.exp (a*x^2*((More (mid m B)).val:ℝ)^3):=by
 obtain ⟨H,k,t⟩:= ang_cash f.T; obtain ⟨K',x,C⟩:= Wealth.income K.top.clip X.toGapSize K.top.paths f.k f.thin; let b:=(value E).price; have he:0<b:=(value E).bought; let L':=4*(b+1)+2*H+K'+8*Chalk.ν^2; have hx:0<L':=by unfold L'; positivity
 refine ⟨L',hx,?_⟩; filter_upwards [t,X.toGapSize.bound_y,C, (broad E).2.1.drop.eventually (ge_mem_nhds zero_lt_one), eventually_gt_atTop (1:ℝ)] with x v t q a h m B A T i W K0 K1 K2
 let D:=era X x; let N:=mid m B; let s:=(More N).val; let w:=(s:ℝ)^3; let Q:= cashmark W (f.k x) (value E) (Between.stipend E x) i; let e:= Chalk.cost_site^(Chalk.withinX (A.band i)).card
 have hQ:0≤ cashmark W (f.k x) (value E) (Between.stipend E x) i:=by unfold cashmark costW heightP Mount.Silhouette.tax yolk Chalk.cost_site; positivity
 refine (mul_le_mul_of_nonneg_right (v _ _ A i) hQ).trans ?_; have hp: (D.P:ℝ)≤ 2*x:=t; have hv:0≤w:=(by unfold w; positivity); have ht:0<x:=(by linarith); let M:ℝ:=D.marked.val+1; have he: M ≤ 4*x:= by have hh: (D.marked.val:ℝ) ≤ D.P:= Nat.cast_le.mpr (Nat.le_add_right ..); unfold M; linarith
 unfold cashmark costW; rw [K0,K1]; unfold heightP; have hz:= Chalk.bodyNeed (N:=N) A i; refine (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hz (Real.exp_pos _).le) (Real.exp_pos _).le) (Real.exp_pos _).le).trans ?_; simp only [←Real.exp_add,A.band_card,Nat.cast_add,Nat.cast_one,Nat.cast_mul,Nat.cast_pow]; apply Real.exp_monotone -- tune `M Notation nat cast`
 have hc:=q _ A T.beta K2 i; change priceMark A K.top.clip T.beta K.top.paths (f.k x) i≤ K'*x^2*w at hc; have hT:Real.log x≤x:= Real.log_le_self ht.le; set S:= Between.stipend E x; have hS:S≤1:=a
 let yP:=priceMark A K.top.clip T.beta K.top.paths (f.k x) i; change H*D.P*Real.log x*w+(yP+(M*w*(b+S)+2*Chalk.ν^2*(M*w)))≤ L'*x^2*w
 have h1: (D.P:ℝ) * Real.log x ≤ 2*x*x:=by gcongr; exact Real.log_nonneg h.le -- tune may no goals
 calc
    _ ≤ H*(2*x*x)*w + (K'*x^2*w +(4*x*w*(b+1)+2*Chalk.ν^2*(4*x*w))) := by
       rw [mul_assoc H (D.P:ℝ)]; refine add_le_add ?_ (add_le_add hc (add_le_add ?_ ?_)); gcongr; apply (mul_le_mul_of_nonneg_left (add_le_add le_rfl hS) (mul_nonneg (by unfold M; positivity) hv)).trans; gcongr; gcongr -- tune
    _ ≤ L'* x^2*w := by unfold L'; have hx:0≤ (4*(b+1)+8*Chalk.ν^2)*w:=(by have hb:0<b:=‹0< b›; positivity); nlinarith only [mul_le_mul_of_nonneg_right ((show x≤x^2 by nlinarith only [h])) hx]
end Around
end YM.CF.BPress.Calendar
