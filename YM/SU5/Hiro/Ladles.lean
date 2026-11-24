import YM.SU5.Hiro.Marinade
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 4500
set_option maxHeartbeats 500000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
open Hiro Ballad Papal Regis.Head Regis.Head.Brecht
open Twah (DirSpin)
open Lamour.Bridge.Celeste Lamour.Bridge.Celeste.Morn
namespace Spine
variable (P: Spine)(L G:DirSpin)(R:ℕ)(F D: PlaqAxes)(x y:Cover){κ:ℝ}(p:0<κ)(s:ℕ)
lemma Jade_spec : P.JadeRate L G R F D x y p s=P.jade L R F x p s*P.jade G R D y p s - (P.tastemaker L G R x y s) • P.view (pepperView F D x y p) s:= rfl
noncomputable def eReadL(s:ℕ): P.Test→ₗ[ℂ]ℂ:={ toFun f:=P.E s f.val,map_smul':=fun v f=>P.linear s f v,map_add':=fun x y=>by simpa using P.homeLinear s x y 1}
def Nuptials (E:P.Test→ₗ[ℂ]ℂ)(X Z:P.Test):= E (X*Z)- E X*E Z
variable (r c:ℕ→ℕ)(U V:ℕ→ Cover){k:ℕ→ℝ} -- k binder already type mismatch! rename
variable (pO:∀ i,0<k i)(b:ℕ→ℝ)
local notation "Χ" i:max => pepperView F D (U i) (V i) (pO i)
local notation "θ" i:max=> P.view (Χ i) (c i)
local notation "σ" i:max=> (P.tapestryRate (Χ i) (c i):ℂ)
local notation "ϱ" i:max=> P.artist (c i)
local notation "φ" i:max=> P.jade L (r i) F (U i) (pO i) (c i)
local notation "χ" i:max=> P.jade G (r i) D (V i) (pO i) (c i)
local notation "τ" i:max=> P.tastemaker L G (r i) (U i) (V i) (c i)
local notation "Ι" i:max=> P.JadeRate L G (r i) F D (U i) (V i) (pO i) (c i)
variable (β:ℕ→ P.Test→ₗ[ℂ]ℂ)
-- the actual required estimates
structure Priceplate : Prop where
 first :∀ᶠ n in atTop,‖β n (φ n)‖≤ b n
 last :∀ᶠ n in atTop,‖β n (χ n)‖≤ b n
 gauges :∀ᶠ n in atTop, ‖β n (θ n)-(σ n)‖ ≤ b n
 aux :∀ᶠ n in atTop, ‖β n (Ι n)‖ ≤ b n
#check @Priceplate
-- selection permission; after b and r,U,V. aggregate compact cost asks. note retains arbitrary n→ρ(k), not fixed test height. 
section
variable {P}{e v:ℝ}{X:Supplier}{R':P.Register}(t:uniform P R' X e v)
private lemma quickly {X:ℕ→ℕ→P.Test}(p:∀ n,0<b n)(t:∀ n,∀ v>0,∀ᶠ s in atTop, ‖P.E s (X n s).val‖≤ v∧ (∫ x,‖P.singleState 3 s x (X n s)‖^2∂(P.pillars 3)) ≤ v): ∃ h:ℕ→ℕ,∀ c:ℕ→ℕ,h≤c → (∀ᶠ i in atTop, ‖P.eReadL (c i) (X i (c i))‖ ≤ b i)∧ ∀ᵐ x∂P.pillars 3,∀ᶠ i in atTop,∀ j:Axis, ‖P.singleState j (c i) (P.otherSpectrum 3 j x) (X i (c i))‖ ≤ b i:=by
 let S(i):=min (b i) (discount i (b i)); have hx(i):0<S i:=by unfold S discount; have h:=p i; positivity
 choose h y using fun i=> eventually_atTop.1 (t i (S i) (hx i))
 refine ⟨h,fun c p'=> ⟨Eventually.of_forall (fun i=> ((y i (c i) (p' i)).1).trans (min_le_left ..)),?_⟩⟩
 let W(n:ℕ)(_:Unit)(x:P.Spectrum0 3):= ‖P.singleState 3 (c n) x (X n (c n))‖^2; have hp(i:ℕ)(l:Unit): Continuous (W i l):= ((P.chi_joint 3 (P.reading 3 _ _)).norm).pow _
 filter_upwards [prognosis W S hp (fun i l x=>sq_nonneg _) b p (fun n l=> (y n (c n) (p' n)).2) (fun n=> by simp; exact min_le_right ..)] with x u; filter_upwards [u] with i u a; rw [P.single_agrees]; exact ((pow_lt_pow_iff_left₀ (norm_nonneg _) (p i).le (by decide : 2≠0)).1 (u ())).le
include t
lemma pulls (p:∀ i,0<b i): ∃ q:ℕ→ℕ,∀ c:ℕ→ℕ,q≤c→ P.Priceplate L G F D r c U V pO b (fun i=> P.eReadL (c i)) ∧ ∀ᵐ x∂P.pillars 3,∀ j:Axis,P.Priceplate L G F D r c U V pO b (fun i=> P.singleState j (c i) (P.otherSpectrum 3 j x)):=by
 obtain ⟨a,u⟩:= quickly b (X:=fun i s=> P.jade L (r i) F (U i) (pO i) s) p (fun i d=> thinBudget L _ F _ _ t d);
 obtain ⟨d,v⟩:= quickly b (X:=fun i s=> P.jade G (r i) D (V i) (pO i) s) p (fun i d=> thinBudget G _ D _ _ t d);
 obtain ⟨w,x⟩:= quickly b (X:=fun i s=> P.JadeRate L G (r i) F D (U i) (V i) (pO i) s) p (fun i d=> thickBudget L G _ _ _ _ _ _ t d);
 obtain ⟨z,Z⟩:= auras (J:=fun i=> Unit) t (fun i (_:Unit)=>pepperView F D (U i) (V i) (pO i)) b p -- tune
 refine ⟨fun i=> max (max (a i) (d i)) (max (w i) (z i)),?_⟩; intro c l; obtain ⟨hp,H⟩:=u c (fun i=>(le_max_left (a i) _|>.trans (le_max_left ..)).trans (l i)); obtain ⟨hx,V⟩:=v c (fun i=>(le_max_right _ _|>.trans (le_max_left ..)).trans (l i)); obtain ⟨f,F⟩:=x c (fun i=>(le_max_left ..|>.trans (le_max_right ..)).trans (l i)); obtain ⟨g,Q⟩:=Z c (fun i=>(le_max_right ..|>.trans (le_max_right ..)).trans (l i));
 refine ⟨⟨hp,hx,Eventually.of_forall (fun i=> g i ()),f⟩,?_⟩; filter_upwards [H,V,F,Q] with z h t e p; exact fun j=> ⟨h.mono (fun _ h=> h j),t.mono (fun _ h=> h j), p.mono (fun i h=> (h j ()).le), e.mono (fun _ u=> u j)⟩
end
open Stationary (Gaia)
-- compare tangent positions (the two standard physical scaled turtles), rank norm and interaction. C weights. 
-- one currency of zoom (must measure into gauge currency, twice R). 
def rGauge(r:ℕ→ℕ)(i:ℕ):ℝ:= 2*r i
theorem fireGauge(U V:ℕ→ Cover)(r:ℕ→ℕ)(g:Tendsto r atTop atTop)(u:∀ i,0<r i)(X:Gaia)(v:Tendsto (fun i=> Onyx.riseX (r i) (U i-V i)) atTop (𝓝 X)): Tendsto (fun i=> Onyx.riseX (rGauge r i) (nodeC (U i)-nodeC (V i))) atTop (𝓝 X):= v.congr (fun i=>by ext a; simp [Onyx.riseX,Onyx.moor,rGauge,nodeC]; grind) -- tune
abbrev costM (i:ℕ):ℂ:= (rGauge r i:ℂ)^4 / (P.artist (c i):ℂ)^2
abbrev tip (i:ℕ):ℝ:= min 1 (Twah.keyV i / rGauge r i ^4)
variable {X: Gaia} (g:Tendsto r atTop atTop)(u:∀ i,0<r i)(v:Tendsto (fun i=> Onyx.riseX (r i) (U i-V i)) atTop (𝓝 X))(e:X≠0)(h:Tendsto (fun i=> (rGauge r i)^4/k i) atTop (𝓝 0))
lemma readyTip(n:ℕ)(w:0< r n):0<tip r n:= lt_min zero_lt_one (div_pos (Twah.keyV_positive _) (by unfold rGauge; positivity))
local notation "μ" i:max=> costM P r c i
include g u v e h
private lemma tempail : Tendsto (fun i=> (μ i)*(σ i)) atTop (𝓝 (speckleV F D SU.group X)):=by
 let t:=speckleV F D SU.group X; let z(i):=(P.artist (c i):ℂ)^2; let f(i):=(rGauge r i:ℂ)^4; have he: Tendsto (rGauge r) atTop atTop:= (tendsto_natCast_atTop_atTop.comp g).const_mul_atTop (by norm_num : (0:ℝ)<2);
 refine Metric.tendsto_nhds.mpr fun ε p=>?_; have h':= chicory P.run P.large P.law F D (R:=rGauge r) (fun i=> by unfold rGauge; have a:=u i; positivity) he (fireGauge U V r g u X v) e pO h (ε/8) (by positivity)
 filter_upwards [h'] with i u; let x:=σ i; have ht: 1/2 ≤ ‖(ϱ i:ℂ)‖:= (P.artRange (c i)).1.trans (by rw [Complex.norm_real]; exact le_abs_self _); have hp:0<‖(ϱ i:ℂ)‖:=lt_of_lt_of_le (by norm_num) ht
 have hv: ‖f i*x-z i*t‖ ≤ ε/8:= u (c i); change dist (f i/z i*x) _ < _; rw [dist_eq_norm, show f i/z i*x-t=(f i*x-z i*t)/(z i) from (by field_simp [(norm_pos_iff.mp hp),z]), norm_div]; have h0: ‖z i‖≥1/4:=by rw [show ‖z i‖=‖(ϱ i:ℂ)‖^2 from norm_pow ..]; nlinarith
 rw [div_lt_iff₀ (lt_of_lt_of_le (by norm_num: (0:ℝ)<1/4) h0)]; nlinarith only [h0,p,hv,mul_le_mul_of_nonneg_left h0 p.le]
omit g v e h
lemma fundTip (A:ℕ→ℂ)(w:∀ᶠ i in atTop, ‖A i‖≤ tip r i): Tendsto (fun i=> μ i*A i) atTop (𝓝 0):=by
 rw [tendsto_zero_iff_norm_tendsto_zero]; refine squeeze_zero' (Eventually.of_forall fun i=>norm_nonneg _) ?_ (by simpa only [mul_zero] using Twah.keyV_go.const_mul (4:ℝ)); filter_upwards [w] with i h; let x:= rGauge r i; let t:=ϱ i; have ht: 0<x:=by unfold x rGauge; have a:=u i; positivity
 have he: ‖(ϱ i:ℂ)‖≥1/2:= (P.artRange (c i)).1.trans (by rw [Complex.norm_real]; exact le_abs_self _); have hv: ‖(ϱ i:ℂ)‖^2≥ 1/4 :=by nlinarith
 rw [norm_mul,costM,norm_div,norm_pow,norm_pow,Complex.norm_real, Real.norm_of_nonneg (le_of_lt ht), div_mul_eq_mul_div, div_le_iff₀ (lt_of_lt_of_le (by norm_num:(0:ℝ)<1/4) hv)]; let b:=Twah.keyV i; have hp:0<b:=Twah.keyV_positive ..; have g:= (le_div_iff₀ (pow_pos ht 4)).1 (h.trans (min_le_right ..)); change x^4* ‖A i‖≤ 4*b*_; nlinarith only [hp,hv,g,mul_le_mul_of_nonneg_left hv hp.le] -- tune
include g v e h
lemma ripeness(t:P.Priceplate L G F D r c U V pO (tip r) β): Tendsto (fun i=> μ i *P.Nuptials (β i) (φ i) (χ i)) atTop (𝓝 (shotR L G (X:=X)*speckleV F D SU.group X)):=by
 let Xb(i):=(τ i); let B(i):= (β i) (θ i); let Fw(i):= (β i) (Ι i) - β i (φ i)*β i (χ i)
 have hx:= tempail P F D r c U V pO g u v e h
 have hv:= P.food_moves L G c r U V g u v e
 have hp:= P.fundTip r c u (fun i=> B i-σ i) t.gauges
 have hm:= P.fundTip r c u (fun i=> β i (Ι i)) t.aux; have hg:= P.fundTip r c u (fun i=> β i (φ i)*β i (χ i)) (by filter_upwards [t.first,t.last] with i p b; rw [norm_mul]; exact (mul_le_of_le_one_right (norm_nonneg _) (b.trans (min_le_left ..))).trans p)
 have he: Tendsto (fun i=>Xb i*(μ i*σ i + μ i*(B i-σ i))+(μ i*β i (Ι i) - μ i*(β i (φ i)*β i (χ i)))) atTop (𝓝 (shotR L G (X:=X)*speckleV F D SU.group X)):=by simpa only [add_zero,sub_zero] using (hv.mul (hx.add hp)).add (hm.sub hg)
 apply he.congr; intro i; rw [P.Jade_spec,map_sub,map_smul]; unfold Xb B Nuptials; simp only [smul_eq_mul]; ring -- tune
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
#print axioms YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine.pulls
#print axioms YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine.ripeness
