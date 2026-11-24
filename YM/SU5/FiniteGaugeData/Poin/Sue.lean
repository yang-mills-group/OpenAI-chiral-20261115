import YM.SU5.FiniteGaugeData.Poin.Hector
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
/-! # Take a single path. real parameters apply estimate. pure imaginary never leave W-admissible wedge even for unbounded Minkowski positions: Eu $λ(t)=z*r$ at `$z=i$`. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Hierarchy.Seld.Poin
open Flute Filter Function Set OS OS.Semigroup Mink Mink.General Mink.Lorentz Complex
open scoped Topology ContDiff NNReal InnerProductSpace
variable {n:ℕ}(t s y v:Fin n→ℝ) -- $t$ base Mink times, $s$ base heights, $y$ base parallel
variable (x r:ℝ)(z:ℂ)(i j:Fin n)
local notation "a"=>timeAxis
def initβ (z:ℂ) (i:Fin n):= (s i:ℂ)-z*t i
def angles (r:ℝ)(z:ℂ):ℂ:= r*z
local notation "θ"=>angles r z
local notation "Λ"=>initβ t s
abbrev bτ (z:ℂ)(i:Fin n):= cos (angles r z)*initβ t s z i - sin (angles r z)* (y i)
abbrev bχ (z:ℂ)(i:Fin n):= sin (angles r z)*initβ t s z i + cos (angles r z)*(y i)
lemma angA : AnalyticAt ℂ (angles r) z:= analyticAt_const.mul analyticAt_id
lemma initA : AnalyticAt ℂ (fun z=> Λ z i) z := analyticAt_const.sub (analyticAt_id.mul analyticAt_const)
lemma jets : AnalyticAt ℂ (fun z=> bτ t s y r z i) z ∧ AnalyticAt ℂ (fun z=> bχ t s y r z i) z:=by
 let f(z):=angles r z; have he: AnalyticAt ℂ (fun z=>cos (f z)) z:= analyticAt_cos.comp (angA r z); have hh:AnalyticAt ℂ (fun z=>sin (f z)) z:= analyticAt_sin.comp (angA r z); have g:= initA t s z i; exact ⟨(he.mul g).sub (hh.mul analyticAt_const),(hh.mul g).add (he.mul analyticAt_const)⟩
abbrev strumβ (x:ℝ):Fin n→ℝ:=fun i=>s i-x*t i
def lτ (x:ℝ):Fin n→ℝ:=fun i=> useu (r*x) (strumβ t s x i) (y i)
def lχ (x:ℝ):Fin n→ℝ:=fun i=> user_ (r*x) (strumβ t s x i) (y i)
@[simp] lemma realβ : Λ (x:ℂ) = soaked (strumβ t s x):=by funext i; simp [initβ, soaked, strumβ]
@[simp] lemma thetaτ : bτ t s y r (x:ℂ)=soaked (lτ t s y r x):=by funext i; simp [bτ,lτ,useu,angles,soaked]
@[simp] lemma thetaχ : bχ t s y r (x:ℂ)=soaked (lχ t s y r x):=by funext i; simp [bχ,lχ,user_,angles,soaked]
def θδ (z:ℝ)(s:Fin n→ℝ):= soaked fun i=> Real.cosh z*s i
def ηδ (z:ℝ)(s:Fin n→ℝ):= fun i=> (Real.sinh z:ℂ)*(s i:ℂ)*I
abbrev imaginary (x:ℝ):ℂ:=x*(Complex.I)
lemma angel : angles r (imaginary x)=imaginary (r*x):=by unfold angles imaginary; push_cast; ring
lemma init_n : initβ t s (imaginary x)=spill (soaked s) (x • t):=by funext i; unfold spill initβ imaginary sideways soaked; simp; ring
abbrev tβ (r:ℝ): Fin n→ℝ:= fun i=> hyperu r (t i) (y i)
abbrev sβ (r:ℝ): Fin n→ℝ:= fun i=> hypers r (t i) (y i) -- binder t y vs s? uses t
lemma uβ : bτ t s y r (imaginary x)=spill (θδ (r*x) s) (tβ (x • t) y (r*x)) := by
 funext i; unfold bτ; rw [init_n,angel,imaginary,cos_mul_I, sin_mul_I]; unfold spill θδ tβ hyperu sideways soaked; push_cast; ring
lemma vβ : bχ t s y r (imaginary x)=spur (ηδ (r*x) s) (sβ (x • t) y (r*x)):=by
 funext i; unfold bχ; rw [init_n,angel,imaginary,cos_mul_I, sin_mul_I]; unfold spur spill ηδ sβ hypers sideways soaked; push_cast
 -- I^2 factor
 ring_nf; simp
lemma char(n:ℕ)(s:Fin n→ℝ)(h:StrictMono s): Radial (θδ x s) (ηδ x s):=by
 intro i j a'; change |((ηδ x s j)-(ηδ x s i)).im| < ((θδ x s j)-(θδ x s i)).re
 have he:0<s j-s i:=sub_pos.mpr (h a'); unfold ηδ θδ soaked; simp; have ht: |Real.sinh x| < Real.cosh x:= abs_lt.mpr ⟨by have hx:= Real.sinh_lt_cosh (-x); rw [Real.sinh_neg,Real.cosh_neg] at hx; linarith,Real.sinh_lt_cosh _⟩; rw [←mul_sub,← mul_sub,abs_mul,abs_of_pos he]; exact mul_lt_mul_of_pos_right ht he
lemma opal (h:StrictMono s): Radial (initβ t s (imaginary x)) (soaked y) ∧ Radial (bτ t s y r (imaginary x)) (bχ t s y r (imaginary x)):=by
 rw [init_n,uβ,vβ]; have he: spur (soaked y) (0:Fin n→ℝ)=soaked y:=funext fun _=> by simp [spur]
 refine ⟨?_,jetset _ _ _ _ ?_⟩
 · exact he ▸ jetset (soaked s) (soaked y) (x • t) 0 ( (wet _ _).2 h)
 exact char (r*x) n s h -- order
-- neighborhood where hypotheses licensed
#print axioms opal
lemma locall {G:ℝ→Fin n→ℝ}(p:StrictMono (G 0))(h:∀ i,ContinuousAt (fun x=> G x i) 0) : ∀ᶠ x:ℝ in 𝓝 0, StrictMono (G x):= eventually_all.mpr (fun i=>eventually_all.mpr (fun j=>eventually_all.mpr (fun e=> eventual_pre (h i) (h j) (p e))))
where
 eventual_pre{f g:ℝ→ℝ}(p:ContinuousAt f 0)(q:ContinuousAt g 0)(e:f 0<g 0):∀ᶠ t in 𝓝 0, f t<g t:=by exact (p.eventually_lt q e) -- tune
lemma pear (h:StrictMono s): ∀ᶠ x:ℝ in 𝓝 0, StrictMono (strumβ t s x)∧StrictMono (lτ t s y r x):=by
 apply Eventually.and <;> (apply locall <;> first |(intro i j p; first|(simpa [strumβ] using h p)|(simpa [lτ,useu,strumβ] using h p))|skip)
 all_goals intro i; first|(unfold lτ useu strumβ; fun_prop)|(unfold strumβ; fun_prop)
abbrev sticks:Set ℂ:= Set.range imaginary
lemma irk : IsPreconnected sticks:= isPreconnected_range (show Continuous imaginary from continuous_ofReal.mul continuous_const)
lemma starship {X:Type*}[NormedAddCommGroup X][NormedSpace ℂ X] {f g:ℂ→X}(p:∀ x:ℝ, AnalyticAt ℂ f (imaginary x))(k:∀ x:ℝ,AnalyticAt ℂ g (imaginary x))(v:∀ᶠ i:ℝ in 𝓝 0,f i=g i): f I=g I:= by
 refine lyc sticks ⟨0,?_⟩ irk ?_ ?_ (v.filter_mono nhdsWithin_le_nhds) ⟨1,?_⟩; simp [imaginary]; rintro _ ⟨x,rfl⟩; exact p x; rintro _ ⟨x,rfl⟩; exact k x; simp [imaginary]
#print axioms pear
#print axioms starship
end YM.CF.Buffered.Afterglow.Hierarchy.Seld.Poin
