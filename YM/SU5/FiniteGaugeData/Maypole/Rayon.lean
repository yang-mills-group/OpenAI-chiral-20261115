import YM.SU5.FiniteGaugeData.Maypole.Hatter
/-! # small boost permit and continuation from reduced Shelf: earns boost covariance. -/
set_option autoImplicit false
set_option maxHeartbeats 390000
set_option synthInstance.maxSize 16000
set_option quotPrecheck false
set_option linter.unusedVariables false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Hierarchy.Seld.Vp.Luft
open Function Filter Metric Set MeasureTheory OS OS.Semigroup Mink General Lorentz Complex
open scoped Topology BigOperators NNReal ENNReal InnerProductSpace ComplexOrder
open Poin Celeritas Land Leal Breve Poin.Gem Boundary Probe Flute
variable {H:Hilbert}(S:OS.Semigroup H timeAxis)(e:Mink.Ray)(v w:H)(hΩ:∀ z:E4,M S z v=v){n:ℕ}
local notation "a"=>timeAxis
local notation "b"=> magnet e
local notation "u" => reduced (magnet e)
variable (F G:Fin n→H.Op)(X:Fin n→Cross timeAxis)(y:Points n) (A:Shelf S (reduced (magnet e))) (ν:Fin n→ℕ)(h:∀ i, inner ℝ (X i) (magnet e)=0)
-- scale spatial coordinates along B.Val actual.
abbrev γY (z:Fin n→ℝ)(i:Fin n):ℝ:= speed*z i
abbrev γH (z:Fin n→ℂ)(i:Fin n):ℂ:= (speed:ℂ)*z i
lemma γboard(t r:ℝ)(x:Cross timeAxis): board (b) t r x=board (reduced (magnet e)) t (speed*r) x:=by unfold board reduced; rw [smul_smul (speed*r) tempo, show speed*r*tempo=r from (by unfold speed tempo; ring)]
variable (t s y':Fin n→ℝ) (c d:ℝ)
lemma γShape : shape (u) t (γY s) X= shape (b) t s X := PiLp.ext fun i=> (γboard e _ _ _).symm
lemma γfee : γH (soaked s)= soaked (γY s):= by funext i; unfold γH γY soaked; push_cast; rfl
lemma γspur(g:Fin n→ℂ):γH (spur g s)=spur (γH g) (γY s):=by funext i; unfold γH γY spur; push_cast; ring
local notation "J"=> rise S (u) A (soaked s) 0 ν
-- motion limit. choose.
abbrev Permit(r:ℝ):Prop:= speed*|Real.sinh r|< Real.cosh r
abbrev Sleeps(r:ℝ):Prop:=∀ s∈ Icc (0:ℝ) 1,Permit (r*s)
lemma permit_0 : Permit 0:=by norm_num [Permit]
lemma sleeps0 :Sleeps 0:=fun t v=> by have he:0*(t:ℝ)=0:=zero_mul _; rw [he]; exact permit_0
lemma sleeps : ∃ ε:ℝ,0<ε∧ ∀ r:ℝ, |r|≤ ε→ Sleeps r:=by
 let D:= {x:ℝ| Permit x}; have he:D∈𝓝 (0:ℝ):=(isOpen_lt (show Continuous (fun x:ℝ=>speed*|Real.sinh x|) from by fun_prop) Real.continuous_cosh).mem_nhds permit_0; obtain ⟨ε,hε,v⟩:= Metric.nhds_basis_closedBall.mem_iff.mp he; refine ⟨ε,hε,fun r h t u' => v ?_⟩; rw [mem_closedBall,dist_eq_norm,sub_zero,Real.norm_eq_abs,abs_mul, abs_of_nonneg u'.1]; exact (mul_le_of_le_one_right (abs_nonneg r) u'.2).trans h
lemma ψcharge (c:ℝ)(h: Permit c)(t:StrictMono s): Radial (θδ c s) (γH (ηδ c s)):=by
 intro i j u'; change |((↑speed * _)-(↑speed * _:ℂ)).im| < _; unfold ηδ θδ soaked; simp; -- tune gammaH normalization Cast
 have he:s i<s j:= t u'
 rw [←ofReal_sinh,ofReal_re,← mul_assoc 512,←mul_assoc 512,←mul_sub,←mul_sub,abs_mul,abs_mul,abs_of_nonneg (by norm_num : (0:ℝ)≤512),abs_of_pos (sub_pos.mpr he)]; exact mul_lt_mul_of_pos_right h (sub_pos.mpr he)
lemma stints {A:Type*}[NormedAddCommGroup A][NormedSpace ℂ A]{f g:ℂ→A}
 (p:∀ i∈ Icc (0:ℝ) 1,AnalyticAt ℂ f (imaginary i) ∧ AnalyticAt ℂ g (imaginary i))(v:∀ᶠ x:ℝ in 𝓝 0, f x=g x): f I=g I:=by
 let T:= (Icc (0:ℝ) 1); let V:= imaginary '' T; have he:IsPreconnected V:= (isPreconnected_Icc).image imaginary (show Continuous imaginary from continuous_ofReal.mul continuous_const).continuousOn; have hz:0∈V:=⟨0,(by simp [T]),by simp [imaginary]⟩; refine lyc V hz he ?_ ?_ (v.filter_mono nhdsWithin_le_nhds) ⟨1,(by simp [T]),by simp [imaginary]⟩; rintro j ⟨x,h,rfl⟩; exact (p _ h).1; rintro j ⟨x,h,rfl⟩; exact (p _ h).2
lemma opalV (h:StrictMono s)(p:Permit (c*d)): Radial (initβ t s (imaginary d)) (soaked (γY y')) ∧ Radial (bτ t s y' c (imaginary d)) (γH (bχ t s y' c (imaginary d))):= by
 refine ⟨(opal t s (γY y') d c h).1,?_⟩; rw [uβ,vβ,γspur]; exact jetset _ _ _ _ (ψcharge s _ p h)
variable (r:ℝ)(V:ℂ→Fin n→H.Op)(p:∀ i:Fin n,∀ z:ℂ,AnalyticAt ℂ (fun z=>V z i) z)(p':∀ x:ℝ,Pavilion S v F (V x) ν (moveB e x).val)(ℓ:V (imaginary r)=G)(q:StrictMono s)(g:Sleeps r)
include p p' q h hΩ g
local notation "Q"=> Mell S v (u) A
local notation "ι" z:max=> bτ t s y' r z
local notation "χ" z:max=> γH (bχ t s y' r z)
local notation "τ"=> initβ t s
lemma sculpt : Mell S v (u) A (initβ t s (imaginary 1)) (soaked (γY y')) X F ν= Q (ι I) (χ I) X (V (angles r I)) ν:=by
 let f(z:ℂ):= Q (τ z) (soaked (γY y')) X F ν; let G'(z:ℂ):= Q (ι z) (χ z) X (V (angles r z)) ν
 rw [show imaginary 1=I from by simp [imaginary]]; show f I= G' I; refine stints ?_ ?_; swap
 · filter_upwards [pear t s y' r q] with i ⟨s0,t0⟩; unfold f G'; rw [realβ, thetaτ,thetaχ,γfee, ← meanR S v (u) A X F ν _ _ hΩ s0,← meanR S v (u) A X _ ν _ _ hΩ t0]; let Y:= strumβ t s i; let V0:= lτ t s y' r i; let W0:= lχ t s y' r i; let U:=shape (b) Y y' X; let Z:= shape (b) V0 W0 X; let T':= moveB e (r*i); have hv: turnO T'.val U=Z:=s_line e Y y' X h (r*i); -- supply h maybe .. incl e etc.
   rw [γShape, γShape, show (shape (b) (lτ t s y' r i) (lχ t s y' r i) X) =_ from hv.symm]; rw [show angles r (↑i:ℂ)=(↑(r*i):ℂ) from (by unfold angles; push_cast; rfl)]; apply (p' (r*i)).share U; show StrictMono (clockV a U); unfold U; rw [Vclock]; exact s0; show StrictMono (clockV a (turnO T'.val U)); rw [hv]; unfold Z; rw [Vclock]; exact t0
 intro x j; obtain ⟨he,hg⟩:= opalV t s y' r x q (g x j); let U:=imaginary x
 have hz(i:Fin n): AnalyticAt ℂ (fun z=> (χ z) i) U := analyticAt_const.mul (jets t s y' r U i).2; exact ⟨mellA S v u A X ν _ (fun _=> soaked (γY y')) (fun _=>F) U he (fun i=>initA ..) (fun _=>analyticAt_const) (fun _=>analyticAt_const), mellA S v u A X ν (bτ t s y' r) (fun z=> χ z) _ U hg (fun i=>(jets t s y' r U i).1) hz (fun i=> (p i (angles r U)).comp (angA r U))⟩
include ℓ
local notation "Jr"=> rise S (u) A (θδ r s) (γH (ηδ r s)) ν
lemma chevalV: inner ℂ v (pitch S F J (shape (b) t y' X) v)= inner ℂ v (pitch S G (Jr) (turnO (e.boost r).val (shape (b) t y' X)) v):=by
 have he:= sculpt S e v hΩ F X A ν h t s y' r V p p' q g; rw [init_n,one_smul, ← show imaginary 1=I from by simp [imaginary],uβ,vβ,angel,mul_one,one_smul,γspur, ℓ] at he
 have hu: Permit r:= by simpa only [mul_one] using g 1 (by simp)
 rw [← show spur (0:Fin n→ℂ) (γY y')= soaked (γY y') from (funext fun i=> by simp [spur,soaked]),stunts S v u A (soaked s) 0 _ F ν t _ hΩ (zbank s q),stunts S v u A _ _ _ _ _ _ _ hΩ (ψcharge s r hu q), γShape, γShape] at he; rw [track e t y' X h r]; exact he -- variable ordering likely wrong
#print axioms chevalV
end YM.CF.Buffered.Afterglow.Hierarchy.Seld.Vp.Luft
