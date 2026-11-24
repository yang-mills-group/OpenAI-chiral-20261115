import YM.SU5.Relativistic.Esthete
import YM.SU5.Selected.Glyph
/-!
# power per real Lens, Banyan receives and all priced
-/
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 6500
set_option maxHeartbeats 280000
set_option quotPrecheck false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.Reconstruction.Staved
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Heat Fock Analysis SlabMark OS.Semigroup MeshClock Set Vacancy Selected
open CF.Pannier.Chancel.ScreeV TopologicalSpace OS.Ground
variable {Λ : Preparation}{l:ℕ} (Y:Course Λ (VolumeCape.Dream.Nimbus l))(H:Real.exp 1≤Λ.x)
local notation "K"=> tent Y H
variable {i k:ℕ→ℕ}{I:ℕ→Family (tent Y H)→ℕ→ℂ}{E:ℕ→Family (tent Y H)→ℂ}(V:Universal Y H i k I E)(s:ℕ)
variable {D:ℕ→Family (tent Y H)→Family (tent Y H)}{a b:ℕ→ℕ} (Q:Coherent (i:=i) (k:=k) (E:=E) Y H D a b) (Qt:Clipped Y H (i∘a) (k∘b))
variable (j:Axis)(strict:Bool)(C:Arena Y H Q.circuit j 0 strict)
local notation "R" i:max x:max p:max=> entrance Y H V i Q Qt j strict C x p
local notation "A"=> driveAlgebra Y H V Q Qt j strict C
local notation "B"=> displayAlgebra Y H V Q Qt j strict C
local notation "Qₛ" s:max => response Y H V s Q Qt j strict C
local notation "Θ" x:max => atCharacter Y H V Q Qt j strict C x
local notation "Ξ" s:max w:max=> Entry Y H s j strict w
local notation "Θx" s:max x:max=> actorLabel Y H s j strict x

-- lays s kernel. 
lemma stack (w:ℕ)(x:Ξ s w)(h:0<w)(n:ℕ) :∃ (l:ℕ)(p:0<l)(y:Entry Y H s j strict l), (star (R s x h)*(R s x h))^(n+1)=R s y p ∧ y.val.val= thicket K j w x.val.val n:=by
 let a:= R s x h; let f:=SlabMark.inverse Y H s j strict w x; let y:=edit Y H s j strict w w f x
 have hp:0<w+w:=by omega
 have hs: star a*a=R s y hp:= (by unfold a; rw [entrance_adj]; exact entrance_pair ..)
 have he:y.val.val=tripleWide K j w x.val.val:= editor ..
 induction n with
 | zero=> rw [zero_add,pow_one]; exact ⟨_,hp,y,hs,he⟩
 | succ n ih=>
               obtain ⟨l,g,z,u,t⟩:= ih
               refine ⟨w+w+l, (by omega : 0<w+w+l), edit Y H s j strict (w+w) l y z,?_,?_⟩
               · rw [pow_succ',u]; change (star a*a)*_= _; rw [hs]; exact entrance_pair ..
               change _=thicket _ _ _ _ (n+1); rw [editor,he,t, thicket] -- tune casts w+w argument

variable (f: displayAlgebra Y H V Q Qt j strict C →⋆ₐ[ℂ] ℂ)
local notation "Ω"=> doorstep Y H V Q Qt j strict C f
local notation "P"=> Selected.arrive Y H V Q Qt j strict C f
lemma favor (X:A)(n:ℕ):let Z:= (star X*X)^(2^n); let W:ℝ:=‖(Θ f) X‖
    W^(2*(2^n))≤ ((Θ f) Z).re ∧ (Θ f) Z = ((‖(Θ f) Z‖:ℝ):ℂ):=by
 let YD(n:ℕ):= (star X * X)^(2^n); let φ:= Θ f; have h(a:A): φ (star a*a)=((↑(‖P a‖^2):ℂ)):=by rw [← show inner ℂ (P a) (P a) = _ from arrive_pair ..,inner_self_eq_norm_sq_to_K]; push_cast; rfl
 have hx(a:A):‖φ a‖≤‖P a‖:=by rw [← arrive_mean Y H V Q Qt j strict C f]; exact (norm_inner_le_norm ..).trans_eq (by rw [ready,one_mul]) -- Y conflict prep
 have ht(n): YD (n+1)=star (YD n)*YD n:=by unfold YD; rw [pow_succ,pow_mul,sq,star_pow,star_mul,star_star]
 have hf(a:A): φ (star a*a)=((‖φ (star a*a)‖:ℝ):ℂ):=by rw [h]; simp [Complex.norm_real,Real.norm_of_nonneg]
 change ‖φ X‖^(2*(2^n)) ≤ (φ (YD n)).re ∧ φ (YD n)=((‖φ (YD n)‖:ℝ):ℂ)
 induction n with
 | zero=>
    simp only [YD,pow_zero,pow_one,mul_one]; refine ⟨?_,hf X⟩
    rw [h,Complex.ofReal_re]; exact pow_le_pow_left₀ (norm_nonneg _) (hx _) _
 | succ n ih=>
    rw [ht]; refine ⟨?_, hf _⟩
    rw [pow_succ,←mul_assoc,pow_mul,h,Complex.ofReal_re] -- expects combine
    have he: ‖φ X‖^(2*(2^n)) ≤ ‖P (YD n)‖:= ih.1.trans ((Complex.re_le_norm _).trans (hx _))
    exact pow_le_pow_left₀ (by positivity) he _
-- reusable power to every point
private lemma thine {X:Type*}[MetricSpace X][CompactSpace X][MeasurableSpace X][BorelSpace X](μ:Measure X)[IsProbabilityMeasure μ][μ.IsOpenPosMeasure] (f:X→ℝ)(v:Continuous f)(c:ℝ)(t:0≤c)(e:∀ x,0≤f x)
    (P0:∀ n:ℕ, (∫ i,(f i)^(2*(2^n)) ∂μ) ≤ c^(2*(2^n))) (x:X) : f x≤ c:=by
 classical
 by_contra! h; obtain ⟨u,r,p⟩:= exists_between h
 let F:= {x| u<f x}; have hu: IsOpen F:=isOpen_lt continuous_const v; let T:= μ.real F; have hT:0<T:= ENNReal.toReal_pos (Measure.IsOpenPosMeasure.open_pos _ hu ⟨x,p⟩) (measure_ne_top _ _)
 have he(n:ℕ):T ≤ (c/u)^(2*(2^n)):=by
    let k:=2*(2^n); let a(i:X):=(f i)^k; have hf:Integrable a μ:= (v.pow _).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
    rw [div_pow]; apply (le_div_iff₀ (pow_pos (t.trans_lt r) _)).2
    apply (P0 n).trans'; change T*u^k ≤ _; rw [show T*u^k=∫ _ in F,u^k ∂μ by simp [T]]
    exact (setIntegral_mono_on (integrable_const _) hf.integrableOn hu.measurableSet (fun y hy=> pow_le_pow_left₀ (t.trans_lt r).le (show u<f y from hy).le _)).trans (setIntegral_le_integral hf (ae_of_all _ (fun i=> pow_nonneg (e i) _)))
 have hz:Tendsto (fun n:ℕ=>2*(2^n)) atTop atTop:= tendsto_atTop_mono (fun i=> le_trans Nat.lt_two_pow_self.le (Nat.le_mul_of_pos_left _ two_pos)) (show Tendsto id (atTop:Filter ℕ) atTop from tendsto_id) -- tune
 exact hT.not_ge (ge_of_tendsto' ((tendsto_pow_atTop_nhds_zero_of_lt_one (div_nonneg t (t.trans_lt r).le) (div_lt_one (t.trans_lt r)|>.2 r)).comp hz) he)

lemma shoulders {w:ℕ}(x:Entry Y H s j strict w)(h:0<w)
    (v:∀ n:ℕ, ‖E s (thicket K j w x.val.val n)‖ ≤ Real.exp (-2*staveP n)) :
     ‖response Y H V s Q Qt j strict C f (Θx s x.val)‖ ≤ Real.exp (-2):=by
 classical
 obtain ⟨U,u⟩:=display_receives Y H V Q Qt j strict C; haveI := u.normalized; haveI := u.support
 let μ:= U.μ; let X:= R s x h; let Φ(i:U.X)(a:A):= atCharacter Y H V Q Qt j strict C (U.character i) a
 let α:=Real.exp (-2)
 obtain ⟨i,t⟩:= u.onto.2 f
 have hν:(Qₛ s) f (Θx s x.val) = Φ i X:=by unfold Φ; rw [t, entry_read]
 rw [hν]; refine thine U.μ (fun i:U.X=> ‖Φ i X‖) ((u.weak (reduceToDisplay Y H V Q Qt j strict C X)).norm) _ (Real.exp_pos _).le (fun _=> norm_nonneg _) (fun n=>?_) i
 let k:=2^n; let m:= k-1; have hp:0<k:=pow_pos two_pos _; have hm:m+1=k:=by omega
 obtain ⟨l,h₀,y,p,e⟩:= stack Y H V s Q Qt j strict C w x h m; let Y':A:= (star X*X)^k
 have hs:Y'=R s y h₀:=by rw [hm] at p; exact p
 have hx:(∫ i,Φ i Y'∂U.μ)=E s (thicket K j w x.val.val m):=by
    rw [hs,←e]; simp_rw [Φ,entry_read]; exact survives_check Y H V s Q Qt j strict C U u _ -- dots tune
 have hu(i):Integrable (fun x:U.X=> Φ x i) U.μ:= (u.weak (reduceToDisplay Y H V Q Qt j strict C i)).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
 apply (integral_mono (((u.weak (reduceToDisplay Y H V Q Qt j strict C X)).norm.pow (2*(2^n))).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)) ((hu Y').re) (fun i=> (favor Y H V Q Qt j strict C (U.character i) X n).1)).trans
 change (∫ x, RCLike.re («K»:=ℂ) (Φ x Y') ∂U.μ) ≤ _; rw [integral_re (𝕜:=ℂ) (hu _),hx]; refine (Complex.re_le_norm _).trans ((v m).trans_eq ?_); rw [←Real.exp_nat_mul,staveP,hm,mul_comm] -- tune definitional

lemma razorB(z:ℝ) {w:ℕ}(x:Entry Y H s j strict w)(h:0<w)
    (v:∀ n:ℕ, ‖E s (thicket K j w x.val.val n)‖ ≤ Real.exp (z*staveP n)) :
     ‖response Y H V s Q Qt j strict C f (Θx s x.val)‖ ≤ Real.exp (z):=by
 classical
 obtain ⟨U,u⟩:=display_receives Y H V Q Qt j strict C; haveI := u.normalized; haveI := u.support
 let μ:= U.μ; let X:= R s x h; let Φ(i:U.X)(a:A):= atCharacter Y H V Q Qt j strict C (U.character i) a
 let α:=Real.exp (z)
 obtain ⟨i,t⟩:= u.onto.2 f
 have hν:(Qₛ s) f (Θx s x.val) = Φ i X:=by unfold Φ; rw [t, entry_read]
 rw [hν]; refine thine U.μ (fun i:U.X=> ‖Φ i X‖) ((u.weak (reduceToDisplay Y H V Q Qt j strict C X)).norm) _ (Real.exp_pos _).le (fun _=> norm_nonneg _) (fun n=>?_) i
 let k:=2^n; let m:= k-1; have hp:0<k:=pow_pos two_pos _; have hm:m+1=k:=by omega
 obtain ⟨l,h₀,y,p,e⟩:= stack Y H V s Q Qt j strict C w x h m; let Y':A:= (star X*X)^k
 have hs:Y'=R s y h₀:=by rw [hm] at p; exact p
 have hx:(∫ i,Φ i Y'∂U.μ)=E s (thicket K j w x.val.val m):=by
    rw [hs,←e]; simp_rw [Φ,entry_read]; exact survives_check Y H V s Q Qt j strict C U u _ -- dots tune
 have hu(i):Integrable (fun x:U.X=> Φ x i) U.μ:= (u.weak (reduceToDisplay Y H V Q Qt j strict C i)).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
 apply (integral_mono (((u.weak (reduceToDisplay Y H V Q Qt j strict C X)).norm.pow (2*(2^n))).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)) ((hu Y').re) (fun i=> (favor Y H V Q Qt j strict C (U.character i) X n).1)).trans
 change (∫ x, RCLike.re («K»:=ℂ) (Φ x Y') ∂U.μ) ≤ _; rw [integral_re (𝕜:=ℂ) (hu _),hx]; refine (Complex.re_le_norm _).trans ((v m).trans_eq ?_); rw [←Real.exp_nat_mul,staveP,hm,mul_comm] -- tune definitional
end YM.CF.Buffered.Afterglow.Tower.Reconstruction.Staved
#print axioms YM.CF.Buffered.Afterglow.Tower.Reconstruction.Staved.shoulders
