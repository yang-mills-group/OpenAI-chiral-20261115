import YM.SU5.Selected.Prag.Ram
import YM.SU5.Selected.Actress.Scarves
set_option autoImplicit false
set_option synthInstance.maxSize 29000
set_option maxHeartbeats 290000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.Germ.Alliance
open Function Filter Metric Topology NormedSpace
open scoped BigOperators Kronecker InnerProductSpace ComplexOrder NNReal ENNReal Classical
variable {Γ:AddSubgroup ℝ} {A:Hilbert}{j:Axis}(P:Alliance (Trans j) Γ A) (dp:Dense (Γ:Set ℝ)) (S: OS.Semigroup A j)(q: ∀ i v t, Commute ((P.crew i).play v) (S.E t))
local notation "u" t:max=> S.E t
local notation "L₀"=> P
local notation "δ"=> dp
local notation "X"=> look j
local notation "T₀"=> (L₀).Realm X
local notation "Y"=> prism P
local notation "V"=> Frog P dp S q
open Spectral Spectral.Alps
-- Projection P not asserted to preserve chronological products beyond two-point separated correlations. extend analytic. parameter orbit E4 norm coordinate physical T^Φ.
variable (z:Trans j→Γ) (x y:A)
local notation "ι"=> (fun a:Trans j=>(z a:ℝ))
local notation "S₀"=> pours j
local notation "ϱ"=> (V).U (pours j (fun a:Trans j=>(z a:ℝ)))
local notation "ϕ"=> P.raw (X) z
private lemma magic {a:Axis}(H:Hilbert)(V':OS.Semigroup H a)(x y:H)(U:H.Op):
    Continuous (fun i:Unit→ℂ=> inner ℂ x (U (balcony V' (i ()) y))) ∧ AnalyticOnNhd ℂ (fun i:Unit→ℂ=> inner ℂ x (U (balcony V' (i ()) y))) (waist Unit) :=by
 refine ⟨continuous_const.inner (U.continuous.comp ((balcony_cont V' y).comp (continuous_apply ()))),fun i z=>?_⟩; let Q:(Unit→ℂ)→L[ℂ]ℂ:= ContinuousLinearMap.proj (); let f:H.Op→L[ℂ]ℂ:= ((innerSL ℂ x).comp U).comp (ContinuousLinearMap.apply ℂ H.space y)
 exact (show AnalyticAt ℂ (f ∘ balcony V' ∘ Q) i from (f.analyticAt _).comp ((balcony_holo V' (Q i) (z ())).comp (Q.analyticAt i)))
private lemma opera (F G:(Unit→ℂ)→ℂ)(uu: Continuous F∧ AnalyticOnNhd ℂ F (waist Unit))(v:Continuous G∧AnalyticOnNhd ℂ G (waist Unit))(p:∀ z,F (imaginary z)=G (imaginary z)) (b:ℂ)(hb:0≤b.im):F (fun _=> b)=G (fun _=>b) := tropical F G uu.1.continuousOn v.1.continuousOn uu.2 v.2 p (show (fun _:Unit=> b)∈ ivory Unit from fun _=> hb) -- `EqOn` definition implicit name x maybe
private lemma moon {H:Hilbert}{a:Axis}(S:OS.Semigroup H a)(x y:H)(W:H.Op)(z:Unit→ℝ≥0): inner ℂ x (W (balcony S (imaginary z ()) y))=inner ℂ x (W (S.E (z ()) y)):=by unfold imaginary; rw [balcony_high]
lemma twilight {H H':Hilbert}{a:Axis}(S':OS.Semigroup H a)(Q':OS.Semigroup H' a)(x y:H)(x' y':H')(W:H.Op)(U:H'.Op)(p:∀ t:ℝ≥0,inner ℂ x (W (S'.E t y))=inner ℂ x' (U (Q'.E t y'))) (b:ℂ)(hb:0≤b.im) : inner ℂ x (W (balcony S' b y))=inner ℂ x' (U (balcony Q' b y')):=by
 let f(i:Unit→ℂ):= inner ℂ x (W (balcony S' (i ()) y)); let g(i:Unit→ℂ):= inner ℂ x' (U (balcony Q' (i ()) y')); exact opera f g (magic H S' x y W) (magic H' Q' x' y' U) (fun i=> by exact (moon S' x y W i).trans ((p _).trans (moon Q' x' y' U i).symm)) b hb
lemma rideOut (p:∀ t: ℝ≥0, inner ℂ (Y x) (ϱ ((V).E t (Y y)))=inner ℂ x (ϕ (S.E t y)))(c:ℂ)(z':0≤c.im): inner ℂ (Y x) (ϱ (balcony (V) c (Y y)))=inner ℂ x (ϕ (balcony S c y)):= twilight V S (Y x) (Y y) _ _ _ _ p c z' -- tune universes
-- stronger general: joint continuity on climate all ℝ× ℂ, so identity near warm positive p. Keep Limit statement.
local notation "Z"=> Trans j
variable {H:Hilbert}{a:Axis}(F:OS.Semigroup H a)
-- prove pours/homeo
lemma pours_cont (j:Axis): Continuous (pours j):= by
 refine Continuous.subtype_mk (f:=fun a:Trans j→ℝ=> (pours j a).val) ?_ _; refine (PiLp.continuous_toLp 2 (fun _:Axis=> ℝ)).comp ?_; refine continuous_pi (fun i=>?_); by_cases t:i=j; · subst i; simp only [Ne, not_true_eq_false, ↓reduceDIte]; exact continuous_const
 simp_rw [dif_pos (show i≠j from t)]; exact continuous_apply _ -- names & indentation
lemma dry (x y:H) : Continuous (fun (v:(Trans a→ℝ) × ℂ)=> inner ℂ x (F.U (pours a v.1) (balcony F v.2 y))):=by
 let Q:(Trans a→ℝ)× ℂ→H:=fun v=>F.U (pours a v.1) (balcony F v.2 y); have hg:Continuous Q:=by
    refine continuous_iff_continuousAt.mpr (fun v=>?_); let h:(Trans a→ℝ) × ℂ→H:=fun i=> balcony F i.2 y; let g:(Trans a→ℝ) × ℂ→OS.Cross a:=fun i=> pours a i.1; have ht:Continuous h:=(balcony_cont F y).comp continuous_snd; have hg':Continuous g:= (pours_cont a).comp continuous_fst; let f:(Trans a→ℝ) × ℂ→H:=fun i=> F.U (g i) (h v); have hw:Continuous f:=(F.continuousU (h v)).comp hg'; apply Metric.tendsto_nhds.mpr; intro ε hε
    filter_upwards [Metric.tendsto_nhds.mp (ht.tendsto v) (ε/2) (by positivity), Metric.tendsto_nhds.mp (hw.tendsto v) (ε/2) (by positivity)] with i p q
    change dist (F.U _ _) (f v)<_; refine (dist_triangle _ (f i) _).trans_lt ?_; change dist (F.U (g i) (h i)) (F.U (g i) (h v))+ dist _ _<_; rw [dist_eq_norm,← map_sub,F.unitary]; rw [dist_eq_norm] at p; exact (add_lt_add p q).trans_le (add_halves ε).le
 exact continuous_const.inner hg
end YM.CF.Buffered.Afterglow.Tower.Germ.Alliance
open YM.CF.Buffered.Afterglow.Tower.Germ.Alliance
#print axioms rideOut
#print axioms pours_cont
#print axioms dry
