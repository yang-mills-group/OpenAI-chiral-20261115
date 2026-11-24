import YM.SU5.FiniteGaugeData.Poin.Floor
/-!
# W covariance COMP of pure motions. Pure Lorentz from strict real-coordinate estimates at point fields!

 Use on same ℋ & analytic Shelf. Includes boosts (full ANY real) about any e. Infinitesimal allowance.NONE.
-/
set_option autoImplicit false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Hierarchy.Seld.Poin
open Filter Function Set OS OS.Semigroup Mink Mink.General Mink.Lorentz Complex Flute MeasureTheory Boundary Probe
open scoped Topology ContDiff NNReal InnerProductSpace
variable {H:Hilbert}{n:ℕ}(S: OS.Semigroup H timeAxis)(Ω:Bench S)(p:∀ x:E4, M S x Ω.val=Ω.val)
variable (G F:Fin n→ H.Op)(ν:Fin n→ℕ)(T:General)(e:Mink.Ray)
local notation "a"=>timeAxis
local notation "b"=>magnet e
variable (A:Shelf S (magnet e))(L:Mink.Lorentz)
-- full W positions real p arguments. $Up Λ push forward`。
abbrev shiftK (P:Mink.Poincare)(f:Test4):Test4:= Joint.push P f
abbrev active (P:Mink.Poincare)(f:Fin n→Test4) := fun i=> shiftK P (f i)
local notation "p₀" g:max=> Poincare.motion g
variable (g:Fin n→Test4)(s:ℕ)(x:Points n)
def WaveC :ℂ:= inner ℂ Ω.val (Rail (panels S G ν g) (Omit S) Ω).val
private lemma mp : MeasurePreserving (Mink.Poincare.togetherL L n) volume volume:= by
 let p:=p₀ L; have he:(Mink.Poincare.togetherL L n : Points n→ Points n)= Poincare.zusammen p n:=funext fun x=> PiLp.ext fun i=> by simp [Poincare.zusammen,p]
 rw [he]; exact Poincare.together p n
abbrev lmove (L:Lorentz) (x:Points n):= turnO L.val x
lemma mn(x:Points n): Mink.Poincare.togetherL L n x = turnO L.val x:=rfl
lemma diagrams : Joint.materialize n (active (p₀ L) g) (lmove L x) = Joint.materialize n g x := by
 rw [Joint.material_at,Joint.material_at]; congr 1; ext1 i; change Joint.push (p₀ L) (g i) _= _; rw [Joint.push_at,show (lmove L x i)= Poincare.sends (p₀ L) (x i) from (Poincare.as_active ..).symm,Poincare.unmade]
variable (X X':Bin n H.Op)
lemma stint (p: ∀ x:Points n,inner ℂ Ω.val (pitch S G X x Ω.val)=inner ℂ Ω.val (pitch S F X' (lmove L x) Ω.val)): (∫ x:Points n, concert S Ω.val Ω.val G X g x) = ∫ x:Points n, concert S Ω.val Ω.val F X' (active (p₀ L) g) x :=by
 let f(x:Points n):= concert S Ω.val Ω.val F X' (active (p₀ L) g) x; refine Eq.trans ?_ ((mp (n:=n) L).integral_comp (Mink.Poincare.togetherL L n).toHomeomorph.toMeasurableEquiv.measurableEmbedding f); apply integral_congr_ae; filter_upwards with x; unfold f concert; rw [p,← diagrams L g x]; rfl
lemma transport (p:saucer S Ω.val=Ω.val)(U V:ℕ→ Bin n H.Op)(e:Solution S ν U)(H:Solution S ν V)(t:∀ i:ℕ,∀ x:Points n, inner ℂ Ω.val (pitch S G (U i) x Ω.val)= inner ℂ Ω.val (pitch S F (V i) (lmove L x) Ω.val)): WaveC S Ω G ν g=WaveC S Ω F ν (active (p₀ L) g):= tendsto_nhds_unique_of_eventuallyEq (traverse S G ν Ω g U e p) (traverse S F ν Ω (active (p₀ L) g) V H p) (Eventually.of_forall fun i=> stint S Ω G F L g _ _ (t i))
def hymns(n:ℕ)(t:ℕ): Fin n→ℝ:= fun i=> ↑(squirt t)*(i.val:ℝ)
lemma hymnsP(n s:ℕ): StrictMono (hymns n s):= fun i j h=> mul_lt_mul_of_pos_left (show (i.val:ℝ)< (j.val:ℝ) from Nat.cast_lt.mpr h) (show (0:ℝ)< (squirt s:ℝ) from squirtP s)
lemma hymnsL(n:ℕ)(i:Fin n): Tendsto (fun s=>hymns n s i) atTop (𝓝 0):= by unfold hymns; simpa only [Function.comp_def,NNReal.coe_zero,zero_mul] using (NNReal.continuous_coe.continuousAt.tendsto.comp squirtL).mul_const (i.val:ℝ)
def callJ (e:Mink.Ray)(A:Shelf S (magnet e)) (s:ℕ) (r:ℝ): Bin n H.Op := rise S (magnet e) A (θδ r (hymns n s)) (ηδ r (hymns n s)) ν
lemma chant(r:ℝ) : Solution S ν (fun s=> callJ S ν e A s r):= by
 apply rise_g
 · exact fun i=> char r n _ (hymnsP n i)
 · intro i; simpa only [Function.comp_def,θδ,soaked,mul_zero,ofReal_zero] using (continuous_ofReal.continuousAt.tendsto (x:=Real.cosh r*0)).comp ((hymnsL n i).const_mul (Real.cosh r)) -- composition simpl
 · intro i; simpa only [Function.comp_def,ηδ, ofReal_zero, zero_mul, mul_zero] using (((continuous_ofReal.continuousAt.tendsto.comp (hymnsL n i)).const_mul (Real.sinh r:ℂ)).mul_const I)
lemma enchas : callJ S ν e A s 0= rise S (magnet e) A (soaked (hymns n s)) 0 ν:=by
 unfold callJ; congr 1
 · funext i; simp [θδ,soaked]
 funext i; simp [ηδ]
include p A
lemma session (r:ℝ) (V:ℂ→Fin n→ H.Op)(J:∀ i:Fin n,∀ x:ℂ,AnalyticAt ℂ (fun y=> V y i) x)(H':∀ x:ℝ, Pavilion S Ω.val G (V x) ν (moveB e x).val)(hv: V (imaginary r)=F): WaveC S Ω G ν g = WaveC S Ω F ν (active (p₀ (e.boost r)) g):= by
 apply transport S Ω G F ν (e.boost r) g (rlock S Ω.val p) _ _ (chant S ν e A 0) (chant S ν e A r); intro i x; rw [enchas]; exact castleT S Ω.val p G F ν e A (hymns n i) r x V J H' hv (hymnsP n i)
lemma roomVal (t:Pin L)(P:Pavilion S Ω.val G F ν (polar L t).val): WaveC S Ω G ν g = WaveC S Ω F ν (active (p₀ L) g):= by
 apply transport S Ω G F ν L g (rlock S Ω.val p) _ _ (chant S ν e A 0) (chant S ν e A 0); intro i x; rw [enchas]; exact digs S Ω.val p G F ν e A _ x (hymnsP n i) L t P
#print axioms session
#print axioms roomVal
end YM.CF.Buffered.Afterglow.Hierarchy.Seld.Poin
