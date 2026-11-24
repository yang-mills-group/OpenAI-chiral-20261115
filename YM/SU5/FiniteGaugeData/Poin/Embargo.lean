import YM.SU5.FiniteGaugeData.Poin.Andine
set_option autoImplicit false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Hierarchy.Seld.Poin
open Filter Function Set Mink Mink.General Mink.Lorentz Real Flute MeasureTheory OS OS.Semigroup
open scoped Topology BigOperators NNReal
local notation "a"=>timeAxis
variable {H:Hilbert}{n:ℕ}{ι:Type}(T:Canopy H ι)(S:OS.Semigroup H timeAxis)(Ω:Bench S)(hΩ:∀ x:E4,M S x Ω.val=Ω.val)
variable (s:SO)(x:Points n)
namespace Canopy
open scoped Classical
open Complex Flute MeasureTheory Boundary Probe
variable (e:Mink.Ray)(A:Shelf S (magnet e)) (u:Fin n→ T.Chip)(g:Fin n→Test4)(k:ℕ)
-- input formula restricted to one parameter *every point x*. all meanings taken through chosen estimate, no analyt continuation across singularities for empirical Scout. charge.b=
local notation "b"=> magnet e
local notation "P"=> clockV a x
abbrev xm : Fin n→ Cross timeAxis:= fun i=> SEP a (x i)
local notation "B"=>hymns n k
local notation "H₀"=> T.senses u
local notation "mmQ"=> T.credit u
local notation "ξ" z:max=> initβ (clockV a x) (hymns n k) z
def deltaM(r:ℝ):= shape b (strumβ P (B) r) 0 (xm x)
structure PCost (V:ℕ→Points n→ℂ→ℂ):Prop where
 reads(x:Points n)(k:ℕ): ∀ᶠ r:ℝ in 𝓝 0, ProofOrder (deltaM x e k r) timeAxis (Each n) ∧ V k x r=T.Sr S Ω (deltaM x e k r) u (Each n)
 imaginary_at (x:Points n)(k:ℕ)(r:ℝ) : AnalyticAt ℂ (V k x) (imaginary r)
abbrev meters (z:ℂ):= Mell S Ω.val b A (ξ z) 0 (xm x) H₀ mmQ
include hΩ
theorem embarks : PCost T S Ω e u (fun k x=>meters T S Ω x e A u k):=by
 constructor
 · intro x k; filter_upwards [pear (clockV a x) (hymns n k) 0 0 (hymnsP n k)] with i ⟨v,u'⟩; let t:= strumβ (clockV a x) (hymns n k) i; have q: (Chronos («a»:=timeAxis) (deltaM x e k i)):=by change StrictMono (clockV _ (shape b t 0 _)); rw [Vclock]; exact v
   refine ⟨orderX _ q, ?_⟩; rw [meters,realβ, show (0:Fin n→ℂ)=soaked (0:Fin n→ℝ) from funext fun i=>by simp [soaked], ← meanR S Ω.val ..]; rfl; assumption; exact v
 · intro x k r; have hz:= (opal (clockV a x) (hymns n k) 0 r 0 (hymnsP n k)).1; have he:Radial (initβ (clockV a x) (hymns n k) (imaginary r)) 0:= (show soaked 0=(0:Fin n→ℂ) from funext fun i=>by simp [soaked]) ▸ hz; exact mellA S Ω.val b A (xm x) mmQ _ _ _ (imaginary r) he (fun i=>initA ..) (fun i=>analyticAt_const) (fun _=>analyticAt_const)
include hΩ A
-- erroneous include hΩ before embarks. chronology includes tiles.Ph.S.
theorem watches (V:ℕ→ Points n→ ℂ→ℂ)(e': PCost T S Ω e u V): V k x I= inner ℂ Ω.val (pitch S H₀ (callJ S mmQ e A k 0) x Ω.val):=by
 let W:= meters T S Ω x e A u k; have h:V k x I=W I:= starship (fun r=> e'.imaginary_at x k r) (fun r=> (embarks T S Ω hΩ e A u).imaginary_at x k r) ?_
 swap; · filter_upwards [e'.reads x k,(embarks T S Ω hΩ e A u).reads x k] with i p q; exact p.2.trans q.2.symm
 refine h.trans ?_; rw [enchas]; exact (Rilling S Ω.val hΩ H₀ mmQ e A P (B) (xm x) (hymnsP n k)).trans (by rw [show shape b P 0 (xm x)=x from PiLp.ext fun i=> poleA ..])
#print axioms watches
lemma resurgence(V:ℕ→Points n→ℂ→ℂ)(p:PCost T S Ω e u V) : (∀ i:ℕ,Integrable (fun x=> Joint.materialize n g x * V i x I)) ∧ Tendsto (fun i=> ∫ x,Joint.materialize n g x * V i x I) atTop (𝓝 (Canopy.Wval T S Ω u g)):= by
 have ht(i:ℕ)(x:Points n):= watches T S Ω hΩ x e A u i V p; simp_rw [ht]; exact ⟨fun i=> billI .., traverse S H₀ mmQ Ω g (fun i=>callJ S mmQ e A i 0) (chant S mmQ e A 0) (rlock S Ω.val hΩ)⟩
#print axioms resurgence
end Canopy
end YM.CF.Buffered.Afterglow.Hierarchy.Seld.Poin
