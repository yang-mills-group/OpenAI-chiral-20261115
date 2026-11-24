import YM.SU5.FiniteGaugeData.Poin.Sue
/-!
# A REAL-price estimate (sphere placements) on these strict Chronos. For boost family
 For all European turns and points paying AFTER and before change (point labels).

 Head readability without requiring registered-spin specifics.
-/
set_option autoImplicit false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Hierarchy.Seld.Poin
open Filter Function Set OS OS.Semigroup Mink Mink.General Mink.Lorentz Complex Flute
open scoped Topology ContDiff NNReal InnerProductSpace
variable {H:Hilbert}{n:ℕ}(S: OS.Semigroup H timeAxis)(Ω:H)(p:∀ x:E4, M S x Ω=Ω)
variable (G F:Fin n→ H.Op)(ν:Fin n→ℕ)(T:General)(e:Mink.Ray)
abbrev turnO (T:General) (x:Points n):Points n:= points fun i=>walk T (x i)
local notation "a"=>timeAxis
local notation "X"=>Cross timeAxis
abbrev Paint (x:Points n):Prop:= TopG S Ω G ν x=TopG S Ω F ν (turnO T x)
structure Pavilion :Prop where
 share (x:Points n) (p: Chronos («a»:=timeAxis) x)(k:Chronos («a»:=timeAxis) (turnO T x)): Paint S Ω G F ν T x
variable (A:Shelf S (magnet e))(t s y:Fin n→ℝ)(Y:Fin n→Cross timeAxis)(eY:∀ i,inner ℝ (Y i) (magnet e)=0)(r:ℝ)(x:Points n)
variable (V:ℂ→Fin n→ H.Op) (J:∀ i:Fin n,∀ x:ℂ,AnalyticAt ℂ (fun y=> V y i) x)
variable (H':∀ x:ℝ, Pavilion S Ω G (V x) ν (moveB e x).val)(hv: V (imaginary r)=F)(h:StrictMono s)
include eY
local notation "b"=> magnet e
lemma s_line : turnO (moveB e r).val (shape (magnet e) t y Y) = shape (magnet e) (fun i=> useu r (t i) (y i)) (fun i=> user_ r (t i) (y i)) Y := PiLp.ext fun i=> alto e (t i) (y i) r (Y i) (eY i)
lemma track : turnO (e.boost r).val (shape (magnet e) t y Y) = shape (magnet e) (tβ t y r) (sβ t y r) Y := PiLp.ext fun i=> trip e (t i) (y i) r (Y i) (eY i)
omit eY
lemma ceremony (L: Mink.Lorentz): turnO L.val x = Mink.Poincare.zusammen (Mink.Poincare.motion L) n x:= PiLp.ext fun i=> by change L.act (x i)= (Poincare.sends (Poincare.motion L) (x i)); rw [Poincare.as_active]
local notation "C"=>magnet e -- C(
local notation "Q"=> Mell S Ω (magnet e) A
local notation "E₀"=>initβ t s
local notation "E₁"=>bτ t s y r
local notation "E₂"=>bχ t s y r
include p h eY J H'
lemma art : Mell S Ω (magnet e) A (initβ t s (imaginary 1)) (soaked y) Y G ν = Q (E₁ I) (E₂ I) Y (V (imaginary r)) ν:=by
 let Z(z:ℂ):= Q (E₀ z) (soaked y) Y G ν; let Mx(z:ℂ):=Q (E₁ z) (E₂ z) Y (V (angles r z)) ν
 have he (z:ℝ):= opal t s y z r h -- check order
 have hh:Z I=Mx I:= starship (fun z=>mellA S Ω b A Y ν E₀ (fun _=>soaked y) (fun _=>G) (imaginary z) (he z).1 (fun i=>initA ..) (fun _=>analyticAt_const) (fun _=>analyticAt_const))
     (fun z=>mellA S Ω b A Y ν E₁ E₂ (fun z=>V (angles r z)) (imaginary z) (he z).2 (fun i=>(jets t s y r (imaginary z) i).1) (fun i=>(jets t s y r (imaginary z) i).2) (fun i=> (J i (angles r (imaginary z))).comp (angA r (imaginary z)))) (?_)
 swap; · filter_upwards [pear t s y r h] with i ⟨v,k⟩; unfold Z Mx; rw [thetaτ,thetaχ,realβ]; let r':= r*i; let f:= moveB e r'; let u:= V (↑r':ℂ); let M:Points n:= shape (magnet e) (strumβ t s i) y Y; let R:= shape (magnet e) (lτ t s y r i) (lχ t s y r i) Y
         have p': angles r ↑i=(↑r':ℂ):=by unfold angles r'; push_cast; rfl
         rw [p', ← meanR S Ω b A Y G ν _ y p v, ← meanR S Ω b A Y u ν _ _ p k]; have hw: turnO f.val M=R:= s_line e _ y Y eY r' -- tune s_line order
         rw [← show turnO f.val M = (shape (magnet e) (lτ t s y r i) (lχ t s y r i) Y) from hw ]; apply (H' r').share M; change StrictMono (clockV a (shape b (strumβ t s i) y Y)); rw [Vclock]; exact v; change StrictMono (clockV a (turnO f.val M)); rw [hw]; unfold R; rw [Vclock]; exact k
 rw [show imaginary 1=I from by simp [imaginary]]; exact hh
local notation "R₀"=>rise S (magnet e) A (soaked s) 0 ν
local notation "R₁"=>rise S (magnet e) A (θδ r s) (ηδ r s) ν
local notation "Π₀"=>shape (magnet e) t y Y
include hv
lemma chevalL : inner ℂ Ω (pitch S G (R₀) (Π₀) Ω)= inner ℂ Ω (pitch S F (R₁) (turnO (e.boost r).val (Π₀)) Ω):=by
 let A':=art S Ω p G ν e A t s y Y eY r V J H' h; have he: ∀ r:ℝ, StrictMono s → Radial (soaked s) (0:Fin n→ℂ):= fun _ g=>by rw [show (0:Fin n→ℂ)=soaked (0:Fin n→ℝ) from funext fun i=>by simp [soaked]]; apply (wet _ _).mpr g
 rw [init_n,←show imaginary 1=I from by simp [imaginary], hv,uβ,vβ, one_smul, mul_one] at A'; rw [← show spur (0:Fin n→ℂ) y= soaked y from (funext (fun i=>by simp [spur,soaked])), stunts _ _ _ _ _ 0 _ _ _ _ _ p (he 0 h), stunts _ _ _ _ _ _ _ _ _ _ _ p (char r n s h)] at A' -- possible rewriting I inside β. tune
 rw [track e t y Y eY r]; exact A'
#print axioms art
#print axioms chevalL
-- Bounded kernels.Shift no freight.Core.
omit eY
lemma castleT : inner ℂ Ω (pitch S G R₀ x Ω)= inner ℂ Ω (pitch S F R₁ (turnO (e.boost r).val x) Ω) := by
 let t(i):= time (x i); let y(i):=Ray.along e (x i); let f(i):= fsp e (x i); suffices he: shape (magnet e) t y f=x by simpa only [he] using chevalL S Ω p G F ν e A t s y f (fun i=> nez e (x i)) r V J H' hv h
 exact PiLp.ext (fun i=>attend e (x i)) -- argument order Flute.nez etc? Flute vars e x; open.
#print axioms castleT
end YM.CF.Buffered.Afterglow.Hierarchy.Seld.Poin
