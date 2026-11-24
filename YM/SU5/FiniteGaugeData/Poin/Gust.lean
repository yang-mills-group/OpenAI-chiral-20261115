import YM.SU5.FiniteGaugeData.Poin.Bureau
/-!
# A system of observable field multiplets. Not forcing a topology over increasing dimension. Lorentz and Eu proper spin groups; independent total arity zeroes permitted.
-/
set_option autoImplicit false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Hierarchy.Seld.Poin
open Filter Function Set OS OS.Semigroup Mink Mink.General Mink.Lorentz Complex Flute MeasureTheory Boundary Probe
open scoped Topology ContDiff NNReal InnerProductSpace
local notation "tt"=>timeAxis
abbrev colorP (d:ℕ):= EuclideanSpace ℂ (Fin d) -- color of label, not gauge
abbrev paintP (d:ℕ):= colorP d→L[ℂ]colorP d
structure Pattern where
 amount : ℕ
 charge : ℕ
 dual : colorP amount →SL[starRingEnd ℂ] colorP amount
 invol : Involutive dual
 E : SO→* paintP amount
 L : Mink.Lorentz →* paintP amount
 Ec : Continuous E
 Lc : Continuous L
 pin p (q:Pin p) : L p=E (polar p q)
 link (_:Mink.Ray) : ℂ → paintP amount
 ink (e:Mink.Ray) (z:ℂ) : AnalyticAt ℂ (link e) z
 base (e:Mink.Ray)(x:ℝ): E (moveB e x)= link e (x:ℂ)
 journey (e:Mink.Ray)(x:ℝ): L (e.boost x)= link e (imaginary x)
 shared (p:Mink.Lorentz) (x:colorP amount) : dual (L p x)= L p (dual x)
structure Canopy (H:Hilbert)(α:Type) where
 P : α→ Pattern
 flash (w:α): colorP (P w).amount →L[ℂ] H.Op
 duplex (w:α)(x:colorP (P w).amount) : flash w ((P w).dual x) = star (flash w x)
variable {H:Hilbert}{α:Type}(M':Canopy H α)(S: OS.Semigroup H timeAxis)(Ω:Bench S)(hΩ:∀ z:E4,M S z Ω.val=Ω.val)
namespace Canopy
abbrev Chip := Sigma (fun i:α=>colorP (M'.P i).amount)
abbrev Token := M'.Chip × Test4
abbrev grade (w:M'.Chip) := (M'.P w.fst).charge
def dep (w:M'.Chip):= M'.flash w.fst w.snd
def mirrorK (w:M'.Chip): M'.Chip:= ⟨w.fst, (M'.P w.fst).dual w.snd⟩
def βL (p:Mink.Lorentz)(w:M'.Chip): M'.Chip := ⟨w.fst,(M'.P w.fst).L p w.snd⟩
def βE (p:SO)(w:M'.Chip): M'.Chip:= ⟨w.fst,(M'.P w.fst).E p w.snd⟩
variable {n:ℕ}
@[simp] lemma Lmult (p q:Lorentz)(w:M'.Chip): M'.βL p (M'.βL q w)= M'.βL (p*q) w:=by unfold βL; simp only [map_mul]; rfl
@[simp] lemma Lini (w:M'.Chip): M'.βL 1 w=w:=by unfold βL; rw [map_one]; rfl
@[simp] lemma Emult (p q:SO)(w:M'.Chip): M'.βE p (M'.βE q w)=M'.βE (p*q) w:=by unfold βE; simp only [map_mul]; rfl
@[simp] lemma Eini (w:M'.Chip): M'.βE 1 w=w:=by unfold βE; rw [map_one]; rfl
lemma spar (w:M'.Chip): M'.dep (M'.mirrorK w)=star (M'.dep w):= Canopy.duplex M' ..
lemma Lowns (w:M'.Chip)(p:Lorentz): M'.mirrorK (M'.βL p w)= M'.βL p (M'.mirrorK w):=by cases w; unfold mirrorK βL; simp [(M'.P _).shared]
lemma Lduo(w:M'.Chip): M'.mirrorK (M'.mirrorK w)=w:=by cases w; exact congrArg (Sigma.mk _) ((M'.P _).invol _)
-- Eu estimate class needed for Lorentz motion n-point
abbrev stampL(p:Lorentz)(w:Fin n→ M'.Chip) := fun i=> M'.βL p (w i)
abbrev stampE(p:SO)(w:Fin n→ M'.Chip) := fun i=> M'.βE p (w i)
variable (p: Mink.Poincare) (w:Fin n→ M'.Chip)(P:Lorentz)
abbrev senses := M'.dep ∘ w
abbrev credit := M'.grade ∘ w
structure Warrant :Prop where
 supports(n:ℕ)(w:Fin n→ M'.Chip)(p:SO): Pavilion S Ω.val (M'.senses w) (M'.senses (M'.stampE p w)) (M'.credit w) p.val
local notation "B"=> Bench S
local notation "E"=> Mink.Poincare
variable (g:Fin n→Test4) (HX:Warrant M' S Ω)
local notation "A"=>M'.senses w
local notation "ν"=>M'.credit w
def Wval := WaveC S Ω (M'.senses w) (M'.credit w) g
local notation "★"=> M'.Wval S Ω
local notation "V"=> M'.stampL
include HX hΩ
lemma stationary (p:Pin P)(e:Mink.Ray)(A₀:Shelf S (magnet e)): Wval M' S Ω w g=★ (V P w) (active (Poincare.motion P) g):= by
 apply roomVal S Ω hΩ _ _ _ _ A₀ P g p; exact ((show M'.stampL P w=M'.stampE (polar P p) w from funext fun i=> congrArg (Sigma.mk (w i).fst) (DFunLike.congr_fun ((M'.P (w i).fst).pin P p) _)) ▸ HX.supports n w _)
lemma Mill(e:Mink.Ray)(A₀:Shelf S (magnet e))(r:ℝ): Wval M' S Ω w g= ★ (V (e.boost r) w) (active (Poincare.motion (e.boost r)) g):= by
 let F(z:ℂ)(i:Fin n):= let v:= w i; M'.flash v.fst ((M'.P v.fst).link e z v.snd); have he(t:ℝ):M'.senses (M'.stampE (moveB e t) w)= F t:=funext fun i=> by
    change M'.flash _ ((M'.P (w i).fst).E (moveB e t) _) =_; rw [(M'.P _).base]
 apply session S Ω hΩ A _ ν e A₀ g r F _ (fun x=> he x ▸ HX.supports n w (moveB e x)) (funext fun i=> by change M'.flash _ _=M'.flash ((w i).fst) ((M'.P (w i).fst).L (e.boost r) (w i).snd); rw [(M'.P _).journey])
 intro i x; let v:=w i; let p:= M'.P v.fst; let J:= ContinuousLinearMap.apply ℂ (colorP p.amount) v.snd; exact (M'.flash v.fst).analyticAt _|>.comp (J.analyticAt _|>.comp (p.ink e x))
#print axioms stationary
#print axioms Mill
omit HX hΩ in
lemma tailor (p q:Mink.Poincare): active p (active q g)=active (p*q) g:=by
 funext i; ext1 x; change Joint.push p (Joint.push q (g i)) x=Joint.push (p*q) (g i) x; rw [Joint.push_at,Joint.push_at,Joint.push_at,mul_inv_rev,Poincare.sends_mul]
theorem drumm (e:∀ b:Mink.Ray,Shelf S (magnet b)): Wval M' S Ω w g= ★ (V P w) (active (Poincare.motion P) g):=by
 obtain ⟨x,t,U,u,rfl⟩:= nilBoost P; let p:=x.boost t; let q:=Poincare.motion U; refine Eq.trans ((stationary M' S Ω hΩ w U g HX u x (e x))) ((Mill M' S Ω hΩ (V U w) (active q g) HX x (e x) t).trans ?_); rw [tailor, ← Poincare.overL, show M'.stampL p (M'.stampL U w)=M'.stampL (p*U) w from funext fun i=> Lmult M' _ _ _]
#print axioms drumm
end Canopy
end YM.CF.Buffered.Afterglow.Hierarchy.Seld.Poin
