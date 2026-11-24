import YM.CF.BProof.Payment.Conductor
import YM.CF.BProof.Seam.Door
import YM.CF.BProof.Pods.Inverse

/- Art.H. pay Sigma reps to ballot. Body equality at Tag only Pawn+ids used. -/
set_option autoImplicit false
set_option autoImplicit false
set_option synthInstance.maxSize 26000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.BProof.West
open Function RG Wilson Lattice Filter MeasureTheory SU Grid Angular Angular.Yard Finset Prox Mapping House Release hot Gauss Weights Pricing Micro Trek
open Gates Gates.Stage Gates.Stage.Setup Contour Contour.Season Contour.Battery Contour.Tower Cube Cabinet Pods Posts Skye Seam
open scoped Topology BigOperators Classical
local notation "G"=> SU.group
variable {c:Clip}{w R v:ℝ}{S:Gates.Stage c w R v}{L:Side}{a:ℕ}{y:ℝ}{d:ℕ}{N:Side}(Y:S.Setup L a (More N) d y)(P:Entice S L a d y)(T:PathData G)(θ:ℝ)(x:Pod Y)
local notation "mH"=> Y.yard
local notation "B"=> Y.Block
local notation "g₀"=> Y.g
local notation "wB"=>House.Season mH Y.c'
local notation "gE"=>Trek.tag mH
local notation "πX"=> Cabinet.roadB Y
local notation "rawK"=> rawG Y P T θ
local notation "K_"=> Y.hall
open Hero Mark
open Spin Dream Fock Dial -- fix
set_option maxHeartbeats 260000
local notation "Ζ_"=>framesL Y P T θ
local notation "CC"=>Y.yard.long
open Rhythm Tape Hearth Lat
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator Hearth Tape Mark
attribute [local instance] opCStarAlgebra
variable {N₁ N₂:ℕ} {m m':Side}{j:ℕ} {a₁ b l r:ℝ}{D:Spin.Ready j a₁ b l r}{u:ℝ} (E:Essence D u)
variable {rₜ:ℕ} (Δ:Rhythm.Note E (Gates.gap L a) rₜ)(U: Orbit N → Pane N) (ν δ:ℝ)
variable {rB:ℕ}
variable {Y E T θ Δ U ν δ} (Z : School Y T θ E Δ U ν δ rB)
open Moment Push.AbsoluteSums
local notation "μz"=> Z.μwage
variable (k ξ:ℕ) -- near depth, and size cutoff in F support
open Branch Tenant Veil
variable {α C:ℝ}{I:Type}[Fintype I](K:Core j a₁ b l r N)
local notation "Ψ"=> Pouch Y P T θ
local notation "ψx"=>Z.world1 P K
local notation "ψ0"=>Z.world0 P K
variable (x' : Pod Y)
open Account
open Payment Garden Palot Oasis Scree
variable (B' : GramM N)
variable (o:Y.Block) (xw x'w:Pouch Y P T θ)
local notation "φf"=> Brick.Act.fields mH g₀
-- Rep hold reveal ℝ.Cap. x.p includes FrameT. Pawn≥P without dependency Fphase. Ensure `K ∧ Pose` equality.
variable (e:Cabinet.tool Y xw.val=tool Y x'w.val)(p:orbitL Y xw.val=orbitL Y x'w.val)
include e p Z
lemma sameF_ : F_' Y P T θ xw.val=F_' Y P T θ x'w.val:=Prod.ext (congrArg (Setup.area P Y T θ) e) p
omit Z
lemma sick_ : sick Y xw.val=sick Y x'w.val:=congrArg (Setup.bad Y) e
include Z
local notation "Θ"=>Z.pose P K
local notation "Lx"=>Z.clothing P
lemma life_eq : Z.clothing P xw.val= Z.clothing P x'w.val:= by
 unfold School.clothing Seam.wear;
 change Trek.actual K_ _ (Setup.area P Y T θ (tool Y xw.val)) mH (Setup.color P Y T θ (Cabinet.tool Y xw.val)) (tool Y xw.val).mood=Trek.actual K_ _ (Setup.area P Y T θ (tool Y x'w.val)) mH (Setup.color P Y T θ (Cabinet.tool Y x'w.val)) (tool Y x'w.val).mood; rw [e]

lemma here_eq : (Θ xw)=(Θ x'w):=by
 have he:= sick_ P xw x'w e p; -- syntax p unused
 let b:= Θ xw; let c:= Θ x'w; have hp:=sameF_ P Z xw x'w e p; have hu:= life_eq P Z xw x'w e p; have heq: Seam.paint Y P T θ xw.val U=Seam.paint Y P T θ x'w.val U:= congrArg U hp
 have h(i:Seat N): Z.easyMoney P xw i=Z.easyMoney P x'w i:=by
    change (Lx xw.val).HH Δ.clock g₀ (sick Y xw.val) (Seam.paint Y P T θ xw.val U) Z.p i=(Lx x'w.val).HH Δ.clock g₀ (sick Y x'w.val) (Seam.paint Y P T θ x'w.val U) Z.p i; rw [hu,heq,he] -- tune
 apply Subtype.ext; apply Prod.ext; apply Subtype.ext; exact Prod.ext (Subtype.ext heq) (congrArg (Pins mH g₀) he)

 · apply Subtype.ext; change (Z.ske P xw).val=(Z.ske P x'w).val; funext i; exact Tape.eq_draw (p:=Z.capital P xw i) (q:=Z.capital P x'w i) (h i)
lemma stund_ : Z.stun P xw.val=Z.stun P x'w.val:=by change Script.XX (Lx xw.val) _ _ (sick Y xw.val) (U (F_' Y P T θ xw.val)) Z.p= Script.XX (Lx x'w.val) _ _ (sick Y x'w.val) (U (F_' Y P T θ x'w.val)) Z.p; rw [sameF_ P Z xw x'w e p,sick_ P xw x'w e p,life_eq P Z xw x'w e p]
omit Z e p
lemma marked (p:Pawn Y.yard)(v: Along P Y T θ p) : Manual.Marked mH p.mood:= by intro i t; exact show p.mood _=_ from (by have ht:= v.2.2.1 i; rwa [if_pos t] at ht) -- tune
-- join by pivot at Front Tag. all phase v: triv Frame. Craft.Adapt 
variable (p':Pawn Y.yard)(t:Ids N)(v₀:Garden.Fields N)
abbrev reveal (p:Pawn Y.yard)(t:Ids N)(v₀:Garden.Fields N): Pod Y:= Brick.invert mH g₀ (p,t,v₀)
variable (w':Along P Y T θ p')
include w'
lemma stems_:tool Y (reveal p' t v₀)=p' ∧ orbitL Y (reveal p' t v₀)=t ∧ spores Y (reveal p' t v₀)=v₀:=by
 let p:= Brick.field_eq mH g₀ (p',t,v₀) (marked P p' w'); exact ⟨(Prod.mk.inj (show Prod.mk _ _=_ from p)).1,(Prod.mk.inj (Prod.mk.inj (show Prod.mk _ _=_ from p)).2).1,(Prod.mk.inj (Prod.mk.inj (show Prod.mk _ _=_ from p)).2).2⟩ -- tune use congrArg
lemma done_: Cabinet.Ready P Y T θ (reveal p' t v₀):= by unfold Cabinet.Ready; rw [(stems_ P p' t v₀ w').1]; exact w'
abbrev cardV : Pouch Y P T θ:= ⟨_,done_ P p' t v₀ w'⟩
end YM.CF.BProof.West
