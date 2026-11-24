import Merino.Brooch.Strand

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 24000
set_option maxHeartbeats 600000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Merino.Retinue

open Function Finset Fock Scroll Spire Sault
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Topology Classical
attribute [local instance] opCStarAlgebra
open Lattice Cube Scree Skye Sour Drapes Tulip Lat Branch Swell
open Thera Hest Levier RG Salt Mew Stax
open Dial Vow Brooch

open Window Buffered BProof StressExchange
variable {n:Side}
variable (y:Spool n)(K:Scree.Loom n)(p:BudgetPoint)(s:Sweep n)
variable (i:Axis)(c:ℝ)

/-- (130) using preJ before transport (scale real). -/
def visage : Evaluation n:=Bide.move s⁻¹ ((c:ℂ) • y.jPole K p i)

/-- alternate for credit. -/
abbrev hookeye := paneMask p y.origin true (metal (y.spin i))
def lance : phy n:= (c:ℂ) • scene0 s K (hookeye y p i)

variable {y K p} {a b d:ℝ}(t:y.Hem K p a b d)
include t
lemma plainC : Allowed (lashes s y p) (visage y K p s i c):=
 outAllowed s (allowedX ((((t.jPole i).up (Spool.fit (by simp)))).scale c))

lemma purled (Z:Orbit n):
 let e:=(c:ℂ) • hookeye y p i Z.1 (K Z)
 bra ((c:ℂ) • y.jPole K p i Z.1) e ∧ Fock.Sector (modes (y.canvas p)) false e:=by
 dsimp +zeta only
 unfold hookeye Spool.jPole flowHead paneMask
 rw [Function.comp_apply,if_pos rfl]
 by_cases g:Z.1∈pass p y.post


 · rw [Set.indicator_of_mem g,mask_eq t.skylight t.sign (t.spurt i) g Z.2]
   have pr:IsStarProjection (tickA n):=by rw [touchP]; exact cutM_idp _
   refine ⟨?_,Sector.scale ?_ _⟩
   · rw [bra,star_smul,star_smul,act_smul,act_smul,←bra_eq _ pr _ (tickB n)] 
     rfl
   rw [region]
   apply dg_lives
   intro j k e
   have l:purse (p.B/10) y.post ⊆ y.canvas p:=inside.trans (Spool.fit (by simp))
   have f:=trunk_lives (t.spurt i) (t.skylight.slot Z) _ _ e
   exact ⟨mode_in rfl (l f.1),mode_in rfl (l f.2)⟩
 rw [masked,Set.indicator_of_notMem g,preJ_nil,Set.indicator_of_notMem g]
 change bra ((c:ℂ) • (0:FC (Single n))) ((c:ℂ) • 0)∧ Fock.Sector _ _ ((c:ℂ) • 0)
 rw [smul_zero];exact ⟨rfl,.zero _⟩


lemma issuance(Z:Orbit n)(pr:Injective (priorP Z.2)):
 bra (visage y K p s i c Z.1) (lance y K p s i c Z) ∧
 Fock.Sector (modes (lashes s y p)) false (lance y K p s i c Z):=by
 let W:=behind s Z
 have he:K W=back s (K Z):=by
    obtain ⟨_,_,_,R,_⟩:=t.skylight.box
    exact R.move _ _ _ pr
 have g:lance y K p s i c Z= move s ((c:ℂ) • (hookeye y p i W.1 (K W))):=by
    have k:cSignX ((actB s).xor (actR s)) c=c:=by cases ((actB s).xor (actR s)) <;> simp [cSignX]
    rw [move,sew_scale,k,he]; rfl
 have h: visage y K p s i c Z.1 = move s ((c:ℂ) • (y.jPole K p i W.1)):=by
   change move _ ( ((c:ℂ) • y.jPole K p i) (flashA s⁻¹⁻¹ Z.1))=_
   rw [inv_inv];rfl
 have e:= purled i c t W
 rw [g,h]; exact ⟨bra_transport s e.1, moved s e.2⟩

end YM.CF.Merino.Retinue
