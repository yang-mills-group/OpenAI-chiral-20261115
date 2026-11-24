import YM.SU5.Exchange.Reg.Lift
import YM.CF.Vp929.Match.Rays
import YM.CF.Vp929.Pre.Azure
/-! Spend the higher exponent on the same Shop's rollT components as in
 incXG, and on the transported parts of the pre_E obligation. Following XXI.
 A change of rate in the *mass paid*, not in any input. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
noncomputable section
namespace YM.CF.Sour
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open Skye Scree Cadre Palot
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
open Cube Lat Tulip Fock Rush Scroll Paige Vault Phase Acorn Spire
open Pastry Vow Rue
attribute [local instance] opCStarAlgebra
variable {n:Side}
local notation "SA"=> Seat n
local notation "VX"=> Aura n
local notation "Hk"=> hook SA
open Hake Jet Sault Stax
attribute [local instance] loreM loreN
variable {P:BudgetPoint}{X Y Z:Aura n}{V W:Firing n}{D:Support (More n)}
open Branch Tenant Drapes Rill Sault
attribute [local instance] Rill.boreKSpace Rill.boreXN
local notation "JS"=> Single n
local notation "SO"=> Support (More n)
local notation "Γ"=> (FC (Dwell n))
namespace Glyph
variable {δ a b u e W:ℝ}{μ:Toll (Single n)}{S:Support (More n)}
variable (F:Raw (Openc (More n) δ) (Single n)){q:ℕ}{K:Scree.Loom n}(p:Roof n a δ q K)(g:0<δ)(t: Suite (badge _) (bail n δ) (bail n δ) S μ F)
variable {H:Op (Single n)→FC (Dwell n)}{Z':Single n→ Single n→ FC (Dwell n)}{h:ℝ}(f: Glyph H Z' h)
variable (T:Scree.Hub n)(z:T.val.1∈ S)(x:S∈αW P.B (Bake.lagE T))
open Ione Bake Nor Larch Levier Salt
local notation "Hz"=>Scree.Hub n
variable {κ:Type}[TopologicalSpace κ][Nonempty κ]
variable (w:Sweep n)(M:Elm n κ δ e u)
local notation "R"=> Salt.actY w
local notation "W'"=> moveHub w
local notation "GZ"=> panel P
local notation "Λ"=> Ione.suit_Y w
local notation "Δ"=> sauce w.charge (detX w.s) (Sour.γS w)
variable (i:κ)
variable {e' a' b' :ℝ}(v:P.threshold ≤ a)(bq:q+10 ≤ P.B)(hk:cipherK q ≤ 5*P.B)(uB:3≤P.B)(p0:HopeT δ e' a' P.order)(t0:P.threshold ≤ a')(h0:1≤h)
local notation "Xq"=> fondC p g M H P i
include v p g bq hk uB p0 t0 h0 f
variable {K':Bool}(c:∀ S:Sweep n,leafJ S K' M M)(c0:∀ s:Sweep n,∀ x:Op (Single n),sauce s.charge (detX s.s) (Sour.γS s) (H x)=H (realR s K' x))
include c c0
lemma scopeInc {A:ℝ} (s : ∀ o:SA,(∑ T:Hz,if T.val.1=o then (raiseRate P).mass T.val.2 (@écu _ (raiseRate P) h M.W T) else 0) ≤ A) : IncX Utrue Xq (raiseRate P) h A:=
 ⟨⟨_,fun T=> raisePress P (essay p g f T M i v bq hk uB p0 t0 h0),fun i => (by
    have hEq (T:Hz) : (T.val.1=i) = (i=T.val.1) := propext eq_comm
    specialize s i
    simp_rw [hEq] at s
    exact s)⟩,fun s k U u T V=> (tag_e p g f T M i v bq hk uB p0 t0 h0 c c0 s V).trans (Ione.tama s U u _).symm⟩
end Glyph
end YM.CF.Sour

namespace YM.CF.Sour
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open Skye Scree Cadre Palot
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
open Cube Lat Tulip Fock Rush Scroll Paige Vault Phase Acorn Spire
open Pastry Vow Rue
attribute [local instance] opCStarAlgebra
variable {n:Side}
local notation "SA"=> Seat n
local notation "VX"=> Aura n
local notation "Hk"=> hook SA
open Hake Jet Sault Stax
attribute [local instance] loreM loreN
variable {P:BudgetPoint}{X Y Z:Aura n}{V W:Firing n}{D:Support (More n)}
open Branch Tenant Drapes Rill Sault
attribute [local instance] Rill.boreKSpace Rill.boreXN
local notation "JS"=> Single n
local notation "SO"=> Support (More n)
local notation "Γ"=> (FC (Dwell n))
open Exa Tap Dial
variable {κ:Type}[TopologicalSpace κ][Nonempty κ]
variable {N:Side} (T S:BeatL N)(E:χL N κ)
local notation "Sta"=> fC N S E
local notation "Bel"=> κR N E
local notation "Q"=> tickA N
local notation "Lx"=> Firing N
namespace BondL
variable {a b c d e s:ℝ}{T S E}(A: BondL T S E b c a d){p:BudgetPoint}{L:Scree.Loom N}{q:ℕ}{t:ℝ}(g:Roof N t d q L)(h:0<d)(W:ℝ)(w0:1 ≤ W)
variable (s_:Sweep N)(V:Orbit N)(i:κ)(Z:Aura N)(pF:Injective (priorP V.2))
open Levier Salt Ione
local notation "Λ"=> sauce s_.charge (detX s_.s) (γS s_)
local notation "OA"=> σX p Z ∅
local notation "WZ"=> yellA s_ V
local notation "Px"=> p.B
local notation "Sg"=> Support (More N)
local notation "Ut"=> (moldA s_ Z)
open Cadre Wray Larch Ione
variable {H p0:ℝ}{I: Aura N→ Support (More N)→ ℝ}(F:Vow.Cusp N)
variable {z0 z1:ℝ}(k: HopeT d z0 z1 p.order)(hv:p.threshold ≤ z1)(y:p.threshold ≤ t)(hx:q+10 ≤ p.B)(v:cipherK q ≤5*p.B)(w:3≤p.B)
variable (f:∀ X:Aura N,∀ D⊆X.val,Fray p W (cipherK q) X D (F X D) (I X D))(r:Bake.Turf (fun X=>F X ∅))
variable (pS: ∀ s:Sweep N,∀ i:Aura N,∀ V:Orbit N,Injective (priorP V.2)→∀ D⊆i.val,F (moldA s i) (actY s D) (yellA s V)=suit_Y s (F i D V))
local notation "τx"=> A.bead W p
local notation "L'"=> (fun i:κ=> litB A g h W w0 k hv y hx v w i)
open Stax Glyph
local notation "Θi"=> (L' i)
local notation "B'"=> Λ
local notation "K'"=> Bias.payX Θi
open Ione
variable {κ':ℝ}(uA:Sour.pureB A κ') (T0:Finset (Scree.Hub N))(Y0:∀ T:Scree.Hub N,coverNumber p.B T.val.2 ≤ 1→T∈T0)
local notation "μs"=> A.lineH (p:=p) g h i
local notation "Yb"=> A.floatH (p:=p) g h i
local notation "Kα"=> A.scarf (p:=p) g h i
local notation "Ωa"=> A.seekB (p:=p) g h i
include w0 k hv y hx v w

variable (he:0 < a)(fα:2*(raiseRate p).supportExponent*Fief.tileN 1 ≤ a/2*p.B)(e': a ≤1)
--abbrev øK (z_:ℝ):=Tenant.quota^2* (wingRent (Fir.Aop-(1/2:ℂ) • 1) 1*z_)
include uA he fα
lemma starInc : IncX Utrue μs (raiseRate p) W (cap1 (raiseRate p) (øK κ') W):= scopeInc g h (pal_v W w0) A.ela i y hx v w k hv w0 (fun i=>(A.sQ i).1) (fun s x=>arm ..) (payWorth (P:=raiseRate p) A.ela uA.1 fα he uA.2)
omit uA
include e'
lemma payInc : IncX Utrue Yb (raiseRate p) W (cap2 (raiseRate p) c W a):=scopeInc g h (pal_v W w0) A.elt i y hx v w k hv w0 (fun i=>(A.sQ i).2.1) (fun s x=>arm ..) (payW (P:=raiseRate p) A.elt A.elt.bank fα he e')
lemma payZInc : IncX Utrue Kα (raiseRate p) W (cap2 (raiseRate p) b 1 a) :=by
 have ht:IncX Utrue Kα (raiseRate p) 1 (cap2 (raiseRate p) b 1 a):=scopeInc g h (oreV 1 le_rfl _) A.coreS i y hx v w k hv le_rfl (fun i=>(A.sQ i).2.2.1) (fun s x=>tiltH ..) (payW (P:=raiseRate p) A.coreS A.coreS.bank fα he e')
 obtain ⟨x,K⟩:=ht; obtain ⟨v₁,f,v'⟩:=x; exact ⟨⟨v₁,fun X=> pose_k X _ W (f X) (Glyph.dust g h X A.coreS i y hx v w k hv), v'⟩,K⟩
end BondL
end YM.CF.Sour
