import YM.CF.BProof.Start.Camera
set_option autoImplicit false
set_option synthInstance.maxSize 26000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.BProof.Start
open Function Filter MeasureTheory Finset
open Lattice Tenant Lat Cube Skye RG Angular Wilson Rhythm Hero Mark Branch
open scoped Topology BigOperators Classical
open Gates Gates.Stage Gates.Stage.Setup Mapping House
open Stint Tape Hearth Prime Estate Cliff
open Jet Paige Drapes Vault Oasis Bias Weights Cabinet Mint Contour
variable {N:Side}{d K:ℕ}{c:Clip}{w R v:ℝ}(S:Gates.Stage c w R v)
variable {m m' L B:Side}{j:ℕ}{a b l r:ℝ}{D:Spin.Ready j a b l r}{u:ℝ}(E:Essence D u)
variable {rₜ a':ℕ}(Δ: Rhythm.Note E (gap L a') rₜ)
variable {p:Odd L.val} {Y:Pricing j L p (Vault.Thread j)} {δ:ℝ}{F:Grasp Y B δ}
variable {E Δ S}{U H:ℝ} (J:Mote S E Δ F U H)
open Veil Anthem
open Spin Seam Payment
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator Hearth Tape Mark
attribute [local instance] opCStarAlgebra
open Scree Scope
local notation "N_" => mid m B
namespace Mote
-- general V, Γ clip and trajectory preClip, eliminator. `p : d₀.funds = c`
variable {B':ℝ→ℕ}{Fp:ℝ→ℝ}{W:ℕ}{y h ν:ℝ} (Γ: J.Licence B' Fp W y h)(V:Setup S L a' (More (mid m B)) W y)(U₀:Loom (mid m B))
variable (d₀:GramM (mid m B))(Y':Spire.Pearl F)
def Design0 (ν:ℝ)(p:d₀.funds=c)(Q:Score V.yard (Manus.Poles (mid m B))) : Prop:= by subst c; exact Show J Γ V U₀ (ν:=ν) Y' Q
-- admissible geometry hypothesis summarized: no Lean witness of s-level periods beyond V. Returns any V.Canvas given License. 
structure Client(d₀:GramM (mid m B))(U₀:Loom (mid m B))(ν:ℝ):Prop where
 mask : d₀.p.threshold=thresh y
 clip_eq : d₀.funds=c
 small : thresh y≤ν
 limit : Roof (mid m B) ν δ rₜ U₀
 betas : y≤2*d₀.beta ∧ d₀.beta≤2*y
 loft : d₀.path.Bounds c w R v
 height : d₀.J.P.toll a b l r
 light : Paint m B d₀.J.I U H
 cargo : Nonempty (Cargo d₀ h (Fp y))
 epoch : F.roundZ≤ (mid m B).val
 B_budget : d₀.p.B=B' y
 support : d₀.p.supportExponent=1
 given : Scene.Output.Warp F (U:=U₀) (d₀:=d₀)
-- need parameter J not implicitly tied? Client uses nvars deduced via U etc, not S E Δ Y? add explicit
variable {Q0:Score V.yard (Manus.Poles (mid m B))}
def Built : Prop:=∃ p:d₀.funds=c,Design0 J Γ V U₀ d₀ Y' ν p Q0
variable (P:J.Extent y W (mid m B))
include P -- extent
-- purchased schedule support norm. no T.h* dependence
structure Yield (p:Score V.yard (Manus.Poles (mid m B))) : Prop where
 mark : ∀ i: V.yard.Index, Allowed (V.yard.band i) (p.slot i) ∧ Paid (p.slot i) (Real.exp (kA y*((More (mid m B)).val:ℝ)^3))
 output : Real.exp (-(kA y)*(((More (mid m B)).val:ℝ)^4)) ≤ ‖numerator d₀ F U₀ p.test‖
-- Need applicability Buy params string; use abbrev using J Γ
omit P in
abbrev BuyP (Γ: J.Licence B' Fp W y h) := Client (a:=a) (b:=b) (l:=l) (r:=r) (w:=w) (R:=R) (v:=v) (c:=c) (U:=U) (H:=H) (h:=h) (F:=F) (rₜ:=rₜ) (y:=y) (B':=B') (Fp:=Fp) d₀ U₀ ν
variable (X: BuyP (J:=J) (Γ:=Γ) U₀ d₀ (ν:=ν)) -- tune order
include X
lemma bought (v:u ≤ Y'.q)(hf: Stamped j L p Y)(hK:1≤j)(ma:0≤δ)(p':δ≤ E.pre.limit)(d':δ≤ E.H.calm):
    ∃ Q: Score V.yard (Manus.Poles (mid m B)), Built (Q0:=Q) J Γ V U₀ d₀ Y' (ν:=ν) ∧ Yield (F:=F) V U₀ d₀ Q := by
 have hx:=X.clip_eq; subst c
 obtain ⟨r,q⟩:= chosen J Γ V U₀ P Y' p' d' ma X.loft X.small X.limit X.height X.mask X.light X.cargo hK hf X.epoch X.B_budget X.support X.betas.1 X.betas.2
 refine ⟨r,⟨rfl,q⟩,?_⟩
 obtain ⟨Z,t,T,v,H,J0,m,b,rfl⟩:=q
 exact ⟨fun i=> Show.marks J Γ V U₀ P Y' Z t T v H J0 b ‹u≤Y'.q› X.B_budget X.support X.betas.1 X.betas.2 X.given i, Show.result J Γ V U₀ P Y' Z t T v H J0 b ‹u≤Y'.q› X.B_budget X.support X.betas.1 X.betas.2 X.given⟩
end Mote
end YM.CF.BProof.Start
#print axioms YM.CF.BProof.Start.Mote.bought
