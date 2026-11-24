import YM.CF.BProof.Canopy.Axles
import Mathlib.Topology.MetricSpace.Contracting
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 800000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Sour.Digit
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
variable {P:BudgetPoint}{X Z:Aura n}{V W:Firing n}{D:Support (More n)}
open Branch Tenant Drapes Rill Sault
attribute [local instance] Rill.boreKSpace Rill.boreXN
local notation "JS"=> Single n
local notation "SO"=> Support (More n)
local notation "Γ"=> (FC (Dwell n))
open Exa Tap Dial
open Haro Ione Larch Glyph
section
variable {N:Side}
end
open Exa Tap Dial
open Push.AbsoluteSums Trees Mew Floral Axial
open Levier Salt Ione Nacre BondL
open scoped YM.CF.Mew YM.CF.Sour.Axial NNReal
variable {T S:BeatL n}{U:Scree.Loom n}{R t d a b c W z₀ z₁ Wk:ℝ}{q:ℕ} {m:Cash P}
namespace Trial
variable (Y:Trial T S P U q t d W z₀ z₁ a b c Wk)
local notation "F"=> Y.F
local notation "k"=> Y.k
variable {e:ℝ}{B G:Stream n}(h:B.Bears P m (cipherK q) W e)(h':G.Bears P m (cipherK q) W e)(p:Reservoir P m R W a b c e Wk)[Nonempty (ΘS R)]
local notation "A"=> orchard F R p.fp.le
local notation "φ"=> board P R W a b c
variable {hd ε:ℝ}{i j: ΘS R}
def delta (x z:ΘS R):ℝ:=dist z.val x.val/R
include p
lemma delta_cost (i j:ΘS R) : 0 ≤ delta i j ∧ delta i j ≤ 2 ∧ ‖j.val-i.val‖= delta i j*R:=by
 unfold delta; rw [dist_eq_norm]; have hz:(0:ℝ)<R:=p.fp; exact ⟨by positivity,(div_le_iff₀ hz).mpr (le_trans (norm_sub_le ..) (by linarith [i.property,j.property])), (div_mul_cancel₀ _ hz.ne').symm⟩ -- lin
local notation "D"=> delta i j
include Y h
lemma spiral : ContractingWith (3/256:ℝ≥0) (Y.onZ h p):=by
 refine ⟨by norm_num,LipschitzWith.of_dist_le_mul fun j i=>?_⟩; obtain rfl|u:=eq_or_ne j i; · simp
 have hx:=h.bark; obtain ⟨u₁,u₂,d⟩:= delta_cost p i j; have hg:0<delta i j:=div_pos (dist_pos.mpr (fun t=>u (Subtype.ext t))) p.fp
 have ht:Court B.B B.B P (cipherK q) m R W 0 (delta i j) i j:=by
    refine ⟨hx,hx,le_rfl,zero_le_one,u₁,u₂,d.le,by rw [zero_add]; exact hg,?_,?_⟩
    · rw [zero_mul,sub_self , show Fine (0:Cusp n)=0 from rfl]; simpa only [norm_zero, zero_mul,zero_smul] using Binder.σ hx.maxH (0:ℂ) -- `Fine 0=0` tune
    rw [zero_mul,sub_self]; simpa using Flaws.σ hx.maxF (0:ℂ)
 have hk:= h.core.firm; have he:= wavy Y h h p ht (show Books P (B.E-B.E) W (0*(e/4)) from (by simpa only [sub_self, norm_zero,zero_mul,zero_smul] using Books.σ (show Books P B.E W e from ⟨hk.weight,fun _ u=>u.elim⟩) (0:ℂ))); change _ ≤ (↑(_:ℝ≥0):ℝ)*dist j.val i.val; push_cast; rw [dist_eq_norm,d]; exact he.trans_eq (by ring)
lemma earned :∃ i:ΘS R,Y.onZ h p i=i:= Moen.Space.bow p.fp _ (Y.spiral h p).toLipschitzWith.continuous
def solve : ΘS R:= (Y.earned h p).choose -- duplicate?
lemma capital : Y.onZ h p (Y.solve h p)= Y.solve h p:= (Y.earned h p).choose_spec
lemma unique (x:ΘS R): riseV x=hz Y B x.val ↔ x=Y.solve h p:=⟨fun i=>ContractingWith.fixedPoint_unique' (Y.spiral h p) (show Function.IsFixedPt _ _ from Subtype.ext (Subtype.ext ((on_tag Y h p x).trans i.symm))) (show Function.IsFixedPt _ _ from capital Y h p),fun i=> by rw [i,←on_tag Y h p (Y.solve h p),capital]⟩ -- tune
lemma credit : let i:=Y.solve h p; BondL.PickZ P (flow Y B i.val) (cash Y B i.val+tuneL k F i.val) B.Q Y.T₀ Y.M Y.j B.L W B.Υq (due m e R W a b c) (m.κ⁻¹*m.Γr) m.γr wΨ True ∧ EdgeC P (k).tile (k).pos T S B.B (flow Y B i.val) (riseV i):=by
 intro i; have he:= (gamble Y h p i).choose_spec.2; rw [show (gamble Y h p i).choose=i from Y.capital h p] at he; exact ⟨⟨he.foot,fun _=> he.post rfl,he.theme,he.price⟩,edge Y h p i⟩
variable {s l:ℝ}[Nonempty (ΘS s)]
lemma squeeze(hs:s≤ R) (u:B.Bears P m (cipherK q) W l)(v:Reservoir P m s W a b c l Wk): (Y.solve u v).val= (Y.solve h p).val:=
 let i:=Y.solve u v; let X:ΘS R:=⟨i.val,i.property.trans hs⟩; congrArg Subtype.val ((Y.unique h p X).mp (show riseV i=hz Y B i.val from (Y.unique u v i).mpr rfl))
end Trial
end YM.CF.Sour.Digit
