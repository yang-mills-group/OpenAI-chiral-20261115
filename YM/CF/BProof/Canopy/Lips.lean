import YM.CF.BProof.Canopy.Spring
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
variable {P:BudgetPoint}{X Y Z:Aura n}{V W:Firing n}{D:Support (More n)}
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
abbrev ahead(B:Stream n)(i:SpaceM):= cash Y B i + tuneL k F i
structure Pulse (δ:ℕ)(B G:Stream n)(P:BudgetPoint)(m:Cash P)(W ε e:ℝ):Prop where
 u:0<ε
 t:ε≤1
 tel: Binder P W (wu P) (Fine (G.B-B.B)) (ε*(m.sh/10))
 sale: Flaws P W (wu P) (G.B-B.B) (ε*(m.sf/10))
 near: Books P (G.E-B.E) W (ε*(e/4))
-- Price at hΔ. We need ≤ C'_A d/λ; sufficient bound below
local notation "φ"=> board P R W a b c
variable {ε:ℝ}
local notation "i"=> Y.solve h p
local notation "j"=> Y.solve h' p
-- avoid i shadow
lemma heads (v: Pulse (cipherK q) B G P m W ε e) : dist (j) (i) ≤ 2*R*ε ∧ Binder P W (ρL P) (Fine (Y.flow G (j).val-Y.flow B (i).val)) (3*ε*m.Γr) ∧ Flaws P W (ρL P) (Y.flow G (j).val-Y.flow B (i).val) (3*ε*(m.κ⁻¹*m.Γr)) ∧ IncX Utrue (ahead Y G (j).val-ahead Y B (i).val) P W (e*ε+2*ε*yard P R W):=by
 obtain ⟨e₁,e₂,e₃⟩:= delta_cost p i j; let u:=delta i j; have he:Court B.B G.B P (cipherK q) m R W ε u i j:= ⟨h.bark,h'.bark,v.u.le,v.t,e₁,e₂,e₃.le,add_pos_of_pos_of_nonneg v.u e₁,v.tel,v.sale⟩; have ht:= wavy Y h h' p he v.near; rw [capital,capital] at ht
 have hz:dist (j) (i)=u*R:=by change dist (j).val (i).val =_; rw [dist_eq_norm]; exact e₃
 rw [hz] at ht; have hu:u ≤ 2*ε:= by rw [mul_comm u] at ht; have hh:= (mul_le_mul_iff_right₀ p.fp).mp ht; linarith [v.u]
 obtain ⟨hw,hf,-⟩:= Court.glyph k F p.toLoomPay he
 refine ⟨?_,Wallet.mono hw (mul_le_mul_of_nonneg_right (by linarith) p.lean),Wallet.mono hf ?_,?_⟩
 · rw [hz]; refine (mul_le_mul_of_nonneg_right hu p.fp.le).trans_eq (by ring)
 · exact mul_le_mul_of_nonneg_right (by linarith) (mul_nonneg (inv_nonneg.mpr (zero_le_one.trans p.l)) p.lean)
 have hh: ‖(j).val-(i).val‖ ≤ 2*ε *R:= (e₃.le).trans (mul_le_mul_of_nonneg_right hu p.fp.le); have hq: 0≤2*ε:=mul_nonneg (by norm_num) v.u.le; obtain ⟨t,q⟩:=tone (2*ε) hq _ hh i; unfold ahead; rw [add_sub_add_comm,←map_sub (tuneL k F),q,map_smul]; refine bump (addT P (TWin Y h h' p he v.near) (inc_scale (lyre Y p t).1 _ hq)) ?_
 gcongr; try exact p.pay.le
 linarith only [hu,v.u]
end Trial
end YM.CF.Sour.Digit
