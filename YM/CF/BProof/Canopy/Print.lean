import YM.CF.BProof.Canopy.Lips
import YM.CF.Pso.Loft
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
variable (Y:Trial T S P U q t d W z₀ z₁ a b c Wk) {ι:Type} [TopologicalSpace ι][Nonempty ι]
local notation "F"=> Y.F
local notation "Pk"=> Y.k
variable {e:ℝ} {B:ι → Stream n}(h:∀ i,(B i).Bears P m (cipherK q) W e) (p:Reservoir P m R W a b c e Wk)[Nonempty (ΘS R)]
local notation "A"=> orchard F R p.fp.le
variable (u:PointK (fun i=> (B i).B))(v:∀ x:Scree.Hub n,∀ V,Continuous fun i=> (B i).E x V)
include u v
lemma habitat(W':ι→ ΘS R) (u':Continuous W'): let Z(i):= Y.onZ (h i) p (W' i); Continuous Z ∧ (∀ x:Scree.Hub n,∀ V,Continuous fun i=> (Y.cash (B i) (W' i).val+tuneL Pk F (Z i).val) x V)∧∀ i:Aura n,∀ D⊆ i.val,∀ V,Continuous (fun z=> Y.flow (B z) (W' z).val i D V):=by
 intro Z; let Pk':=(Pk).hw; let h0:=zero_le_one.trans Pk'; choose S eX using fun i=> (h i).bark.prices h0
 have hx(i):m.vines (S i) ((A).bead W P) 1:= Cash.clock p.toWarrant (eX i) (cop F p.toLoomPay) Pk' (kernel_p Pk F p.fp.le (W' i)).dice
 let hX(i):=Cash.clock₂ (hx i); let he(i):= (eX i).fr; let hp:= Cash.Ψk; let ht:=Cash.Φk P; let HH:=Cash.ΦΨ P; have hw:wΨ≤wu P-wΨ*2:=by unfold wu wΨ; linarith [P.exponent_pos]
 have hu':= (A).tune_QX (k:=(Pk).paid) Y.k.tile Y.k.pos W Pk' (Pk).hv (Pk).y (Pk).hx (Pk).v (Pk).w ht hp HH wΨ m.sh m.z m.γr hp le_rfl p.s p.ht p.earn p.wings W' _ u S u' he hx hX (fun i=> (Leaf.price (eX i) (Cash.uv P) h0).lien) hw (fun i=> (B i).E) v Y.T₀ Y.j Y.M Y.Tp Y.ok Z (fun i=>?_) -- have/meta
 swap; · rw [pre_c Y p (B:=B i)]; exact Y.on_tag (h i) p (W' i)
 refine ⟨hu'.1,fun x V=>?_,fun i D g V=> ?_⟩
 · simp_rw [← pre_c Y p, ←goalL Pk F p.fp.le]; exact hu'.2 x V
 have heq(z:ι):Y.flow (B z) (W' z).val= _ := (flow_eq Y p (B:=B z) (W' z)).symm; rw [show (fun z=> Y.flow (B z) (W' z).val i D V)= _ from (show (fun z=> Y.flow (B z) (W' z).val i D V)=_ from funext (fun z=> congrArg (fun x:Cusp n=> x i D V) (heq z)))]; exact (A).key_z (k:=(Pk).paid) Y.k.tile Y.k.pos W Pk' V i (Pk).hv (Pk).y (Pk).hx (Pk).v (Pk).w ht hp HH W' _ u S u' he hx hX hw D g
lemma tenacity : let Z(i):=Y.solve (h i) p; Continuous Z ∧ (∀ x:Scree.Hub n,∀ V,Continuous fun i=> (Y.ahead (B i) (Z i).val) x V) ∧∀ i:Aura n,∀ D⊆ i.val,∀ V,Continuous fun z=>Y.flow (B z) (Z z).val i D V:=by
 intro Z
 have ht:Continuous Z:=by
    refine continuous_iff_continuousAt.mpr fun x=> Metric.tendsto_nhds.mpr fun ε he=> ?_
    let f(i):=Y.onZ (h i) p (Z x); let K:ℝ≥0:=3/256; have hx:= (Y.spiral (h x) p).one_sub_K_pos
    have hf:Continuous f:= (Y.habitat h p u v (fun _=> Z x) continuous_const).1
    have hζ:Tendsto (fun i=> dist (Z x) (f i)) (𝓝 x) (𝓝 0):=by simpa only [show f x=Z x from Y.capital (h x) p,dist_self] using (tendsto_const_nhds (x:=Z x)).dist (hf.tendsto x)
    filter_upwards [hζ.eventually (Iio_mem_nhds (show 0 < ε*(1-K:ℝ) from mul_pos he hx))] with y hz
    rw [dist_comm]; exact ((Y.spiral (h y) p).dist_le_of_fixedPoint (Z x) (show Function.IsFixedPt (Y.onZ (h y) p) (Z y) from Y.capital (h y) p)).trans_lt ((div_lt_iff₀ hx).mpr hz)
 have he:= Y.habitat h p u v Z ht; refine ⟨ht, fun x V=> ?_,he.2.2⟩; have hx:=he.2.1 x V; unfold Z at *; simp_rw [Y.capital] at hx; exact hx
end Trial
end YM.CF.Sour.Digit
