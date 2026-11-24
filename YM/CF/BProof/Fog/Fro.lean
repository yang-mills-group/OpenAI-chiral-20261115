import YM.CF.BProof.Fog.Beam
import YM.CF.BProof.Law.Product
set_option autoImplicit false
noncomputable section
namespace YM.CF.Window
open Graph Graph.Diff
open Filter Function NormedSpace Lattice Finset Cube SU Fock Lat Spire Scroll Peaks Drapes Rush Tulip Pastry Scree Girt Gall Branch Dial
open scoped Topology ContDiff Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Classical
attribute [local instance] opCStarAlgebra
open Skye RG Laic
open Sods Wilson PathData Precision Tree Work.F03
variable {N:Side}{t:ℝ}
open MeasureTheory Cascade Vale CF.Paige Vault Nova
open Emu Flare
namespace Unfit
variable {m B L:Side}{j n:ℕ}{o:Odd L.val}{Y:Pricing j L o (Thread j)}{e v b c a l r K u η vA k s r' D L' C μ y R w z β:ℝ}{P:Grasp Y B e}
variable (A U:GramM (mid m B))(S:Loom (mid m B))(Hm:P.roundZ ≤ (mid m B).val)(H:Roof _ u e n S)
local notation "Π" => mid m B
variable (he:U.path.Bounds U.funds μ D L')(hD:0≤D)(hw:0≤U.beta)(hp:U.beta≤β)(W:Ledger R v v r C U)(ht:0≤r)(tA:1≤R)(hC:0≤C)
open YM.CF.BProof
/-
 Marks on physical fields are `Prelude` etc, so Enough to prove diff for unnormalized
 physical kernels. Here also variant of thm:Fit for tests taking tags, not for use as AP
 kernels.
 -/
abbrev Spy (N:Side):= Orbit N→FC (Single N)
local instance (I : Type) [Fintype I] [DecidableEq I] : MeasurableSpace (Op I) := borel _
local instance (I : Type) [Fintype I] [DecidableEq I] : BorelSpace (Op I) := ⟨rfl⟩
abbrev costSpy (p: Spy N)(v:ℝ) := ∀ x,‖p x‖ ≤ v
def taste (X: Orbit N→ Phys N)(F:Spy N)(x:Orbit N):= beamZ N (acts (F x) (X x))
def gulp (X: Orbit N→ Phys N)(F:Spy N):= ∫ x, taste X F x ∂city N
lemma env_taste (X: Orbit N→ Phys N)(F:Spy N)(t:Envelope F)(h:Envelope X): Envelope (taste X F):= pole_w (X:=Phys N) (fun i=>acts (F i) (X i)) _ (continuous_const.inner continuous_id) (kitE F X (fun x y=>acts x y) (Continuous.clm_apply (acts_cont.comp continuous_fst) continuous_snd) t h) -- open Girt
lemma env₀ (h:Envelope (denZ U P S)): Envelope (ket₀ U P S):=by
 exact pole_w (denZ U P S) (fun x=> Complex.exp (-U.v) • x) (Continuous.const_smul continuous_id (Complex.exp (-U.v))) h
lemma fee(X:Orbit N→Phys N)(F:Spy N)(c w:ℝ)(u:costSpy F w)(h:∀ i,‖X i‖≤c): ‖gulp X F‖ ≤ w*c:=by
 let t(i:Orbit N):= taste X F i; have he(i:Orbit N): ‖t i‖ ≤ w*c:=by
    apply (norm_inner_le_norm ..).trans; rw [(Dial.tickB N).2,one_mul]; exact (spentS ..).trans (mul_le_mul (u i) (h i) (norm_nonneg _) ((norm_nonneg _).trans (u i)))
 exact (norm_integral_le_of_norm_le_const (μ:=city _) (Eventually.of_forall he)).trans_eq (by simp)
lemma drop (X Y:Orbit N→Phys N)(F:Spy N)(p q:ℝ)(t:Envelope F)(u:costSpy F q)(h:Envelope X)(hv:Envelope Y)(hi:∀ i,‖X i-Y i‖ ≤ p): ‖gulp X F-gulp Y F‖ ≤ q*p:=by
 rw [show gulp X F-gulp Y F=gulp (X-Y) F from ?_]; exact fee (X-Y) F p q u hi
 have hx:Integrable (taste X F) (city N):= Law.pay (env_taste X F t h)
 have hv:Integrable (taste Y F) (city N):= Law.pay (env_taste Y F t hv)
 unfold gulp; rw [←integral_sub hx hv]; unfold taste beamZ; simp only [Pi.sub_apply,map_sub,inner_sub_right]
theorem taste_of (X : Obs (mid m B)) : numerator U P S X = gulp (ket₀ U P S) (fun i=> X i.1):= rfl
theorem lower (X: Obs N)(p:Envelope X): Envelope (fun i:Orbit N=>X i.1):= Girt.snap (X:=fun x : Orbit N => x.1) p measurable_fst
-- cost exact scale
abbrev price (p:BudgetPoint)(b v C D L':ℝ):= b*(D*p.threshold^3+D*p.threshold^4)+ L'*p.threshold^2 + v*3 + (4 +180*(45*(2+2^2)))*C/16
lemma cost_epoch(n:Side)(p:BudgetPoint)(b v C D L':ℝ): cost n p b v C D L'=volt n *price p b v C D L':=by unfold cost price Graph.taxY Window.flagBill Graph.pittance Graph.doorF Graph.lark volt; rw [show (More n).val=n.val*2 from rfl]; push_cast; ring
end Unfit
end YM.CF.Window
