import YM.CF.Graph.Sage
import YM.CF.Girt.Quay
import YM.Gauge.Size
set_option autoImplicit false
noncomputable section
namespace YM.CF.Graph
open Filter Function NormedSpace Lattice Finset Cube SU Fock Lat Spire Scroll Peaks Drapes Rush Tulip Pastry Scree Girt Gall Branch Dial
open scoped Topology ContDiff Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators
attribute [local instance] opCStarAlgebra
open Skye RG Laic
open Sods Wilson PathData Precision Tree Work.F03
variable {N:Side}{t:ℝ}
open MeasureTheory Cascade Vale CF.Paige Vault Nova
open scoped NNReal ENNReal Classical
variable {n:Side}{C L H k r u v s a b c e y η:ℝ}{P:GramM n}
abbrev past(R:GramM n)(X:Pane n):ℝ:= Real.exp (-(R.path.inChannels R.funds R.p R.beta X))
def Lace(R:GramM n): Set (Orbit n):= (Prod.fst) ⁻¹' (Calm group (More n) R.p.threshold)
lemma lace_m(R:GramM n):MeasurableSet (Lace R):= measurable_fst (calm_m ..)
def dim(R:GramM n)(V:Orbit n):ℝ:= (Lace R).indicator (fun v=> past R v.1) V
def angle(R:GramM n):ℝ:=∫ i,dim R i∂city _
lemma worth(X:Ward P): Envelope (dim P):=by
 obtain ⟨c,p,w,U⟩:= X.area; have ht:= snap (ι:=Pane n) (Z:=Orbit n) (pole_w (P.path.inChannels P.funds P.p P.beta) (fun v=> Real.exp (-v)) (by fun_prop) (P.path.channels_env U _ _)) (measurable_fst)
 have hx(i:Orbit n): (past P i.1) = past P i.1:=rfl -- pin
 have hm: Envelope (fun i:Orbit n=> past P i.1):=ht; obtain ⟨b,g⟩:= hm.cost
 refine ⟨hm.meas.indicator (lace_m _),max b 0,fun i=>?_⟩; by_cases h:i∈Lace P; rw [dim,Set.indicator_of_mem h]; exact (g i).trans (le_max_left ..); rw [dim,Set.indicator_of_notMem h,norm_zero]; exact le_max_right ..
lemma mass_i (G:Gauge)(n:Side)(k:ℝ)(h:0<k)(p:k≤1): ((k/4)^(Module.finrank ℝ G.Mat))^(4*n.val^4)≤ (prior G n).real (stone G n k):=by
 rw [prior,Measure.real,stone,Measure.pi_pi]; simp_rw [prod_const,card_univ,show Fintype.card (Edge (Site n))=4*n.val^4 by unfold Edge; rw [Fintype.card_prod,site_card, (show Fintype.card Axis=4 from Fintype.card_fin _)]; omega,ENNReal.toReal_pow]; exact pow_le_pow_left₀ (by positivity) (G.shell_ge k h p) _
def gainS (n:Side)(h:ℝ):ℝ:= ((h/4)^(Module.finrank ℝ group.Mat))^(4*n.val^4)
lemma glow (X:Ward P)(W:P.path.Bounds P.funds H C L)(h:0<u)(hu:u≤1)(s:4*u≤P.p.threshold)(r:P.funds.direct ≤b)(hp:0≤C)(hv:0≤P.beta) : gainS (More n) u * Real.exp (-stoutY (More n) P.beta (4*u) b P.p.threshold C L) ≤ angle P:=by
 let N:= More n; let a:=stoutY N P.beta (4*u) b P.p.threshold C L; let v:= Real.exp (-a); have he:0<v:=by unfold v; positivity
 let S:Set (Orbit n):= Prod.fst ⁻¹' (stone group N u); have hx:MeasurableSet S:= measurable_fst (stones ..)
 have hi(i:Orbit n): S.indicator (fun _=>v) i ≤ dim P i:=by
    by_cases z:i∈ S; swap; · rw [Set.indicator_of_notMem z]; exact Set.indicator_nonneg (fun _ _=> (Real.exp_pos _).le) _
    have hb:i∈Lace P:= rife P.p _ z s -- tune
    rw [dim,Set.indicator_of_mem z,Set.indicator_of_mem hb]; exact Real.exp_le_exp.mpr (neg_le_neg (money W _ i.1 z r s h.le hv hp))
 let μ:=city n; have hj: gainS N u≤ Measure.real μ S:=by
    rw [Measure.real, show μ S= _ from ((measurePreserving_fst (μ:= prior group N) (ν:= Skye.depot n)).measure_preimage (stones group N u).nullMeasurableSet)]; exact mass_i group _ u h hu
 refine le_trans ?_ (integral_mono ((integrable_const v).indicator hx) ((worth X).integrable μ) hi); rw [integral_indicator hx, setIntegral_const]; exact mul_le_mul_of_nonneg_right hj he.le
structure SkinT (P:GramM n)(T:Loom n)(η:ℝ):Prop where
 wave: ∃ u:ℝ,∃ j:ℕ, Roof _ u η j T
 high: ∀ V,V∈Lace P→ T V= V.1
variable {m B J:Side}{o:Odd J.val}{j:ℕ}{Y: Pricing j J o (Vault.Thread j)}{P': Grasp Y B e}
abbrev cab (R: GramM (mid m B))(P:Grasp Y B e)(A:Loom (mid m B))(t:Orbit (mid m B)):= changeM (m:=m) P (A t) R.J.M
lemma moon (W:Pearl P')(p:Stamped j J o Y)(t:0<e)(w:1≤j)(h:P'.roundZ ≤ (mid m B).val)(A:GramM (mid m B))(X:Loom (mid m B))(K:SkinT A X e):Envelope (cab A P' X):=by
 letI: CompactSpace (CapX m B e):= isCompact_iff_compactSpace.mp (show IsCompact {x:Pane (mid m B)|Guard x e} from (CF.Phase.cover_closed ..).isCompact)
 obtain ⟨R,l,F⟩:= K.wave; let f(i:Orbit (mid m B)):CapX m B e:= ⟨X i,F.paid _⟩
 exact refill (fun i:CapX m B e=> changeM P' i.val A.J.M) (Kea.concur W p t w A.J.M h) f F.bill.subtype_mk
end YM.CF.Graph
