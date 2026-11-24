import YM.SatinExist.Szell
/-!
 # CP9: hierarchical operator fields. Price (strong) at poly domain. EU-Wick all orders thereof. Still not a relativistic determination: actual unclipped gauge price lacks spatial orientations/gluing and factors. Use in advance.
-/
set_option autoImplicit false
set_option synthInstance.maxSize 29000
set_option maxRecDepth 3500
set_option maxHeartbeats 520000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Heat Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry TopologicalSpace
namespace Spine
open Aria Casting
open _root_.YM.CF.Buffered.Afterglow.Hierarchy.Seld LineDeriv
open _root_.YM.Boundary Spectral Poin
open SatinTails SatinJets Ballad
variable (P:Spine) (x:P.Spectrum0 3) (A:ℕ→P.Apron) (j:Axis)
local notation "ξ"=>P.advocate 3 x j
local notation "CX"=> P.ManyF j (P.advocate 3 x j)
local notation "ν"=> P.seasons j (P.advocate 3 x j)
local notation "λ'"=> P.ColorHil j (P.advocate 3 x j)
local notation "ω"=> P.heaven j (P.advocate 3 x j)
local notation "ω'"=> P.Asp x j
local notation "G"=> P.cartage j (P.advocate 3 x j)
local notation "T"=> M (P.seasons j (P.advocate 3 x j))
local notation "K"=> Cache (P.seasons j (P.advocate 3 x j))
local notation "χ" i:max J:max=> (A i).pivot P J
variable (V:P.PowerNames x A)
structure PowerNames.Costs : Prop where
 transports (v: E4) (l:List Axis) (f:Test4) (i: Bench (P.seasons j (P.advocate 3 x j))) : (P.seasons j (P.advocate 3 x j)).unit.translation v (((V.action P x A j l) f i).val)= (V.action P x A j l (Probe.ahead v f) (CF.Buffered.Afterglow.Hierarchy.Seld.usher (P.seasons j (P.advocate 3 x j)) v i)).val
 space (v:E4): (P.seasons j (P.advocate 3 x j)).U (OS.Semigroup.SEP j v)=P.cartage j (P.advocate 3 x j) (lens v)
 sharp (v:List Axis)(f:Test4)(a b:Bench (P.seasons j (P.advocate 3 x j))): inner ℂ ((V.action P x A j v f a).val) b.val=inner ℂ a.val ((V.action P x A j (j::v) (Probe.bar f) b).val)
 attends (v:List Axis)(a:Bench (P.seasons j (P.advocate 3 x j))) : Continuous (fun f=> (V.action P x A j v f a).val)
 warms (n:ℕ)(r:Fin n→List Axis)(f:Fin n→Test4) (i:Bench (P.seasons j (P.advocate 3 x j))) (s:ℝ≥0)(t:0 < s): pays_to (P.seasons j (P.advocate 3 x j)) atTop (P.HBills x A j r f i s) (P.posBills x A j V r f i s)
 lands (n:ℕ)(r:Fin n→List Axis)(f:Fin n→Test4) (i:Bench (P.seasons j (P.advocate 3 x j))) : pays_to (P.seasons j (P.advocate 3 x j)) (𝓝[>] (0:ℝ≥0)) (fun s=> P.posBills x A j V r f i s) ((List.ofFn (P.labelBills x A j V r f)).prod i)
lemma PowerNames.kudos : V.Costs P x A j:=by
 constructor
 · intro p j' f i; exact congrArg Subtype.val (CF.Buffered.Afterglow.Hierarchy.Seld.attends (ν) _ _ _ _ _) -- ambiguity
 · exact P.actual_times x j
 · exact V.adj_rule P x A j
 · intro v a; exact CF.Buffered.Afterglow.Hierarchy.Seld.singular ..
 · exact fun n=> P.beat_bills x A j V
 intro n r f i; rw [P.granted_W]; exact P.heat_limit x A j V r f i

variable (W': ∀ (n :ℕ), (Fin n → List Axis) → (Joint n) →L[ℂ] P.ManyF j (P.advocate 3 x j))
-- *not* promising covariance etc. -i timing always with ι.
structure MomentWhere :Prop where
 wave (n:ℕ)(r: Fin n → List Axis)(p: Points n) : AnalyticOnNhd ℂ (V.promiseW P x A j r p) (OrientedTimes n)
 interior (n:ℕ)(r: Fin n → List Axis)(p: Points n)(s:Equiv.Perm (Fin n))(a:ℝ)(u:DiningE j p s a)(J:P.Ellis 3 x): EuGift j (nextSeam p s) a∈ OrientedTimes n ∧
      Tendsto (fun m=> P.commonWell 3 x (P.reachU A r m) (Vants p) (Each n)) atTop (𝓝 (inner ℂ (P.heaven j (P.advocate 3 x j)) (V.promiseW P x A j (r ∘ s) (nextSeam p s) (EuGift j (nextSeam p s) a))))
 charged (n:ℕ)(r:Fin n→List Axis)(q:Joint n)(t: Fin n→ℝ≥0)(h:t∈Margins n) : (∀ p: Points n, countM j 0 p.ofLp t∈ OrientedTimes n) ∧ Integrable (fun p:Points n=> q p • V.promiseW P x A j r p (countM j 0 p.ofLp t))
 arcs (n:ℕ)(r:Fin n→List Axis)(q:Joint n) : Tendsto (fun t=> ∫ p:Points n, q p • V.promiseW P x A j r p (countM j 0 p.ofLp t)) (𝓝[Margins n] (0:Fin n→ℝ≥0)) (𝓝 (W' n r q))
 fields(n:ℕ)(r: Fin n→List Axis)(f: Fin n→Test4): W' n r (Joint.materialize n f) = ((List.ofFn (P.labelBills x A j V r f)).prod (P.Asp x j)).val
lemma PowerNames.named: ∃ W' : ∀ (n:ℕ), (Fin n→List Axis) → (Joint n) →L[ℂ] P.ManyF j (P.advocate 3 x j), MomentWhere P x A j V W' :=by
 choose W' t using fun n (f: Fin n → List Axis)=> boundary_R (ν) ω 0 ((V.fields j) ∘ f) (pedestal 0 (V.rate j ∘ f))
 have he(n:ℕ)(r:Fin n→List Axis)(z: Fin n → ℝ≥0)(v:z∈Margins n)(p:Points n) : V.promiseW P x A j r p (countM j 0 p.ofLp z)=regia (ν) ω 0 (slew (ν) (pedestal 0 ((V.rate j) ∘ r)) z) ((V.fields j) ∘ r) p:= conducts _ _ _ _ _ _ v -- syntax
 refine ⟨W',⟨fun _ _ _=>wave_h (ν) ω _ _ _,?_,?_,?_,?_⟩⟩
 · intro n r p s a u J; exact ⟨EuGift_ready _ _ _ u, P.perm_w x A j V r p s J a u⟩
 · intro n r q z v; simp_rw [he _ _ _ v]; exact ⟨fun _=> clock_ready _ _ _ v, regiaI ..⟩
 · intro n r Q; apply ((t n r) Q).congr'; filter_upwards [self_mem_nhdsWithin] with z h; simp only [he _ _ z h, wishL_eq,regia_bill]
 intro n r f; rw [P.granted_W]; exact computes (ν) (ω') (P.transportsK x j) _ _ _ (W' n r) (t n r)
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
