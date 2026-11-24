import Anomaly.Ship.Glass
import Anomaly.Ship.Pod
import Anomaly.Ship.TwinZ
import Anomaly.Apert.Lift
import Anomaly.Apert.Price
import Anomaly.Ship.Salary
import Anomaly.Ship.Tines
set_option autoImplicit false
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Vow.TreasuryFog
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
open Cube Lat Tenant Tulip
open Pastry Hake Peaks Fock Branch Drapes Rush Scroll Paige Vault Phase Acorn Spire
attribute [local instance] opCStarAlgebra
open Palot Cadre Rill Stax Rive Ione Larch Roots Push.AbsoluteSums.Trees Sour Py.Rate.BScale Nor Mew PowerSeries
open scoped Mew

variable {n:Side} {I:Type} [LinearOrder I] [Fintype I]
variable {P:BudgetPoint} {q:ℕ} {h:ℝ}
open Neon Bake Rive QuadClock Stilo Roots
-- earned Root-v keyed regulator rep. Analytic both fresh and old together.
-- expose First pins on separated Θ tests
variable {N B:Side}
local notation "Fᴷ" => mid N B
set_option maxHeartbeats 700000
local notation "F₀"=> Orbit (mid N B)
open Py Oise Swell Sault Pastry Rue
variable {R:GramM (mid N B)}{L:Side}{wL:Odd L.val}{i_:ℕ}{X: Pricing i_ L wL (Thread i_)}{e':ℝ}(U:Grasp X B e')(C:Scree.Loom (mid N B))
variable {A:Key I→ I→ Bag (mid N B)}
variable {a b: Key I→I→ Aura (mid N B)→ℝ} {K:Key I→ForceBudget (mid N B)}
variable (H:∀ z∈hill I,∀ i:I,∀ X:Aura (mid N B),Sour.Flight R.p q X h (A z i X) (a z i X) (b z i X))
variable {D:Finset I}{σ:I→Site (mid N B)}{Ω:Occlus R.p}
variable (T: Crews D K (Cube.node∘σ) Ω A H) (u:1≤ h)
local notation "Θ"=>presse H
variable(m:ℕ)
local notation "YX" x:max=> lensCells (K x) (Θ x) m
local notation "Yφ" x:max=> lensG (P:=R.p) (K x) (Θ x) m
local notation "Sσ"=>Cube.node∘σ
variable {l:ℕ}{η v μ:ℝ}
variable (J: I→ RegBudget (mid N B))(G:I→Cusp (mid N B))(t0:I→ℂ)(x:I→ArcΦ)(Tp:Ids (mid N B))
local notation "σE"=> polish (K:=K) H m J Tp
variable (W:∀ i:I,Neon.Ice l (σ i) R.p h η v μ (coldE R.p (τι (lensG (P:=R.p) (K 0) (presse H 0) m) [i])) (J i) (G i) (t0 i) (x i))
local notation "Πq" F:max z:max E:max => color_b R R.beta (R.F+F) R.slip z (R.v+E)
local notation "Σσ"=> inkF (K:=K) H m G
variable (E:Key I→ RegBudget (mid N B))(F:Key I→ForceBudget (mid N B))(r:Key I→ℂ)
variable (V:Orbit (mid N B))(p:IsStarProjection (Dial.spar i_ R.J.M (C V)))
include p
set_option quotPrecheck false
lemma den_root (q:∀ X,River (fun z=> E z X V.1))(hK:∀ X,River (fun z=> F z X V))(uR: River r) : River fun z:Key I=> denZ (Πq (E z) (F z) (r z)) U C V:=by
 let Y(z):= r z • (1:Cipher Fᴷ)+exponentL R.p (E z) V.1; let Z(z):= exp (Y z)*fueled R.p (F z) V
 have hV:River Y:=by
    refine dub_V (κscale uR (zeroR _)) ?_
    unfold exponentL numbE; refine tick_sum _ _ (fun i _=> ?_)
    by_cases v:pingS R.p.threshold i.val.2 V.1; · simp_rw [Set.indicator_of_mem (show V.1∈ {k:Pane Fᴷ | pingS R.p.threshold i.val.2 k} from v)]; exact q i
    simp_rw [Set.indicator_of_notMem (show V.1∉ {k:Pane Fᴷ| pingS R.p.threshold i.val.2 k} from v)]; exact zeroR _
 have hv:River Z:=by
    refine River.mul_T (a:=exp ∘ Y) (b:=fun z=> fueled R.p (F z) V) hV.exp_V ?_
    unfold fueled; refine tick_sum _ _ fun j v=>?_ ; split; swap; exact zeroR _
    apply cost_R; intro i _; unfold clamp; split; exact hK i; exact zeroR _
 let T:=pilotH U R C V p; let Q:Cipher Fᴷ→ₗ[ℂ] Phys Fᴷ:=⟨⟨fun i=> T (Cadre.poseL _ i),fun i j=>(congrArg (fun v=>T v) (act_add ..)).trans (map_add ..)⟩,fun x y=>(congrArg (fun v=>T v) (act_smul ..)).trans (map_smul ..)⟩
 exact (sc_V hv Q.toContinuousLinearMap).cong (fun z _=> switched U C V (E z) (F z) _ p)
-- diagonal fresh parameter y=z
local notation "Xo" z:max=> (Πq (E z) (K z) (r z))
variable (oV:I→phy (mid N B)) (hp: Dorm D r)(uE:Dorm D E)
variable (fee:∀ z∈hill I,∀ (i:I),∀ v:Wave (Dwell (mid N B)),pilotH U (color_b R R.beta (R.F+E z) R.slip (K z) (R.v+r z)) C V p (acts (giveB (A z i) V) v)=acts (oV i V) (pilotH U (color_b R R.beta (R.F+E z) R.slip (K z) (R.v+r z)) C V p v))
-- use raw outputs. ANY assignments, incl nonuniform Sensors
local notation "Rn" z:max=> color_b (Xo z) R.beta ((R.F+E z)+σE z) R.slip (K z+Σσ z) ((R.v+r z)+α_ξ t0 z)
include W T u
lemma firm_root (pv:∀ X,River (fun z=> E z X V.1))(pr: River r) : River fun z:Key I=>denZ (Rn z) U C V:=by
 obtain ⟨pQ,P1,t,W⟩:=Polish_ports H T u m J G t0 x Tp W
 let S:= T.compass.toll; let Yo(z:Key I):=α_ξ t0 z
 let f:= E+σE; let h0:= K +Σσ; have ht:River (fun z:Key I=>denZ (Πq (f z) (h0 z) (r z+Yo z)) U C V):= den_root U C f h0 _ V p (fun i=>dub_V (pv i) ((pQ i).2 _)) (fun i=> dub_V (S i _) (W.toll i _)) (dub_V pr (rer_C _)) -- tune rer_C Rep_C
 refine ht.cong fun z w=>congrArg (fun x=>denZ x U C V) ?_
 unfold f; change color_b R R.beta ((R.F+E z)+σE z) R.slip (h0 z) ((R.v+r z)+Yo z)= _; rw [add_assoc,add_assoc R.v]; rfl
local notation "Wo"=> (flags R.p.threshold V.1)
open Push.AbsoluteSums Gas Ursell
lemma influx (u:Key I)(vQ:u∈hill I)(qL:FleetS R.p.threshold V.1): denZ (Rn u) U C V= pilotH U (Xo u) C V p (poseL _ (hGas Wo (hailV Wo ((YX u) u) V))):=by
 -- binder shadow.P
 let R':= Xo u
 have e := switched (P:=R') U C V (σE u) (K u+Σσ u) (α_ξ t0 u) (p)
 exact e.trans (congrArg (fun v:Cipher Fᴷ=>pilotH U R' C V p (poseL _ v)) (flow_cash H T (by assumption) m J G t0 x Tp W _ vQ V qL).symm)
include hp uE fee
variable (l':List I)
lemma fresh_root (z:Key I)(hv:z∈hill I)(wV:∀ i∈ l',i∈D)(hZ:∀ i∈D,z i=0)(hx:FleetS R.p.threshold V.1)(uS: l'.Nodup)(v':l'.length ≤ m)
    (t:l'.Pairwise (fun i j=> Commute (oV i V) (oV j V))) : tipI ((fun z:Key I=>denZ (Rn z) U C V) ∘ antler D z) l' = acts ((l'.map fun i=>oV i V).prod) (denZ (Xo z) U C V):=by
 let f:= fun v:Key I=>antler D z v; let He:= Xo z; let H':= pilotH U He C V p; let D0(z':Key I):=H' (poseL _ (hGas Wo (hailV Wo ((YX z) z') V)))
 let Y(v:Key I):=denZ (Rn v) U C V; have ht(y:Key I)(t:y∈hill I) : Y (f y)=D0 y:=by
    have hu:f y∈hill I:=antler_c D _ _ hv t
    unfold Y; rw [influx U C H T u m J G t0 x Tp W E r V p (f y) hu hx] -- order
    have gE:=Dorm.arg D E uE z y hv t hu; have gF:=Dorm.arg D r hp z y hv t hu; have gK:=Dorm.arg D K T.silent z y hv t hu
    rw [show (YX (f y)) (f y)= (YX z) y from Crews.pucks H T m z y hv t,show E (f y)=_ from gE, show K (f y)=_ from gK, show r (f y)=_ from gF]
 obtain ⟨a,b,r,F⟩:=T.wing z hv; let Af:= fun y v Y=>pinSeries (A z) y Y v
 let Q:= H' (poseL _ (hGas Wo (hailV Wo (settleK (K z)) V)))
 have h(z': Key I)(u:z'∈hill I)(x): H' (acts (∑ i:Aura Fᴷ,pinSeries (A z) z' i V) x)= acts (Liss.waveΦ (fun i=>oV i V) z') (H' x):=by
    unfold pinSeries Liss.waveΦ; simp_rw [Finset.sum_apply,Pi.smul_apply]; rw [sum_comm]; simp_rw [← smul_sum, act_sum,map_sum, act_smul,map_smul]; refine sum_congr rfl ?_; intro i _; rw [←show giveB (A z i) V=_ from Finset.sum_apply ..,show H' _=_ from fee z hv i x] -- annotation
 have hk:tipI D0 l'= acts ((l'.map fun i=>oV i V).prod) Q:=(concreteTip (settleK (K z)) r F.pigment (Θ z) _ F.price (zero_le_one.trans u) V hx F.gamb H' _ l' m v' h).trans (Liss.ketTip _ _ uS t Q)
 refine (lace_C l' (g:=D0) (fun _ uy=>ht _ uy) roots).trans (hk.trans ?_) -- tune f'=Y
 have hr:= showUp (R:=He) U C V p 0 (K z)
 have hv:exponentL He.p 0 V.1=0:=by simp [exponentL,numbE]
 rw [hv,exp_zero,one_mul,add_zero] at hr
 have he:Q=denZ He U C V:=by unfold Q; rw [totGas Ω (K z) (Θ z) _ q Af F u,settleSelf V hx]; exact hr.symm -- p shadow
 exact congrArg (fun v=>acts _ v) he
lemma mixed_root (q:ψS Sσ l')(hL:m≥ l'.length)(hx:FleetS R.p.threshold V.1)(pv:∀ X,River (fun z=> E z X V.1))(pr: River r)(t:(Leit D l').Pairwise (fun i j=> Commute (oV i V) (oV j V))) : tipI (fun z:Key I=>denZ (Rn z) U C V) l'= acts (((Leit D l').map fun i=>oV i V).prod) (tipI (fun z:Key I=>denZ (Xo z) U C V) (Leit (Finset.univ\D) l')):=by
 apply mix_rule D _ _ (firm_root U C H T u m J G t0 x Tp W E r V p pv pr) _ (den_root U C E K r V p pv (fun x=> T.compass.toll x V) pr)
 exact fun z w x0=> fresh_root U C H T u m J G t0 x Tp W E r V p oV hp uE fee (Leit D l') z w (by simp [Leit]) x0 hx ((List.filter_sublist).nodup (uS_b _ q)) ((List.filter_sublist).length_le.trans hL) t
end YM.CF.Vow.TreasuryFog
