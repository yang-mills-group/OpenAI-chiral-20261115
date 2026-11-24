import GaugeFieldConstruction.PriceplacJ
import GaugeFieldConstruction.AerageJ
import GaugeFieldConstruction.DolourJ
import GaugeFieldConstruction.Pillars
import GaugeFieldConstruction.CannonJ
import GaugeFieldConstruction.Enmity
import GaugeFieldConstruction.Quail
import YM.CF.Roots.East
import GaugeFieldConstruction.Overland
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 800000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Py.Rate
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open CF.Appel CF.Newt CF.Char CF.Neige CF.Summit Next Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Wisps Next.SectorChange.Schur MultiNext.SignedSource Lyre Banjo Analysis Pressure AnalyticBridge.MarginalMultiplier3b1d PatchReads SectorNext.Remainder SectorNext.Remainder.Scales Planned.AtomRegular Extra.Iteration Extra.Iteration.Scales
open Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
open AnalyticBridge.Annulus1AD Ac Esti
open Atala Forge Cloak Rill Hive Fock Stilo Palot Scion
open Cube Lat Tenant Tulip
open Pastry Hake Levier Urn Peaks Fock Laic Branch Drapes
attribute [local instance] opCStarAlgebra
open Rush Scroll Paige Vault Phase Acorn Spire
attribute [local instance] opCStarAlgebra
open Tarn Cay Slate Esti Cour Hest Arena Reine Kennel Facet Broc Pec Push.SectorMeasure.Oriented
open Hom Vale Vale.Grace Next.Free Thera Nacre Dial Fock
open Tye Lich Stake Pail Pail.Dew
open Ione Beau Haro Cascade Fief
open Wray Oath Feu Feu.Corset Nor Yaw Pig Oise Jade Plume Push.AbsoluteSums
open Trees Lich.Muster Jet
set_option linter.flexible false
open Eire Girt
open VolumeRate
namespace Pitching
open Vow Bake Larch
namespace Focus
open Neon
open Mew Vow Rive Roots
open scoped YM.CF.Mew
namespace CoeffArc
section
variable {N:Side}{I Z D E : Type}[Fintype I][LinearOrder I][Fintype Z] [NormedAddCommGroup E][NormedSpace ℂ E][CompleteSpace E]
open Ing Ing.Iona Onwards Py.Riant Fock.Flux
variable {m n L B:Side}{K:Teller SU.group}{R:Patch}{X:ChartRatio SU.group}{d:ℝ}(V:Grace K R X)
variable (P:GramM (mid m B))(U:Grasp V.U B d) (H:Loom (mid m B)) (σ:I→Seat (mid m B))(A:Finset I)
variable (F:Finset I→ RegBudget (mid m B))(T:Finset I→ ForceBudget (mid m B))
variable (L0: Loom (mid n B))(ρ: Ratio (mid n B) (mid m B))(q:Chi)(t:ℝ)
local notation "Bco" => mid m B
variable {r s v h a C:ℝ}(p:0<h)(pv: P.p.power=2) (L':Graph.Ledger h v v a C P)
variable (τ:Journal1 P.p p σ F T (5/4) 1 s)
variable (e:1 ≤ r)(f:8 ≤P.p.B)(m₀:ℕ)(hp:Force_M P.p.B σ m₀)(w:Nice_B P.p.B m₀ r (1/32))(tL:0≤ s)
-- scaling mask.
abbrev ArM (A:Finset I)(r:ℝ)(i j:I):ℂ:= if j=i∧ i∈A then ↑r else 0
include τ p
omit τ p
local notation "C0"=> ArM A r
local notation "uX"=> toV_C σ C0
lemma arDream (z:Key I)(i:I): uX z i= if i∈A then (r:ℂ)*z i else 0:=by
 unfold toV_C; rw [sum_eq_single_of_mem (s:=pipe_ζ σ i) i (mem_filter.mpr ⟨mem_univ _,rfl⟩)]
 · split
   next h=> rw[ArM,if_pos ⟨rfl,h⟩]
   next h=> rw[ArM,if_neg (fun t:i=i∧ i∈A=> h t.2),zero_mul]
 intro j v e; rw [ArM,if_neg (fun v:j=i∧ i∈A=> e v.1),zero_mul]
include e
lemma dreamBeam (z:Key I)(v:z∈hill I): (∀ i, ‖uX z i‖ ≤r)∧ (∀ i∉A,(uX z i)=0):=by
 refine ⟨fun i=>?_,fun i h=>by rw[arDream,if_neg h]⟩; rw[arDream]; have h₁:=zero_le_one.trans e; split_ifs
 · rw[norm_mul,Complex.norm_real,Real.norm_of_nonneg h₁]; exact mul_le_of_le_one_right h₁ (hill_i.mp v i)
 exact norm_zero (E:=ℂ)|>.trans_le h₁ -- tune
local notation "KV"=> (Fintype.card (Seat Bco):ℝ)
abbrev DustJ (A:Finset I) (N:Side)(r s:ℝ)(B:ℕ):ℝ:= (A.card:ℝ)*(r*s)+(Fintype.card (Seat N):ℝ)*hope_E B s
include p pv τ L' e f hp w tL
local notation "Sκ"=> DustJ A Bco r s P.p.B
local notation "Sμ"=> v*KV+Sκ
abbrev aBeam(x:Key I):=color_b P P.beta (P.F+WritV σ F (toV_C σ (ArM A r) x)) P.slip (P.K+WritV σ T (toV_C σ (ArM A r) x)) P.v
local notation "Pζ"=> fun i:Key I=>aBeam (r:=r) P σ A F T i
lemma dreamy (z:Key I)(hz:z∈hill I): let H':= aBeam (r:=r) P σ A F T z; Arc_r H' h (ExTax P (fun i:Scree.Hub (mid m B)=> i.val.2) Sμ) v (ExTax P (fun i:Scree.Force (mid m B)=>i.val.1.val.2) Sμ)∧ ∀ x:Orbit (mid m B), tier h (H'.board x).val ≤ Real.exp (2*Sκ + 3*v* KV):=by
 intro H'; let V':=σ; let K:=v*(Fintype.card (Seat Bco):ℝ); let Z:=Sκ
 have ⟨pB,Tg⟩:= dreamBeam σ A e z hz; have ht:=τNow σ A (SecX (KeyUp P.p) p.le Bco) (fun i=>show i.val.2.Nonempty from ⟨_,i.property⟩) F e f τ.fil τ.rite hp w tL (uX z) pB Tg τ.root.1; let P₀:=H'.F; let W:=H'.K
 have u:VastJ (SecX (P.p) p.le Bco) P₀ (K+Z) := Vast_add _ (VastRegJ P L' p) (WIde P p ht pv)
 have hz':=τNow σ A (SecK P.p p.le Bco) (fun i=>show i.val.1.val.2.Nonempty from ⟨_, i.val.1.property⟩) T e f τ.high τ.right hp w tL (uX z) pB Tg τ.root.2
 have vX:VastJ (SecK P.p p.le Bco) W (K+Z):=Vast_add _ (VastForceJ P L' p) hz'
 refine ⟨⟨VaryReg P p u,L'.slip,VaryF P p vX⟩,fun x=>?_ ⟩
 let Q:= Graph.actG H' x; let F':=fueled H'.p H'.K x; have hv: tier h Q.val ≤ (K+Z)+K :=by
    apply le_trans (b:=tier h (exponentL H'.p P₀ x.1).val+tier h (exponentL H'.p P.slip x.1).val) (tier_plus p.le _ _) -- tune p
    apply add_le_add (VastRegTier (X:=P) p u x)
    rw [show K= v*(More Bco).val^4 from (by unfold K; rw [site_card,Nat.cast_pow])]; exact Graph.toeE L'.slip p.le _
 change tier h ((exp Q:Dough _).val* F'.val) ≤ _
 rw[show 2*Sκ+3*v*KV=((K+Z)+K)+(K+Z) from (by unfold K Z; ring), Real.exp_add]; exact (tier_mul p.le _ F').trans (mul_le_mul ((dust_exp h Q p.le).trans (Real.exp_le_exp.mpr hv)) (VastForceTier (X:=P) p vX x) (Pastry.pitch p.le F'.val) (Real.exp_pos _).le)
omit p τ e f hp w pv L' tL
local notation "D0"=> fun z:Key I=> denZ (aBeam (r:=r) P σ A F T z) U H
local notation "O_F"=>Verdante σ C0 F
local notation "O_K"=>Verdante σ C0 T
lemma dream_κ (l:List I)(u:ψS σ l)(W:Orbit (mid m B)): let Q:Key I→Phys (mid m B):=fun z=>denZ (BreathJ P σ F T 0 z) U H W; Law_C σ C0 l Q (fun z:Key I=>D0 z W):=by
 intro Q
 let x(z:Key I):= P.F+WritV σ F z; let y(z:Key I):= P.K+WritV σ T z
 let zP(z:Key I):= P.F+WritV σ (Verdante σ C0 F) z; let zF(z:Key I):= P.K+WritV σ (Verdante σ C0 T) z
 have hp:Q=(fun z:Key I=>denZ (color_b P P.beta (x z) P.slip (y z) P.v) U H W):=by funext z; unfold Q BreathJ; rw[add_zero]
 have hv:D0=(fun z:Key I=>denZ (color_b P P.beta (zP z) P.slip (zF z) P.v) U H):=by
    funext z; unfold aBeam zP zF; rw[TellerJ,TellerJ]
 let L:= pulse_H (U:=U) V σ C0 l u P H x zP (fun _=> P.slip) (fun _=>P.slip) y zF (fun _=>P.v) (fun _=>P.v) W (fun i p=>foamPlus σ F C0 l u (P.F i p) _ _) (fun _ _=>σtag_l ..) (fun i p=>foamPlus σ T C0 l u (P.K i p) _ _) (σtag_l ..)
 rw [hp,hv]; exact L
lemma stampI {E:Type}[NormedAddCommGroup E][NormedSpace ℂ E](l:List I)(x:∀ i∈l,i∈A) (u:List I→E): Roots.snow σ C0 u l=(r:ℂ)^l.length • u l:=by
 induction l generalizing u with
 | nil=> simp [Roots.snow]
 | cons i l ih=>
   rw [Roots.snow,sum_eq_single_of_mem (s:=pipe_ζ σ i) i (mem_filter.mpr ⟨mem_univ _,rfl⟩),ArM,if_pos ⟨rfl,x _ (List.mem_cons_self ..)⟩,ih (fun j u=>x _ (List.mem_cons_of_mem _ u)),List.length_cons,pow_succ',mul_smul]
   intro j p t; rw [ArM,if_neg (fun e:i=j∧j∈A=> t e.1.symm),zero_smul]
lemma zoom_tip (l:List I)(t:ψS σ l)(h_:∀ i∈ l,i∈A)(W:Orbit (mid m B)): tipI (fun z:Key I=>D0 z W) l=(r:ℂ)^l.length • TraceJ U P H σ F T 0 l W :=by
 let T:= dream_κ V P U H σ A F T l t W (r:=r) -- shadow
 exact (T.2.2 l (List.Sublist.refl _)).trans (stampI σ A l h_ _)
#print axioms dreamy
end
end CoeffArc
end Focus
end Pitching
end YM.CF.Py.Rate
end
