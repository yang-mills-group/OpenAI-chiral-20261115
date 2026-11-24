import YM.CF.Vp929.Stage.Factory
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
open scoped Mew

open Wray Oath Feu Feu.Corset Nor Yaw Pig Oise Jade Plume Push.AbsoluteSums
open Trees Lich.Muster Jet
set_option linter.flexible false
variable {K : Teller SU.group} {R : Patch} {L : ChartRatio SU.group} {V : Grace K R L}
open Eire Girt
open VolumeRate
variable {d:ℝ} {m n N B : Side} {U : Grasp V.U B d} {W : GivenX V U} {J : Robes N V W} {q : Chi}
variable {A C' Pay h ρ f ff ag Cg x β β' : ℝ} {D : Treaty J q A C' Pay h ρ} {c:Estimate}
variable {w:Location (R:=R) B m n} {p p' : BudgetPoint}
namespace Pitching

namespace Focus
open Sour.MatchW Sour.MatchW.Technique Cycle929 Tap Lilt Vow Ione Beau
open Sour Stockpile Test TestW QuiltB
local notation "τ0"=> mid m B
namespace Shop
open BudgetPoint
variable {r:ℝ}[Nonempty (Haro.ΘS r)]
variable (s:Shop w J p p' q h x r)
local notation "ι"=> Scree.mid m B
local notation "ηt"=> Scree.mid n B
local notation "Er"=> (ΘS r)
local notation "Tp"=> (Pair (Haro.ΘS r))
local notation "μ"=> ↥SpaceM
local notation "Eμ"=> Pair ↥SpaceM
variable {y:ℂ}{G H:Corr (Scree.mid n B)}{S:Set ℂ}
local notation "Shf"=> w.freq
local notation "φE"=> (houseP p K s.Aχ s.Γχ s.Λf)
local notation "dr"=> s.A0.dream
local notation "VE"=> shownP (A0:=s.A0) (Lp:=s.Lp) s.Ty
local notation "Ex"=> verseX (Lp:=s.Lp) (A0:=s.A0) s.Ty
local notation "EkX"=> verseY (Lp:=s.Lp) (A0:=s.A0) s.Ty
local notation "δφ"=> rollGX K.j s.s.k R.L.val (houseP p K s.Aχ s.Γχ s.Λf) h
local notation "xm"=> w.output.M
local notation "xT"=> pointW ι K.j s.s.k xm
local notation "sx"=> treeΘ p R.L.val
local notation "Sch"=> Client K R x w.input p' h
local notation "Sub"=> Pair (RegBudget ι)
local notation "Wp"=> s.multiplier
local notation "Sx"=> s.stepV
include s
open scoped NNReal
local notation "V'"=> (closedBall (0:Eμ) (r/2))
variable {F:Pair (Corr (mid n B))}
lemma half_room : V' ⊆ ball (0:Eμ) r:= closedBall_subset_ball (by linarith [s.Th.radius])
lemma march_Point (pB:Sch y F) : Set.MapsTo (Wp y F) V' V' ∧ LipschitzOnWith (1/2:ℝ≥0) (Wp y F) V':=by
 have hp(V:Eμ)(v:V∈ball (0:Eμ) r):= s.ceiling pB (mem_ball_zero_iff.mp v); refine ⟨Chute.littleV s.Th.radius hp,Chute.contract_form s.Th.radius hp fun Z g hζ t q=> s.stepHolo (show Arcμ x h p' w K Z _ _ from ⟨hζ,differentiableOn_const _, holoCorr_const Z F, fun _ _=>pB⟩) q t⟩

abbrev Point (x y:Eμ) := x=y
lemma zeroSubs : (0:Eμ)∈ V':= mem_closedBall_self (div_nonneg s.Th.radius.le (by norm_num))
def Sol (b:ℂ)(F:Pair (Corr ηt))(X:Eμ) :Prop:= X∈ V' ∧ Function.IsFixedPt (s.multiplier b F) X
lemma resolves {F:ℂ→Pair (Corr (mid n B))}{b:ℂ→ℂ}(A:Arcμ x h p' w K S b F): ∃ c:ℂ→Eμ,Form S c ∧ ∀ z∈ S, s.Sol (b z) (F z) (c z)∧(∀ c':Eμ,s.Sol (b z) (F z) c'→ c'=c z)∧ Tendsto (fun i:ℕ=> (s.multiplier (b z) (F z))^[i] 0) atTop (𝓝 (c z)):=by
 let R(z:ℂ):= s.multiplier (b z) (F z); let t:= (1/2:ℝ≥0); have g':t<1:=by unfold t; norm_num
 obtain ⟨g,pg,v⟩:= Chute.fix_form (F:=R) (fun z p=> (s.march_Point (A.legal _ p)).1) (fun z p=>(s.march_Point (A.legal _ p)).2) g' s.zeroSubs A.openT isClosed_closedBall isBounded_closedBall (fun g p w=> s.stepHolo A w (fun z u=> s.half_room (p u)))
 exact ⟨g,pg,fun z p=>by obtain ⟨a,b,c,d⟩:=v z p; exact ⟨⟨a,b⟩,fun w h'=>c w h'.1 h'.2,d⟩⟩
lemma existsSol (pB:Sch y F) :∃ c': Pair ↥SpaceM,s.Sol y F c' ∧ (∀ c₁,s.Sol y F c₁→c₁=c') ∧ Tendsto (fun i:ℕ=> (s.multiplier y F)^[i] 0) atTop (𝓝 c'):=by
 obtain ⟨g,_,t⟩:= s.resolves (show Arcμ x h p' w K Set.univ (fun _=> y) (fun _=> F) from ⟨isOpen_univ,differentiableOn_const _,holoCorr_const Set.univ F,fun _ _=>pB⟩)
 exact ⟨g 0,t 0 (Set.mem_univ _)⟩
def pickW (b:ℂ)(F:Pair (Corr ηt)) : Eμ:= if u:Sch b F then (s.existsSol u).choose else 0
lemma sleepsW (pB:Sch y F) : let X:= s.pickW y F; s.Sol y F X ∧ (∀ v,s.Sol y F v→ v=X) ∧ Tendsto (fun i:ℕ=> (s.multiplier y F)^[i] 0) atTop (𝓝 X):=by intro x; unfold x pickW; rw [dif_pos pB]; exact (s.existsSol pB).choose_spec
lemma kpS {F:ℂ→Pair (Corr (mid n B))}{b:ℂ→ℂ}(A:Arcμ x h p' w K S b F): Form S (fun z=>s.pickW (b z) (F z)):=by
 obtain ⟨c,hc,v⟩:= s.resolves A; exact hc.congr (fun z e=> (v z e).2.1 _ (s.sleepsW (A.legal z e)).1)

lemma homely (pB:Sch y F): sunny (inwardP r (s.pickW y F)):= intent1 (mem_ball_zero_iff.mp (s.half_room (s.sleepsW pB).1.1))
lemma δV (pB:Sch y F): ‖s.pickW y F‖ ≤ r/2:= mem_closedBall_zero_iff.mp (s.sleepsW pB).1.1
lemma real_I {X:Eμ}(G:X∈ V')(p:X.2=0): inwardP r X=rePoint (inwardP r X).1:=by refine Prod.ext rfl (Subtype.ext ?_); exact (congrArg Prod.snd (intent0 X (mem_ball_zero_iff.mp (s.half_room G)).le)).trans p
lemma real_aim (pB:Sch (β:ℂ) (G,0))(i:Eμ)(g:i∈V')(v:i.2=0): (Wp (β:ℂ) (G,0) i).2=0:=by
 have he:= s.real_I g v; let Q:=inwardP r i; let p:=intent1 (mem_ball_zero_iff.mp (s.half_room g))
 obtain ⟨r,_,_,_,_,_,q,-⟩:= house_real s.qL s.s s.Th s.S0 s.Ty s.coin.full pB Q.1 (by rw [← show Q= _ from he]; exact p)
 unfold multiplier stepV; rw [he]; change i.2+waveTest _ _ _ _= _; rw [q,←pointE,v,show StackL (0:RegBudget ι) univ=0 from map_zero (Fixed.Voltage.frame_P univ),map_zero,zero_add]
lemma real_pick (pB:Sch (β:ℂ) (G,0)): (s.pickW β (G,0)).2=0:=by
 let X(z:Eμ):= z.2; let F:= Wp (β:ℂ) (G,0); let f(k:ℕ):= F^[k] 0; let z:= s.pickW β (G,0); have h(i:ℕ): X (f i) = 0:=by
    induction i with | zero=> rfl | succ i t=> exact (congrArg X (iterate_succ_apply' F _ 0)).trans (s.real_aim pB (f i) ((s.march_Point pB).1.iterate _ s.zeroSubs) t)
 exact tendsto_nhds_unique ((continuous_snd.tendsto z).comp (s.sleepsW pB).2.2) (tendsto_const_nhds.congr (fun i=>(h i).symm))
lemma tests_set (pB:Sch y F) : let X:= Sx y F (s.pickW y F); Both (fun x=> waveTest Shf x K.j xm=0) X:= by
 intro X; obtain z:= (s.sleepsW pB).1.2; let W:= s.pickW y F; let t: (waveTest Shf X.1 K.j xm,waveTest Shf X.2 K.j xm)=(0,0):= add_eq_left.mp (show W + _= W from z); exact ⟨congrArg Prod.fst t,congrArg Prod.snd t⟩
end Shop
end Focus
end Pitching
end YM.CF.Py.Rate
