import YM.CF.Vp929.Stage.Menu
import YM.CF.Vp929.Canon.Knit
import YM.CF.Vp929.Contour.Chute
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
structure Shop (w:Location (R:=R) B m n) (J: Robes N V W)(p p':BudgetPoint)(q:Chi)(h x r:ℝ)[Nonempty (ΘS r)] where
 Wk:ℝ
 Aχ:ℝ
 Γχ:ℝ
 ψ₁:ℝ
 ψ₂:ℝ
 θ₁:ℝ
 θ₂:ℝ
 ξ₁:ℝ
 ξ₂:ℝ
 u0:ℝ
 Ep:ℝ
 Ek:ℝ
 Ea:ℝ
 Λf:ℝ
 b0:ℝ
 b1:ℝ
 b2:ℝ
 b3:ℝ
 Lp:Depot (Scree.mid m B) (Scree.mid n B)
 qL : Lobby x h K w p p' J.n Lp u0 Ep Ek Ea
 A0:Stakehouse (h:=h) p J w b0 b1 b2 r
 n₀:ℕ
 s: Major V Wk b0 b1 b2 b3 Aχ Γχ n₀
 Th: Mood p (512*Wk) h b0 (Tenant.quota^2*b1) (Tenant.quota^2*b2) r (Scales.g SU.group R.L x) Ep Ek u0 (rainX R 1 x) (rainX R 2 x) Λf ψ₁ θ₁ ξ₁ ψ₂ θ₂ ξ₂
 S0: Cease p (V.L.path (w.lag+1)) K.top.clip Aχ Γχ K.below.width K.below.paths V.W.bar (Scree.mid m B)
 Ty: Ids (Scree.mid m B)
 t:0 ≤ u0
 Sh:ℝ
 v:ℝ
 m₁:ℝ
 C:ℝ
 coin:Cycle929.Coin p θ₂ ((rainX R 2 x)⁻¹ * ψ₂) Sh (rainX R 2 x) v
 pH:2*((Ea+ηF p R K Γχ Λf)+m₁) ≤ Sh
 Mp:Mantel J p p' x C q Lp w A0
 GraspY: Frequency R.L (mid m B) w.freq
 RatioCZ: rollGX K.j s.k R.L.val (houseP p K Aχ Γχ Λf) h ≤ r/256
 shape:Vast R.L.val p.B (mid m B)
 size:4≤(More (mid m B)).val
 ownership:p=epoch x
 paid: priceYT K.top.clip K.j s.k R.L.val p (houseP p K Aχ Γχ Λf) (shipT p R.L.val K.top.clip K.below.width K.below.paths Aχ Γχ) ≤ m₁
 solv: 0 ≤ m₁
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
def inwardP(r:ℝ)[Nonempty (ΘS r)](V:Pair ↥SpaceM):Pair (ΘS r):=(inward V.1 r,inward V.2 r)
lemma intent0 (x:Pair ↥SpaceM)(p:‖x‖ ≤ r): bearer (inwardP r x)=x:=by
 have hp:= (norm_fst_le x).trans p; have ht:= (norm_snd_le x).trans p; unfold bearer inwardP inward; rw [dif_pos hp,dif_pos ht]
lemma intent1 {i:Eμ}(u:‖i‖<r): sunny (inwardP r i):=by obtain e:=intent0 i u.le; change ‖(bearer _).1‖ <r ∧ ‖(bearer _).2‖ < r; rw [e]; exact ⟨(norm_fst_le i).trans_lt u,(norm_snd_le i).trans_lt u⟩
def stepV (b:ℂ)(F:Pair (Corr ηt))(p: Eμ): Pair (RegBudget ι) := VE (inwardP r p) b F
def multiplier (b:ℂ)(F:Pair (Corr ηt))(u:Eμ): Pair (SpaceM:Type) := u + (waveTest Shf (s.stepV b F u).1 K.j xm, waveTest Shf (s.stepV b F u).2 K.j xm)
local notation "Wp"=> s.multiplier
local notation "Sx"=> s.stepV
include s

lemma ceiling {F:Pair (Corr (mid n B))}(pB:Sch y F){q:Eμ}(hp:‖q‖<r) : ‖s.multiplier y F q‖ ≤ r/128:=by

 let i:= inwardP r q; obtain h':=intent1 hp; obtain ⟨⟨a,b⟩,u,-⟩:= house_r s.qL s.s s.Th s.S0 s.Ty _ pB (inwardP r q) h'; obtain ⟨⟨xz,k⟩,-⟩:= (inkwell s.qL s.s s.Th s.Ty _ i h' pB).1; let F0:=Sx y F q
 obtain ⟨v,t',w⟩:= (show p.order=6 ∧ p.power=2 ∧ p.supportExponent=1 from s.ownership.symm ▸ let_X HI x)
 let Sh:Finset (Scree.Hub ι):= sx; obtain ⟨p',q'⟩:= u Sh
 let χ:= Shf; let ρ:= xT; let FT:=EkX i y F; let Fx_:= Ex i y F
 have he (z: μ)(j:ΘS r)(t:z=j.val)(E A B: RegBudget ι)(v:IncX Utrue E p h φE)(B':B=A+(dr).ler j)(Z:StackL E Sh=StackL B Sh)(hg:IncX Utrue A p h (κAge p s.u0 h s.b0 s.b1 s.b2 r (Scales.g SU.group R.L x))): ‖z+waveTest χ E K.j xm‖ ≤ r/128:=by
    let Q:= ρ (StackL E Sh); let x:=ρ (StackL A Sh)
    have h':AxisP (heroP (StackL A Sh)):= (gem (plea ι p _) hg (dr).floor t' s.s.k xm 0 fun i _=> Nat.zero_le _).axisP
    have hx:‖waveTest χ E K.j xm-Q‖≤ r/256:= (cake s.s.k w t' v (dr).floor s.GraspY).trans s.RatioCZ
    have hk: ‖x‖ < r/256:=by change ‖(pointW _ _ _ _ (StackL A Sh)).val‖<_; rw [pointCash s.s.k h']; exact ((dr).latticeFieldEstimates s.Th A hg sx (plea ι p _) s.s.lens K.j s.s.k xm s.t).2
    have hu: z+Q=x:=by unfold Q; rw [Z,B',mark_T,map_add]; rw [show ρ _ = - j.val from getS (dr) s.s.k j (teal ι p _ s.s.head),←t]; unfold x; abel
    rw [show z+waveTest χ E K.j xm=x+(waveTest χ E K.j xm-Q) from (by rw [← hu]; abel)]
    exact (norm_add_le ..).trans ((add_le_add hk.le hx).trans_eq (by ring))
 apply max_le; exact he q.1 i.1 (congrArg Prod.fst (intent0 q hp.le).symm) F0.1 Fx_.1 FT.1 a.1 rfl p' xz; exact he q.2 i.2 (congrArg Prod.snd (intent0 q hp.le).symm) F0.2 Fx_.2 FT.2 b.1 rfl q' k
lemma logic_wave : Logic p h (fun T:RegBudget ι=> waveTest Shf T K.j xm):=by exact Logic.comp (pointC _ _ _ _) (cw_bear (subset_univ _))
lemma stepHolo {F:ℂ→Pair (Corr (mid n B))}{b:ℂ→ℂ}(A:Arcμ x h p' w K S b F){i:ℂ→ Eμ}(g:Form S i)(pI: Set.MapsTo i S (ball 0 r)): Form S (fun z=> s.multiplier (b z) (F z) (i z)):=by
 let q(z:ℂ): Pair (ΘS r):=inwardP r (i z); have hp(u)(v:u∈ S):‖i u‖ < r:= mem_ball_zero_iff.mp (pI v); have hx:Scen S q:= g.congr (fun x v=> intent0 _ (hp x v).le); let X(z:ℂ):= VE (q z) (b z) (F z)
 let u:= s.logic_wave; have ht:Valid (DuesQ Utrue p h) Py.Rate.Census S X:= ⟨A.openT,(house_query s.qL s.s s.Th s.S0 s.Ty F b _ A hx (fun u v=> intent1 (hp _ v))).1,φE,fun z p=>by obtain ⟨x,v⟩:= (house_r s.qL s.s s.Th s.S0 s.Ty _ (A.legal _ p) (q z) (intent1 (hp z p))).1; exact ⟨x.1,v.1⟩⟩; exact g.add (Logic.travel ht u)
end Shop
end Focus
end Pitching
end YM.CF.Py.Rate
