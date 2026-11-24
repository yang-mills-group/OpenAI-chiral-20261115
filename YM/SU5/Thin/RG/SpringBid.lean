import YM.SU5.Thin.RG.SpringYear
import YM.CF.Vp929.Ledger.Yole
/-! Enriched chronological purchase. Adapt Plant; then pass through the
Granger proof of `nowAppointment` and `joinPermit`. -/
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
variable {R0 δ C: ℝ→ℝ}{N0:ℕ}
local notation "Θ"=> mid n B
private lemma nonemp(t:ℝ)(h:0 ≤ t):Nonempty (Haro.ΘS t):= ⟨⟨0,(norm_zero |>.trans_le h)⟩⟩
variable {b0 b1 b2 Bv kC hℓ:ℝ}{n₁:ℕ}{X Fq oμ Dκ Sh:ℝ→ℝ}{pW:WindV K.j 2}
variable (F:∀ᶠ x in atTop, Speck D c pW x (R0 x) (δ x) (C x) N0 ag Cg Bv n₁ (X x) (Fq x) b0 b1 b2 (Sh x) kC hℓ (oμ x) (Dκ x))
variable (R1:sizeK R.L 2 R0)(Z'S:Chill_v Sh)(hp0:0<b0)(Hs:MarkForesee D c X Fq pW ag Cg Bv n₁ kC HI hℓ oμ Dκ)(t:Chill_v δ)(hc:∀ᶠ x in atTop, 0 ≤ δ x)
include R1 Z'S hp0 Hs
include F t hc
lemma bidding : ∃ (P:Prescription R B)(d:ℝ), Service V U W J q h δ C R0 P N0 d ∧ CutFrom R0 δ C J q h P N0 d ∧ PulseMemo kC Pay J q h P N0:=by
 obtain ⟨d,qT⟩:= eventually_atTop.mp (F.and (prolong (V:=V) t hc))
 have ξ (m n:Side)(w:Location (R:=R) B m n)(x:ℝ)(p p':BudgetPoint): ∃ P : Operation (mid m B) (mid n B),∀ [Nonempty (Haro.ΘS (R0 x))],d ≤ x → Location.Request V U W J q w N0 x p p' → ∃ S:Shop w J p p' q h x (R0 x),Shop.Ready (δ x) (C x) S ∧ P=S.operate ∧ RootPond x h (R0 x) N0 w p p' J D c pW ag Cg Bv n₁ (X x) (Fq x) b0 b1 b2 (Sh x) kC hℓ (oμ x) (Dκ x) S:=by
    by_cases z:d ≤ x ∧ Location.Request V U W J q w N0 x p p'; swap
    · exact ⟨⟨0,0,0,0⟩,fun t v=>False.elim (z ⟨t,v⟩)⟩
    letI:=nonemp (R0 x) (qT x z.1).1.value.le; obtain ⟨S,T,xT⟩:= (qT x z.1).1.expense _ _ w p p' z.2; exact ⟨S.operate,fun _ _=> ⟨S,T,rfl,xT⟩⟩
 choose P hP using ξ
 refine ⟨P,d, ⟨fun m n w x p p' y hz=> ?_,?_⟩,?_,?_⟩
 · letI:=nonemp _ (qT x y).1.value.le; obtain ⟨T,w',v,_⟩:= hP m n w x p p' y hz; rw [v]; exact T.worn (s:=(qT x y).2) w'
 · intro m n w x x' p p' P₀ P₁ y y' hw hz b E E' v v' q1 q2 e1 e2 L L' Z Z' pΨ;
   let k:= (qT x y); let k':=(qT x' y'); letI:=nonemp _ k.1.value.le; letI:=nonemp _ k'.1.value.le
   obtain ⟨l,u,note,_⟩:=hP _ _ w _ _ _ y hw; obtain ⟨l',v',note',_⟩:=hP _ _ w _ _ _ y' hz; unfold Z Z' L L'; rw [note,note']
   exact l.prosper l' (submits k.2 q1 ⟨e1,Charged.zero.mono (show 0 ≤ 3* dleaf R.L x from mul_nonneg (by norm_num) k.2.high.le)⟩) (submits k'.2 q2 ⟨e2,Charged.zero.mono (show 0 ≤ 3*dleaf R.L x' from mul_nonneg (by norm_num) k'.2.high.le)⟩) pΨ hw hz
 · constructor; intro m n w x p p' y hz; let u := qT x y
   letI := nonemp _ u.1.value.le; obtain ⟨T,w',v,_⟩:= hP m n w x p p' y hz
   exact ⟨u.2,R0 x,u.1.value,le_rfl,inferInstance,T,w',v⟩
 refine ⟨⟨A,C',ρ,D,c,X,Fq,R0,Sh,ag,Cg,Bv,n₁,b0,b1,b2,hℓ,oμ,Dκ,pW,hp0,Z'S,R1,Hs,?_⟩⟩
 filter_upwards [eventually_ge_atTop d] with x y; let t:= qT x y
 letI := nonemp _ t.1.value.le
 refine ⟨t.2,t.1.value,fun m n w p p' hz=>?_⟩; obtain ⟨T,w',v,F₀⟩:= hP m n w x p p' y hz; exact ⟨inferInstance,T,v,F₀⟩

omit R1 Z'S hp0 Hs F t hc

end Focus
end Pitching
end YM.CF.Py.Rate