import Thin.Answer
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
variable (G:Morn K)(Rk:Diary)(F:∀ᶠ x in atTop,LampF G Rk (R0 x) (δ x) (C x) x N0 J q h) (t:Chill_v δ)(hc:∀ᶠ x in atTop, 0 ≤ δ x)
/-- Which transfer rule was purchased. Retains the actual Shop bank; including existence of
 canonical real proposals on all these stages (and complex-parameter arc grants).
 This additional detail is not required to bound the denominator. It exposes more about
 the prescription, e.g. for users of prepared-step comparison. -/
structure ShelfTh (G:Morn K) (Rk:Diary) (R0 δ C:ℝ→ℝ)(J:Robes N V W)(q:Chi)(h:ℝ)(P:Prescription R B)(N0:ℕ)(y:ℝ) :Prop where
 ships(m n:Side) (w:Location (R:=R) B m n)(x:ℝ)(p p':BudgetPoint): y≤x → Location.Request V U W J q w N0 x p p' →
    Capsule R x ∧ ∃ r:ℝ, 0<r ∧ r≤R0 x ∧ ∃ hR:Nonempty (ΘS r), letI := hR; ∃ Y:Shop w J p p' q h x r,Shop.Ready (δ x) (C x) Y ∧ P m n w x p p'=Y.operate ∧ Record G Rk J h x Y N0
-- `Service` alone suffices for the pressure theorem.
include F t hc
lemma supplyTh : ∃ (P:Prescription R B)(d:ℝ), Service V U W J q h δ C R0 P N0 d ∧ ShelfTh G Rk R0 δ C J q h P N0 d:=by
 obtain ⟨d,qT⟩:= eventually_atTop.mp (F.and (prolong (V:=V) t hc))
 have ξ (m n:Side)(w:Location (R:=R) B m n)(x:ℝ)(p p':BudgetPoint): ∃ P : Operation (mid m B) (mid n B),∀ [Nonempty (Haro.ΘS (R0 x))],d ≤ x → Location.Request V U W J q w N0 x p p' → ∃ S:Shop w J p p' q h x (R0 x),Shop.Ready (δ x) (C x) S ∧ P=S.operate ∧ Record G Rk J h x S N0:=by
    by_cases z:d ≤ x ∧ Location.Request V U W J q w N0 x p p'; swap
    · exact ⟨⟨0,0,0,0⟩,fun t v=>False.elim (z ⟨t,v⟩)⟩
    letI:=nonemp (R0 x) (qT x z.1).1.buys.le; obtain ⟨S,T,Mn⟩:= (qT x z.1).1.keeper _ _ w p p' z.2; exact ⟨S.operate,fun _ _=> ⟨S,T,rfl,Mn⟩⟩
 choose P hP using ξ
 refine ⟨P,d, ⟨fun m n w x p p' y hz=> ?_,?_⟩,?_⟩
 · letI:=nonemp _ (qT x y).1.buys.le; obtain ⟨T,w',v,_⟩:= hP m n w x p p' y hz; rw [v]; exact T.worn (s:=(qT x y).2) w'
 · intro m n w x x' p p' P₀ P₁ y y' hw hz b E E' v v' q1 q2 e1 e2 L L' Z Z' pΨ;
   let k:= (qT x y); let k':=(qT x' y'); letI:=nonemp _ k.1.buys.le; letI:=nonemp _ k'.1.buys.le
   obtain ⟨l,u,note,_⟩:=hP _ _ w _ _ _ y hw; obtain ⟨l',v',note',_⟩:=hP _ _ w _ _ _ y' hz; unfold Z Z' L L'; rw [note,note']
   exact l.prosper l' (submits k.2 q1 ⟨e1,Charged.zero.mono (show 0 ≤ 3* dleaf R.L x from mul_nonneg (by norm_num) k.2.high.le)⟩) (submits k'.2 q2 ⟨e2,Charged.zero.mono (show 0 ≤ 3*dleaf R.L x' from mul_nonneg (by norm_num) k'.2.high.le)⟩) pΨ hw hz
 constructor; intro m n w x p p' y hz
 let u := qT x y
 exact ⟨u.2,R0 x,u.1.buys, le_rfl,nonemp _ u.1.buys.le,haveI:= nonemp _ u.1.buys.le; hP m n w x p p' y hz ⟩

variable {G Rk}
omit F t hc
lemma ShelfTh.past {P:Prescription R B}{y:ℝ}(u:ShelfTh G Rk R0 δ C J q h P N0 y):CutFrom R0 δ C J q h P N0 y:=by
 constructor; intro m n w x p p' v ht; obtain ⟨a,i,g,k,hR,Z⟩:=u.ships m n w x p p' v ht; letI:=hR; obtain ⟨b,x,c,m'⟩:=Z
 exact ⟨a,i,g,k,hR,b,x,c⟩
lemma ShelfTh.mono {R0' δ':ℝ→ℝ}{P:Prescription R B}{y y':ℝ}(u:ShelfTh G Rk R0 δ C J q h P N0 y)(v:y≤y')(ht:R0≤R0')(g:δ ≤ δ'):ShelfTh G Rk R0' δ' C J q h P N0 y':=by
 constructor; intro m n w x p p' t a; obtain ⟨M,i,ip,k,hR,Y⟩:=u.ships m n w x p p' (v.trans t) a; letI:=hR; obtain ⟨b,z,c,mh⟩:=Y
 exact ⟨M,i,ip,k.trans (ht x),hR,b,{z with gold:=z.gold.trans (g x)},c,mh⟩
lemma ShelfTh.bright {P:Prescription R B}{y:ℝ}(u:ShelfTh G Rk R0 δ C J q h P N0 y)(e:G.After R){m n:Side}{x:ℝ}(w:Location (R:=R) B m n)(p p':BudgetPoint)(t:y ≤ x)(l:Location.Request V U W J q w N0 x p p')(Fv:Corr (mid n B))(ℓ:ℂ)(hi:enters (x+billX R.L) (β:ℂ))(hF:Charged p' w.input K.j R.L.val h (3*dleaf R.L x) Fv): brightAll (q:=q) (V:=V) (U:=U) (J:=J) G Rk (P m n w x p p') w p p' x h β Fv ℓ:=by
 obtain ⟨a,i,v,H,hR,z⟩:=u.ships m n w x p p' t l; letI:=hR; obtain ⟨b,c,k,M⟩:=z
 rw [k]; exact M.questions e a Fv ℓ hi hF
end Focus
end Pitching
end YM.CF.Py.Rate
