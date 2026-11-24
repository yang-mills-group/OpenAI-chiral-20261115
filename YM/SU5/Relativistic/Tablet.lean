import YM.CF.Vp929.Stage.Plant
import YM.SU5.Relativistic.GlobalF
import YM.CF.Vp929.Stage.Manufacture
import YM.CF.Vp929.Stage.Shore
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
private lemma nonempR(t:ℝ)(h:0 ≤ t):Nonempty (Haro.ΘS t):= ⟨⟨0,(norm_zero |>.trans_le h)⟩⟩
private lemma late (X:ℝ→ℝ→Prop)(h:∀ ε> (0:ℝ), ∀ᶠ x:ℝ in atTop,X ε x):∃ E:ℝ→ℝ,Tendsto E atTop (𝓝 0) ∧ ∀ᶠ x:ℝ in atTop, X (E x) x:=by
 let CΩ(i:ℕ):ℝ:=(i+1:ℝ)⁻¹; have he:Tendsto CΩ atTop (𝓝 0):=tendsto_inv_atTop_zero.comp (tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop)
 have ht(i:ℕ):∃ Ω:ℝ,i≤Ω∧ ∀ x,Ω≤x→X (CΩ i) x:=by obtain ⟨a,h⟩:= eventually_atTop.mp (h (CΩ i) (by unfold CΩ; positivity)); exact ⟨max i a,le_max_left ..,fun x p=> h x ((le_max_right ..).trans p)⟩
 choose Ω t w using ht; let L(x:ℝ):= (Finset.range (Nat.ceil x + 1)).filter fun i=> Ω i≤ x -- syntax nat ceil
 have hm(x:ℝ)(hi:Ω 0≤x): (L x).Nonempty:= by refine ⟨0,mem_filter.mpr ⟨mem_range.mpr (by omega),hi⟩⟩
 let V(x:ℝ):= if h:Ω 0≤x then (L x).max' (hm x h) else 0
 refine ⟨CΩ ∘ V,he.comp (tendsto_atTop.mpr ?_),?_⟩
 · intro b; filter_upwards [eventually_ge_atTop (Ω 0),eventually_ge_atTop (Ω b)] with i h k; have he: b∈ L i:= mem_filter.mpr ⟨mem_range.mpr (Nat.lt_succ_of_le (by exact_mod_cast ((t b).trans (k.trans (Nat.le_ceil _))))),k⟩; unfold V; rw [dif_pos h]; exact le_max' _ _ he
 filter_upwards [eventually_ge_atTop (Ω 0)] with x h; unfold Function.comp V; rw [dif_pos h]; exact w _ x ((mem_filter.mp (max'_mem _ (hm x h))).2)
variable (F:∀ ε> (0:ℝ),∀ᶠ x in atTop,Tabloid ε (R0 x) (δ x) (C x) x N0 J q h) (t:Chill_v δ)(hc:∀ᶠ x in atTop, 0 ≤ δ x)
-- arc certificate on any high requests at this chosen Shop.
structure FairRoute (P:Prescription R B)(J:Robes N V W)(h:ℝ)(N0:ℕ)(q:Chi):Prop where
 owes (ε:ℝ)(p:0<ε):∀ᶠ x:ℝ in atTop,∀ {m n:Side}(w: Location (R:=R) B m n) {p p':BudgetPoint},w.Request V U W J q N0 x p p' → TapGold h ε w p p' x V (P m n w x p p')
include F t hc
lemma supplyQ : ∃ (P:Prescription R B)(d:ℝ), Service V U W J q h δ C R0 P N0 d ∧ CutFrom R0 δ C J q h P N0 d ∧ FairRoute P J h N0 q:=by
 obtain ⟨f,hf,F⟩:=late _ F
 obtain ⟨d,qT⟩:= eventually_atTop.mp (F.and (prolong (V:=V) t hc))
 have ξ (m n:Side)(w:Location (R:=R) B m n)(x:ℝ)(p p':BudgetPoint): ∃ P : Operation (mid m B) (mid n B),∀ [Nonempty (Haro.ΘS (R0 x))],d ≤ x → Location.Request V U W J q w N0 x p p' → ∃ S:Shop w J p p' q h x (R0 x),Shop.Ready (δ x) (C x) S ∧ P=S.operate ∧ TapGold h (f x) w p p' x V P:=by
    by_cases z:d ≤ x ∧ Location.Request V U W J q w N0 x p p'; swap
    · exact ⟨⟨0,0,0,0⟩,fun t v=>False.elim (z ⟨t,v⟩)⟩
    letI:=nonempR (R0 x) (qT x z.1).1.hi.le; obtain ⟨S,T,M⟩:= (qT x z.1).1.ready _ _ w p p' z.2; exact ⟨S.operate,fun _ _=> ⟨S,T,rfl,M⟩⟩
 choose P hP using ξ
 refine ⟨P,d, ⟨fun m n w x p p' y hz=> ?_,?_⟩,?_⟩
 · letI:=nonempR _ (qT x y).1.hi.le; obtain ⟨T,w',v,G⟩:= hP m n w x p p' y hz; rw [v]; exact T.worn (s:=(qT x y).2) w'
 · intro m n w x x' p p' P₀ P₁ y y' hw hz b E E' v v' q1 q2 e1 e2 L L' Z Z' pΨ;
   let k:= (qT x y); let k':=(qT x' y'); letI:=nonempR _ k.1.hi.le; letI:=nonempR _ k'.1.hi.le
   obtain ⟨l,u,note,-⟩:=hP _ _ w _ _ _ y hw; obtain ⟨l',v',note',-⟩:=hP _ _ w _ _ _ y' hz; unfold Z Z' L L'; rw [note,note']
   exact l.prosper l' (submits k.2 q1 ⟨e1,Charged.zero.mono (show 0 ≤ 3* dleaf R.L x from mul_nonneg (by norm_num) k.2.high.le)⟩) (submits k'.2 q2 ⟨e2,Charged.zero.mono (show 0 ≤ 3*dleaf R.L x' from mul_nonneg (by norm_num) k'.2.high.le)⟩) pΨ hw hz
 constructor; swap
 · constructor; intro ε e; filter_upwards [hf.eventually (ge_mem_nhds e),eventually_ge_atTop d] with x u v m n w p p' hz; letI:=nonempR _ (qT x v).1.hi.le; obtain ⟨Y,_,_,Q⟩:= hP m n w x p p' v hz; exact ⟨fun a b e c q=> (Q.faith a b e c q).trans (mul_le_mul_of_nonneg_right u (zero_le_one.trans (sites_pos _)))⟩
 constructor; intro m n w x p p' y hz
 let u := qT x y
 exact ⟨u.2,R0 x,u.1.hi, le_rfl,nonempR _ u.1.hi.le,haveI:= nonempR _ u.1.hi.le; let X:= hP m n w x p p' y hz; ⟨_,X.choose_spec.1,X.choose_spec.2.1⟩ ⟩
end Focus
end Pitching
end YM.CF.Py.Rate
