import Finch.Bra
import YM.SU5.Exchange.Pace.Cult
import YM.SU5.Interaction.Source

set_option autoImplicit false
set_option maxHeartbeats 150000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
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
open Chaff Gloss Maize Tye RP RP.Str Oise
namespace LocalLimit

namespace Preparation
open FullBill Window Marks
open Swell Buffered
open Vow.TreasuryFog Sour

section
variable {I:Type*}[LinearOrder I][Fintype I]{S S':Finset I}{X Y:FC I}
lemma disjoint_even_moves (p:Sector S false X)(q:Sector S' false Y)(v:Disjoint S S'): X*Y=Y*X:=by
 have h:= p.apart q v; rwa [show Fock.Sector.grainB false false=(1:ℂ) from rfl,one_smul] at h

end

variable {P:Preparation}{F:(s:Side)→Scree.Loom s→Prop}(Y: Course P F)
-- For purchases on this course, exact opening notion, actual scaling demanded on inputs
local notation "Ng" i:max s:max => (P.Ctor (Y.ir i) s)
local notation "A" i:max s:max => (Y.voyage i).CapeT s
local notation "S" i:max k:max s:max=> RootBook Y i k s
variable (i k s m:ℕ)
structure FullInsertion (i k s:ℕ)(o:Site (Ng i s)) (q p₀ c:ℝ)(W:Sa (Ng i s))
    (Z:Evaluation (Ng i s))(M: phy (Ng i s))(L: Sour.Bag (Ng i s)) : Prop where
 tagW : NativeMark W Z c
 seed : Nest P.U (S i k s) (A i s) P.J.n 24 (node o) P.h (rScale (S i k s).p) M L q p₀
 stakeX (x:Orbit (Ng i s)) : Sector (modesIn (Ng i s) W) false (M x)
 bra (x:Orbit (Ng i s)): acts (star (M x)) (mateK (Ng i s))=acts (star (Z x.1)) (mateK (Ng i s))

abbrev liftedOrbit {s:Side}(F:Evaluation s) : Tagged s := fun x=> F x.1
omit Y i k s in
lemma NativeEnv {N:Side}{F:Evaluation N}{B:Sa N}{c:ℝ}(p:NativeMark B F c):
    RG.Envelope (liftedOrbit F) :=by
 let t(x:Orbit N) :Fields N:=(x.1,x.1)
 -- Marks scopes instance clashes
 exact Env.along (show RG.Envelope (toMark F) from p.foot.env) (g:=t) (measurable_fst.prodMk measurable_fst)

variable {i k s}
local notation "G" => S i k s
local notation "a'"=> A i s
local notation "ν"=> Ng i s
local notation "Wℓ" v:max=> pilotH P.U G a' v (projects_here Y i k s v |>.1)
-- charged symbol pairing for physical operator. Spectators may be dressed, may use separate Costs.
def birthReading (i k s:ℕ)(B: Tagged (Ng i s))(L: Sour.Bag (Ng i s))(x: Orbit (Ng i s)):ℂ :=
 Marks.read B x (pilotH P.U (S i k s) (A i s) x (projects_here Y i k s x |>.1)
   (acts (∑ i':Vow.Aura (Ng i s), L i' x) (Cadre.poseL _ (fueled (S i k s).p (S i k s).K x))))
variable {Z:Evaluation (P.Ctor (Y.ir i) s)}{M:phy (P.Ctor (Y.ir i) s)}{L:Bag (P.Ctor (Y.ir i) s)}{c q p:ℝ}{D:Sa (P.Ctor (Y.ir i) s)}{o:Site (P.Ctor (Y.ir i) s)}
variable (pX:FullInsertion Y i k s o q p c D Z M L)
include pX
lemma open_read {B: Tagged (Ng i s)}(x: Orbit (Ng i s)){U:Sa (Ng i s)} (h:Sector (modesIn (Ng i s) U) false (B x)) (t:Disjoint D U) : Marks.read (B*liftedOrbit Z) x (denZ G P.U a' x)=birthReading Y i k s B L x:=by
 let T:=mateK (Ng i s); have f: Disjoint (modesIn ν U) (modesIn ν D):= Finset.disjoint_left.mpr fun j h v=>Finset.disjoint_left.mp t ((modes_at ..).mp v) ((modes_at ..).mp h)
 let d:=denZ G P.U a' x; have w: Sector (modesIn ν D) false (Z x.1):=(pX.tagW.foot.allV ((x.1,x.1):Fields ν)).sector
 have e := pX.seed.science x (projects_here Y i k s x |>.1)
 have he : denZ G P.U a' x= (Wℓ x) (Cadre.poseL _ (fueled (G).p (G).K x)) := by
    have hy:=showUp (R:=G) P.U a' x (projects_here Y i k s x|>.1) 0 (G).K; rw [show exponentL (G).p 0 x.1=0 from by simp [exponentL,numbE], exp_zero,one_mul,add_zero] at hy; exact hy
 unfold birthReading Marks.read; simp only [ContinuousLinearMap.comp_apply,innerSL_apply_apply] -- tune
 change inner ℂ T (acts (B x*Z x.1) _)= inner ℂ T (acts (B x) _)
 rw [disjoint_even_moves h w f,show pilotH _ _ _ _ _ _= _ from e (Cadre.poseL _ (fueled (G).p (G).K x)), ← he,←act_mul,disjoint_even_moves h (pX.stakeX x) f, act_mul,act_mul,←act_inner (Z x.1),←act_inner (M x), pX.bra]
 -- e _ apply arity tune
-- exact equality of normalized price, eligible denominators. No claim small price in arbitrary geometry.
lemma integrates_full {B: Tagged (Ng i s)}{U:Sa (Ng i s)} (h:∀ x, Sector (modesIn (Ng i s) U) false (B x)) (t:Disjoint D U) (l:(Y.voyage i).kick ≤ k)(w:s≤ Y.uv k)(v:RG.Envelope B) : partitionZ G P.U a'≠0 ∧ Integrable (birthReading Y i k s B L) (city (Ng i s)) ∧ Marks.ratio P.V P.U G a' (B*liftedOrbit Z)= (∫ x,birthReading Y i k s B L x ∂city ν)/(partitionZ G P.U a'):=by
 let X:=Y.each_level i k s l w; have hx: (fun x=> Marks.read (B*liftedOrbit Z) x (denZ G P.U a' x))= _ := (funext fun x=> open_read Y pX x (h x) t)
 refine ⟨X.valid,hx ▸ Marks.read_int _ (Marks.can_read P.V P.U (S i k s) _ X) ?_, ?_⟩ -- tune positivity via valid
 · exact env_mult v (NativeEnv pX.tagW)
 unfold Marks.ratio Marks.evaluate; rw [hx]
-- scale families
lemma FullInsertion.dress (w:ℂ): FullInsertion Y i k s o (‖w‖*q) (‖w‖*p) (‖w‖*c) D (w • Z) (w • M) (w • L) := by
 refine ⟨pX.tagW.smul _, nestScale P.U G a' w pX.seed, fun i=> (pX.stakeX i).scale w, fun x=> ?_⟩; rw [Pi.smul_apply,Pi.smul_apply,star_smul,star_smul,act_smul, act_smul,pX.bra]
end Preparation
end LocalLimit
end YM.CF.Py.Rate
