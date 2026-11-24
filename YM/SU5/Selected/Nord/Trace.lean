import YM.SU5.Selected.Nord.Comp
set_option autoImplicit false
set_option maxHeartbeats 1200000
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
open Ione Beau Haro Cascade Fief VolumeRate Branch
open scoped Mew
variable {K : Teller SU.group} {R : Patch} {L : ChartRatio SU.group} {V : Grace K R L} {d h x z : ℝ} {D C R0 : ℝ → ℝ} (h' : ℝ) {delay : ℝ} {m N B : Side} {U : Grasp V.U B d} {W : GivenX V U} {J : Robes N V W} {N0 B1 : ℕ} {q : Chi}
variable {n T' : ℕ → ℕ} {P : Prescription R B}
namespace LocalLimit
open Preparation Chene Pitching Focus
variable {Λ:Preparation}{Z:(s:Side)→ Scree.Loom s → Prop} (Y: Course Λ Z)(Q:Scooped Λ)
local notation "Y_" i:max=> hat Λ.R.L Λ.x i
private abbrev Arc (i k:ℕ):= Actual Y.meter (Y.voyage i).funds (Y.voyage i).CapeT (gaugeFreq Λ (Y.tile*Λ.M)) (Y.uv k)
private abbrev Loc (s i k:ℕ) := (Arc Y i k).toSpine.address s
local notation "Yc" => Λ.P
include Q
lemma plumage (ε D:ℝ)(pε:0<ε): ∀ᶠ s in atTop,∀ i k,s<Y.uv k → ∃ (T: Monk SU.group (Stem Y i k s)),∃ z≥ D, |(RootBook Y i k s).v.re-(RootBook Y i k (s+1)).v.re-jumpT Λ.V Λ.U (Loc Y s i k) (Y_ s) (RootBook Y i k (s+1)).beta z T| ≤ ε*sites (Λ.Ctor (Y.ir i) s):=by
 filter_upwards [(turnover Λ).eventually (Q.sharper.supply ε D pε)] with s p i k h
 let T:=Y.voyage i; let F0:=Arc Y i k; let F:= T.X (Y.uv k); let X:=Loc Y s i k; let v:= Q.from_cut; let H:=T.paths (Y.uv k); let H':= H.paid; obtain ⟨b,hB,S,hS⟩:= H.issued; have hu: RootBook Y i k= Branch.gram Yc F0 b:= S
 let f:= ((Y_ s)); let hR:= H'.request s h
 obtain ⟨c,r,r₀,hA,hn,A,Tp,hs⟩:= v.ships (mesh (Y.ir i) Λ.R.L s) (mesh (Y.ir i) Λ.R.L (s+1)) X f (Y.meter.a s) (Y.meter.a (s+1)) (H'.late.trans (Vale.crown ..)) hR
 let Y₀:=(RootBook Y i k s); let Y' := RootBook Y i k (s+1); let v':=(F0.gram Yc b (s+1)).beta; let V:= F0.chargeLevel Yc b (s+1); let B':=F0.offset Yc b (s+1)
 let p₀:= H'.beta_ok Λ.H hB.toRealQ (s+1) h
 let E:= H'.flow (H'.charged Λ.H hB.toRealQ (s+1) h)
 letI:= hn
 have ha: AngleDesk D A.operate X f v' V B' ε Λ.J:= p.law _ _ _ _ _ hR r A _ _ Tp c _ _ B' (hat_step s ▸ p₀.2) E -- check `.law` [Nonempty] bankers.
 rw [hu]; obtain ⟨T,hZ,q,hQ⟩:=ha
 refine ⟨T,hZ,q,?_⟩
 change |(F0.offset Yc b s).re-B'.re-jumpT Λ.V Λ.U X f v' hZ T| ≤ _
 rw [show F0.offset Yc b s= A.operate.offset v' V B' from ?_]; exact hQ
 rw [Branch.offset.eq_1,dif_pos h]; change (Λ.P _ _ X f _ _).offset _ _ _= _; rw [hs]

abbrev replacement (i k s:ℕ):ℝ:= Cour.shipA (apt (Y.ir i) Λ.block Λ.R.L s) Λ.U (RootBook Y i k (s+1)).J.M (RootBook Y i k (s+1)).J.P.den (RootBook Y i k (s+1)).J.I (RootBook Y i k s).J.I (1,1) |>.re
omit Q
private lemma retroplot (i k s:ℕ)(h:s<Y.uv k) : replacement Y i k s= retro Λ.V Λ.U (Loc Y s i k):=by
 obtain ⟨t,hT,hq,-⟩:= ((Y.voyage i).paths (Y.uv k)).issued; rw [replacement, show RootBook Y i k= (Arc Y i k).gram Yc t from hq]; rfl
lemma volumesBB(S:Side):Perks.bulk (More S)=sites S:=by unfold Perks.bulk sites; rw [site_card,Nat.cast_pow]
include Q
lemma truthUp (ε:ℝ)(pε:0<ε): ∀ᶠ s in atTop,∀ i k,s<Y.uv k → let H:=RootBook Y i k s; let K:=RootBook Y i k (s+1); let l:= HighAge Y s k; let x:=Λ.V.L; let m:=sites (Λ.Ctor (Y.ir i) (s+1)); |H.v.re-K.v.re - (Perks.schedule Λ.L (More (Λ.Ctor (Y.ir i) (s+1))) (x.H l) K.beta-Perks.schedule Λ.L (More (Λ.Ctor (Y.ir i) s)) (x.H (l+1)) H.beta-replacement Y i k s)| ≤ ε*m:=by
 let h:=ε/2; have hx:0<h:=half_pos pε; obtain ⟨A,v,g⟩:=grainPrice Y h hx
 filter_upwards [plumage Y Q h A hx,g] with s v w i k u
 obtain ⟨X,b,t,H⟩:= v i k u; have he:=(w i k u X b t).2; rw [retailG] at he; unfold jumpT at H; intro a c l x m; let d:=(retro Λ.V Λ.U (Loc Y s i k)); let V:= Λ.Ctor (Y.ir i); let B:=Perks.tariff Λ.L (Peck Y i k s) X.park X.k c.beta (Y_ s) b; let C:=Perks.schedule Λ.L (More (V (s+1))) (x.H l) c.beta; let D:=Perks.schedule Λ.L (More (V s)) (x.H (l+1)) a.beta
 rw [retroplot Y i k s u]; change |a.v.re-c.v.re-(C-D-d)| ≤ ε*m; change |a.v.re-c.v.re-(B-d)| ≤ h*sites (V s) at H; rw [volumesBB] at he; change |B-(C-D)| ≤ h*m at he; have hv: Perks.bulk (More (V s))≤ Perks.bulk (More (V (s+1))):= Perks.stem (Stem Y i k s); rw [volumesBB, volumesBB] at hv; have hl: sites (V s) ≤ m := hv; rw [abs_le] at H he ⊢; have ht:h*m=ε*m/2:=by unfold h; ring
 have he':= mul_le_mul_of_nonneg_left hl hx.le; constructor <;> linarith only [he',ht,H.1,H.2,he.1,he.2]
end LocalLimit
end YM.CF.Py.Rate
#print axioms YM.CF.Py.Rate.LocalLimit.truthUp
