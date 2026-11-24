import YM.CF.Vp929.Kinematic.Pencils
import YM.CF.Vp929.Kinematic.Lid
import YM.CF.Vp929.Analysis.RealLevel
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
local notation "G5"=> SU.group
local notation "S'"=> w.step V
local notation "y"=> Scales.y SU.group R.L x
local notation "ι" => Scree.mid m B
local notation "η" => Scree.mid n B
local notation "z'" => (coming D.Z 105 5*radiusB x)
variable {o : Pitching w D x}
local notation "Bs" v:max F:max => base (q:=q) (J:=J) (w:=w) p' v F
local notation "Ys" β:max F:max=> Pitching.input (V:=V) (w:=w) p' β F
local notation "Xs" β:max => Pitching.start (V:=V) (w:=w) p β
local notation "A'"=> o.muster
local notation "P'"=> D.pilot
local notation "Up" v:max=> (tint_z o.muster v)
local notation "Jq"=> (w.Φ (V:=V))
namespace Lid
variable (H: Lid o p p' f)
variable {F F': Corr (Scree.mid n B)}
local notation "τ"=> radiusB x
variable (Mk: Monk SU.group (w.step V))(A₀:Ids (Scree.mid m B))(T₁:Ids (Scree.mid n B))
local notation "Rc" v:max=> poleY Mk v (Scales.y SU.group R.L x)
local notation "Δ" => (o.muster.post+90)*radiusB x
local notation "Δ₀"=> (D.pilot.hat R x)
local notation "χ"=> (shotM o.muster.vita)
local notation "Tσ"=> (vast (k:=D.Z.N1*τ) A')
local notation "mu"=> Cipher ι
private lemma axis_flour {w:ℝ}{S:Finset (Dwell m)} {E:ℂ→ Cipher m} (h:Differentiable ℂ E)(q:∀ᶠ (t:ℝ) in 𝓝 w, Flour S (E t).val) (z:ℂ): Flour S (E z).val:= by
 let v: Finset (Dwell m)→ℂ:=crumb (E z).val; refine ⟨v,((fineShape (E z)).allP).trans (Eq.symm (sum_subset (subset_univ _) fun j _ e=>?_))⟩; rw [show v j=0 from congrFun (axis_eq ((Mew.chipV j).differentiable.comp h) (differentiable_const _) (q.mono fun i p=>(p.door e))) z,zero_smul]
open Tye.Firn
-- silhouette depends on no input array; same from `still`
def soloR (Kq:Stores (w.step V)) := onK ((H.eye Mk A₀ T₁ (F:=0) (Location.gross_zero _ _ f H.start)).blocks Kq)
def soloW (Kq:Stores (w.step V)):= onK (Quori Mk A₀ T₁ D.pilot (H.crew y H.living).1 H.still Kq)
local notation "Qw" i:max => H.soloW Mk A₀ T₁ i
local notation "Qr" i:max => H.soloR Mk A₀ T₁ i
local notation "r₂" => D.Z.r2*τ
variable (Kq:Stores (w.step V)) (z:ℂ)
variable (O : Hos (w.step V) (coming D.Z 105 5*radiusB x))(C: Words (w.step V))
local notation "socketR" => (rare_l o.muster (Eire.trot S' Mk Kq) (Qw Kq) (Qr Kq) H.night (D.Z.r2*τ) z' D.pilot.cost D.pilot.s O)
local notation "socketC" => (coin_l o.muster (Eire.trot S' Mk Kq) (Qw Kq) (Qr Kq) H.night (D.Z.r2*τ) Δ D.pilot.cost D.pilot.s C)
-- primitive real-slope row fields with Frozen-normalizer removed.
def jewel:ℂ→mu := (socketR).choose
def crown:ℂ→mu := (socketC).choose
local notation "𝓡"=> H.jewel Mk A₀ T₁ Kq O
local notation "𝒞"=> H.crown Mk A₀ T₁ Kq C
lemma jewel_p: Pencilled 1 (H.jewel Mk A₀ T₁ Kq O):= (socketR).choose_spec.1
lemma crown_p: Pencilled 2 (H.crown Mk A₀ T₁ Kq C):= (socketC).choose_spec.1
local notation "κ" => Fintype.card (Frozen O.val x Mk.park)
lemma jewelReal {X:Pilot} (g:X.cost=D.pilot.cost) (v:X.s=D.pilot.s)(hb:β∈Year R x)(hv:fends p p' o β X)(Lx: Bs β F):
   (groupTide Mk A₀ T₁ X hv Lx).rare Kq O=((χ (X.hat R x) β:ℂ)⁻¹^κ) • 𝓡 (β:ℂ):= by
 let E:= Quori Mk A₀ T₁ X hv Lx Kq; let Pq:= Eire.trot S' Mk Kq
 change heedP (Up β) (poleY Pq β y) (onK E) (onK ((groupTide Mk A₀ T₁ X hv Lx).blocks Kq)) (D.Z.r2*τ) z' X.cost X.s (χ (X.hat R x) β) O=_
 obtain ⟨hu,h⟩:= H.qori Mk A₀ T₁ hb H.living hv (H.crew y H.living).1 Lx H.still Kq; unfold E; rw [hu,h,g,v]
 exact (socketR).choose_spec.2 _ (H.pos hb) _
lemma crownReal {X:Pilot} (g:X.cost=D.pilot.cost)(v:X.s=D.pilot.s)(hb:β∈Year R x)(hv:fends p p' o β X)(Lx: Bs β F): (groupTide Mk A₀ T₁ X hv Lx).coin Kq C=𝒞 (β:ℂ):= by
 let E:= Quori Mk A₀ T₁ X hv Lx Kq; let Pq:= Eire.trot S' Mk Kq
 change wistL (Up β) (poleY Pq β y) (onK E) (onK ((groupTide Mk A₀ T₁ X hv Lx).blocks Kq)) (D.Z.r2*τ) Δ X.cost X.s C=_
 obtain ⟨hu,h⟩:= H.qori Mk A₀ T₁ hb H.living hv (H.crew y H.living).1 Lx H.still Kq; unfold E; rw [hu,h,g,v]
 exact ((socketC).choose_spec.2 _ (H.pos hb)).symm
private lemma jewelPath (l:ℂ) : Flour (camp (stem S' O)) (l⁻¹^κ • 𝓡 z).val:= by
 refine Flour.smul (axis_flour (w:=y) (H.jewel_p Mk A₀ T₁ Kq O).entire ?_ z) _; filter_upwards [H.day] with β hb
 have v:= (H.crew β hb).1; let Lx:= H.choice (F:=0) hb (Location.gross_zero _ _ f H.start); let lq:ℂ:=↑(χ Δ₀ β); let q:= groupTide Mk A₀ T₁ D.pilot v Lx; let f:=q.rare Kq O; have hp:lq≠0:= Complex.ofReal_ne_zero.mpr (H.shot_p hb _ v).ne'; rw [show 𝓡 (β:ℂ)=lq^κ • f from ?_]; exact (q.rareP Kq O).smul _
 rw [show f=lq⁻¹^κ • _ from H.jewelReal Mk A₀ T₁ Kq O rfl rfl hb v Lx]; simp [smul_smul,hp]
private lemma crownPath : Flour (camp ((vast (k:= D.Z.N1*τ) o.muster C).val)) (𝒞 z).val := by
 refine axis_flour (w:=y) (H.crown_p Mk A₀ T₁ Kq C).entire ?_ z; filter_upwards [H.day] with β hb
 have v:= (H.crew β hb).1; let Lx:= H.choice (F:=0) hb (Location.gross_zero _ _ f H.start)
 rw [← H.crownReal Mk A₀ T₁ Kq C rfl rfl hb v Lx]; exact (groupTide Mk A₀ T₁ P' v Lx).coinP Kq C
variable (l:ℂ)
/-- `l` = absolute retag shot value at complex beta `z`. Use `l=1` for the entire pencil field. -/
def lantern (hF:Location.gross p' D f F): Eire.Dress w.G S' d z' (20*τ) (Rc y) (Ys y F) Δ Tσ:=
 { H.eye Mk A₀ T₁ hF with
   rare := fun Kq O => l⁻¹^Fintype.card (Frozen O.val x Mk.park) • H.jewel Mk A₀ T₁ Kq O z
   coin := fun Kq C => H.crown Mk A₀ T₁ Kq C z
   rareP:= fun _ _=>jewelPath ..
   coinP:= fun _ _=>crownPath .. }
end Lid
end Pitching
end YM.CF.Py.Rate
