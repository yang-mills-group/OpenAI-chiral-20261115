import Bay.C.Maple
import Bay.C.Kiln
set_option maxHeartbeats 1050000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Bay.C
open QuadClock
open Neon
open Py
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
open Ione Moto Taxi Hove Haro Vow Bake Lilt Prism Rue Larch Push.AbsoluteSums.Trees Salt Jet
open scoped YM.CF.Mew

set_option autoImplicit false
open Mew Waxy Roots Rive Oise



open Rate LocalLimit Preparation Pitching Focus 
set_option maxRecDepth 3500
set_option synthInstance.maxHeartbeats 160000
local notation "VΔ"=>Buffered.Afterglow.Tower.VacuumSelection.Spine


structure HullF where
 P:VΔ
 s:ℕ
 i:ℕ
 k:ℕ
namespace HullF
variable (w:HullF)
abbrev π := w.P.par
abbrev old:=takeUp w.P w.s w.i w.k
abbrev newb:=takeUp w.P (w.s+1) w.i w.k
abbrev home:=w.old.side
abbrev sea:=w.newb.side
abbrev X:= RootBook w.P.run w.i w.k w.s
abbrev Y:= RootBook w.P.run w.i w.k (w.s+1)
abbrev Mm:= ArmX
abbrev L:=w.π.R.L
abbrev G := apt (w.P.run.ir w.i) w.π.block w.L w.s
abbrev S := Stem w.P.run w.i w.k w.s
abbrev tape := w.P.run.voyage w.i
abbrev U := w.π.U
abbrev G₀ := w.tape.CapeT w.s
abbrev G₁ := w.tape.CapeT (w.s+1)
abbrev Xp := ((w.tape.X (w.P.run.uv w.k)).wave w.s).val
abbrev x:= JumpF w.P w.s
abbrev gaps:Prop:=w.s+1 < w.P.run.uv w.k
abbrev peak:Prop:=w.tape.kick ≤ w.k
variable (b:Rib w.P)
abbrev purse := WorkF w.P b.Γ w.s
abbrev pouch:= DyeF w.P b.Γ w.s
abbrev amt(M:ℕ)(g:Outfit)(t:ℕ):= PriceF w.P M g t w.s

structure Apron(w:HullF) where
 Be: Observatory w.G w.X.p
 Vκ:Cusp w.home
 Ca:ArcΦ→ℝ→ℝ

variable (M:ℕ)
abbrev valid (r:Apron w):Prop:=
 let D:=ArmX w.P b
 OrbitJet w.π.V w.U w.G w.S w.G₀ w.G₁ w.X w.Y w.Xp Chi.canonical w.π.J.d w.π.h
   (b.V1 w.x) (b.Kf w.x) (b.W w.x) D.delta D.f0 D.g0 D.g1 D.g2
   (w.purse b) (w.pouch b) (b.Z w.x) r.Be r.Vκ r.Ca (cipherK w.π.J.n) M

abbrev scene:Prop:=SceneF w.P b M w.s w.i w.k
lemma apron_exists (f:w.scene b M):∃r,w.valid b M r:=by
 obtain ⟨x,y,z,h⟩:= AstroFunding.trust f
 exact ⟨⟨x,y,z⟩,h⟩

variable (g:Outfit)(t:ℕ)(r:Apron w){J:Type}[LinearOrder J][Fintype J]
 (σ:J→Site w.home)

abbrev grid (T:J→SealV w.sea):Prop:=
 gr T=Cube.node ∘ heel w.G ∘ σ ∧
 w.newb.GaugeBill M (gr T) ∧ GapN σ w.X.p.B w.L.val M

variable (E:Key J→RegBudget w.sea)(F:Key J→ForceBudget w.sea)
abbrev Ey:=CropE w.Y E
abbrev Fy:=CropF w.Y F
abbrev tag (_:J):=w.amt M g t

abbrev PulseF:Prop:=
 OrbitPulse w.G w.X w.Y w.π.h (w.purse b) (w.pouch b) w.L σ (w.Ey E) (w.Fy F)
   0 (w.tag M g t) M

abbrev SailF(O:Ignition σ):Prop:=
 let D:=ArmX w.P b
 Passage (h:=w.π.h) w.π.V w.U w.G w.S w.G₀ w.G₁ w.X w.Y w.Xp Chi.canonical w.π.J.d
   (b.V1 w.x) (b.Kf w.x) (b.W w.x) D.delta D.f0 D.g0 D.g1 D.g2
   (b.Z w.x) r.Be r.Vκ r.Ca (cipherK w.π.J.n) σ (w.Ey E) (w.Fy F)
   0 (w.tag M g t) O

abbrev Moves(x:Orbit w.home)(f:Orbit w.sea→Phys w.sea)(y:Orbit w.sea):=
 lynx w.π.K w.S w.G w.G₁ w.G₁ w.G₀ w.Y Chi.canonical w.π.J.d w.Xp x y (f y)
abbrev Flame (O:Ignition σ)(l:List J)(x:Orbit w.home)(f:Orbit w.sea→Phys w.sea):Prop:=
 Integrable (w.Moves x f) (city w.sea) ∧
 tipI (fun z=>denZ (Roast w.X r.Vκ O z) w.U w.G₀ x) l = ∫y,w.Moves x f y ∂city w.sea

variable {w b M g t r σ E F}
open FullBill Buffered Afterglow Journey

lemma burnP {O:Ignition σ}(v:w.gaps)(u:w.peak)
 (p:w.scene b M)(i:w.PulseF b M g t σ E F)
 (h:w.SailF b M g t r σ E F O)
 (l:List J)(x:Orbit w.home)(y:Rue.FleetS w.X.p.threshold x.1):
 w.Flame r σ O l x (w.newb.winE E F l):=by
 have j:w.s<w.P.run.uv w.k:=(Nat.lt_succ_self _).trans v
 let H:= (fullness w.P.run w.i w.k u).cap_grant
 obtain ⟨d⟩:=H.grant _ j
 have e:=cinder h i.buy (AstroFunding.toe p) d (H.aligned _ j) (H.branch _ j) l x y
 unfold Flame
 suffices a: ClientY w.π.V w.U w.G₁ w.Y (w.Ey E) (w.Fy F) l=w.newb.winE E F l from a ▸ (show Integrable (w.Moves x _) _ ∧ _=_ from e)
 funext z
 apply lace_C l _ roots
 intro a ha
 have hp:w.Y.slip=0:= AstroFunding.hush p
 unfold Ey Fy CropE CropF dampE
 change _=denZ (w.newb.offsetR (E a) (F a)) ..
 simp only [if_pos ha]
 rw [←hp]

end HullF
namespace HullF
variable (w:HullF)(b:Rib w.P)(M:ℕ)(g:Outfit)(t:ℕ)(r:w.Apron)
variable {J:Type}[LinearOrder J][Fintype J](σ:J→Site w.home)(T:J→SealV w.sea)
variable (E:Key J→RegBudget w.sea)(F:Key J→ForceBudget w.sea)
variable (m:ℕ)

structure ShipF (w:HullF)(b:Rib w.P)(M:ℕ)(g:Outfit)(t:ℕ)(r:w.Apron)
 {J:Type}[LinearOrder J][Fintype J](σ:J→Site w.home)(T:J→SealV w.sea)
 (E:Key J→RegBudget w.sea)(F:Key J→ForceBudget w.sea)
 (m:ℕ)(O:Ignition σ):Prop where
 dons:Dons w.newb T w.L.val m (w.amt M g t) E F
 pink:w.PulseF b M g t σ E F
 tips:∀j,νTip (w.Ey E) j=νTip E j ∧ emberTip (w.Fy F) j=emberTip F j
 sail:w.SailF b M g t r σ E F O
 envelope (l:List J)(x:Orbit w.home):
   w.peak → FleetS w.X.p.threshold x.1 →
   w.Flame r σ O l x (w.newb.winE E F l)∧
   (ψS (gr T) l → w.Flame r σ O l x (w.newb.scroll (agent T) l))

/- For fixed E,F given (e.g. native licenses), issue ship from common Apron. -/
variable {w b M g t r m}
variable (p:w.scene b M)(c:w.valid b M r)(j:w.gaps)
   (a:0 ≤ w.amt M g t)(u:w.amt M g t ≤ w.pouch b)

include p c j a u
lemma steamboat (y:w.grid M σ T)
 (d:Dons w.newb T w.L.val m (w.amt M g t) E F):
 ∃o,ShipF w b M g t r σ T E F m o:=by
 have h:w.s<w.P.run.uv w.k:=(Nat.lt_succ_self _).trans j
 have d0:=d.book.paid
 rw[y.1] at d0
 have hy:= blush d0 a (AstroFunding.hush p) (leafArc w.P _ _ w.i h) u
    (add_le_add_right u _) y.2.2
 have n:w.PulseF b M g t σ E F:=hy.1
 obtain ⟨o,burn⟩:=heatRun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _  _ _ _ _ _ c (zero_le_one.trans (AstroFunding.toe p)) n
 refine ⟨o,⟨d,n,hy.2,burn,fun l x v y=>?_⟩⟩
 have t:w.Flame r σ o l x (w.newb.winE E F l):= burnP j v p n burn l x y
 refine ⟨t, fun i=>?_⟩
 let f₁:=w.Moves x (w.newb.winE E F l)
 let f₂:=w.Moves x (w.newb.scroll (agent T) l)

 have r:f₁=ᵐ[city w.sea] f₂:=by
   filter_upwards [d.book.flow.thick] with z e
   unfold f₁ f₂ Moves; exact congrArg _ (d.book.flow.entry l z i (d.wide l i) e)
 exact ⟨t.1.congr r,t.2.trans (integral_congr_ae r)⟩

variable (f:FleetX w.newb g M w.L.val t)
include f
lemma flotilla
 (v:w.grid M σ T)(h:∀i,σq w.newb g t (T i))(y:w.newb.lampCap ≤ m):
 ∃E F o,ShipF w b M g t r σ T E F m o:=by
 obtain ⟨W,Z,k⟩:= f.quay _ v.2.1 h y
 exact ⟨W,Z,steamboat _ _ _ _ p c j a u v k⟩
