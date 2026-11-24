import Anomaly.Rack.RawCost
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 300000
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
open Eire Girt
open VolumeRate


namespace LocalLimit
namespace Preparation
open BScale Vow.TreasuryFog Sour Roots Exa Vow Rive Mew Stax Swell QuadClock

open Buffered Vow Stax Sault Exa Afterglow Tapestry Girt
variable {P:Preparation} {ℓ:ℕ}(Y:Course P (VolumeCape.Dream.Nimbus ℓ)) {j i s k m:ℕ}
local notation "N" => P.Ctor (Y.ir i) s
local notation "κ" => (Y.voyage i).CapeT s
local notation "Rm" => RootBook Y i k s
local notation "Θ" => hat P.R.L P.x s

variable {J:Type} [Fintype J][LinearOrder J]

lemma Quill.tender {σ : J→ Site (P.Ctor (Y.ir i) s)}
 {X:J→ Mark (P.Ctor (Y.ir i) s)} {W:J→ phy (P.Ctor (Y.ir i) s)} {A:J→ Aura (P.Ctor (Y.ir i) s)}
 {C:Key J→RegBudget (P.Ctor (Y.ir i) s)}{T:Key J→ForceBudget (P.Ctor (Y.ir i) s)}{u d e f:ℝ}
 (p:Quill Y s i k σ X W A C T u d e f)(h: (Y.voyage i).kick ≤ k)(w: s< Y.uv k)
 (L:List J)(v:ψS (Cube.node∘ σ) L)(z:L.Pairwise fun i j=>Disjoint (A i).val (A j).val) :
    let Y':=RootBook Y i k s; let K:= (Y.voyage i).CapeT s; let D:=partitionZ Y' P.U K
    let g(x:Orbit (P.Ctor (Y.ir i) s)):=beamZ (P.Ctor (Y.ir i) s) (tipI (fun q=> denZ (color_b Y' Y'.beta (Y'.F+C q) Y'.slip (Y'.K+T q) Y'.v) P.U K x) L)
    D≠0 ∧ Integrable g (city _)∧ Journey.compass Y i k s (L.map X).prod=(∫ x,g x∂city _)/D:=by
  intro R K D g
  let W:=(L.map X).prod
  have hx: Rue.IsleB SU.group R.p.threshold:= by
    have he:R.p=Y.meter.a s:= (((Y.voyage i).X (Y.uv k)).pull.owns s w.le).width.symm
    rw [he]; exact ((Y.voyage i).paths k).paid.can.isle s
  have hv : (fun x:Orbit N=> letterRead (W (x.1,K x)) (denZ R P.U K x))=ᵐ[city _] g:=by
    filter_upwards [ae_fleet (n:=N) hx] with x y
    unfold g; rw [show tipI _ _ =_ from p.marked L v z x y]; exact Contact.stencil p.spine z _ _
  obtain ⟨u,t',Q⟩:= Tapestry.funds Y s i k (Contact.assemblePitch L (fun i _=> p.spine i) |>.env) h w.le
  refine ⟨t',(show Integrable (fun x:Orbit N=> letterRead (W (x.1,K x)) (denZ R P.U K x)) (city _) from u).congr hv,?_⟩
  exact congrArg (· / D) (integral_congr_ae hv)

variable (k0 : ℕ)
def rootBud (o:Site (P.Ctor (Y.ir i) s))(m k:ℕ):Vow.Aura N:=⟨rootRim (RootBook Y i k s).p m o,Cube.node o,halo_subset _ _ (mem_singleton_self _)⟩
def puffKey (X:SOp (P.Ctor (Y.ir i) s))(D : Axis → SOp (P.Ctor (Y.ir i) s))(k m:ℕ)(o:Site (P.Ctor (Y.ir i) s)) : phy N:=
  ((hueW P.R.L (hat P.R.L P.x s):ℂ) • puffLine ((Y.voyage i).CapeT s) (RootBook Y i k s).p o (fun j=>co_Ψ o 0 (D j)) (co_Ψ o 0 X) m)

structure PostPins (Y:Course P (VolumeCape.Dream.Nimbus ℓ))(s i k m:ℕ)(a b:ℝ)(f d u v c e:ℝ)(k0:ℕ)
    (Z Z' : Axis→ SOp (P.Ctor (Y.ir i) s))(X T:SOp (P.Ctor (Y.ir i) s)) : Prop where
    cart : CartPins Y i k s m a b f d Z Z' X T
    pack : ∀ {J:Type} [Fintype J][LinearOrder J] (σ:J→ Site (P.Ctor (Y.ir i) s)), Force_M (RootBook Y i k s).p.B (Cube.node∘σ) k0 →
     ∃ (U: Key J→ RegBudget (P.Ctor (Y.ir i) s))(W:Key J→ ForceBudget (P.Ctor (Y.ir i) s)), Quill Y s i k σ (fun j=> tested Y (σ j) X Z k m) (puffKey Y X Z k m ∘ σ) (fun j=> rootBud Y (σ j) m k) U W u v c e ∧ ∀ L:List J, ψS (Cube.node∘σ) L → L.Pairwise fun i' j' => Disjoint (rootRim (RootBook Y i k s).p m (σ i')) (rootRim (RootBook Y i k s).p m (σ j'))

lemma ReadyBench.certify {G D μ K:ℝ→ℝ} {a b:ℝ} {J T:Axis→SOp (P.Ctor (Y.ir i) s)} {X W:SOp (P.Ctor (Y.ir i) s)}
 (t:CartPins Y i k s m a b (G Θ) (D Θ) J T X W)
 (v:ReadyBench Y Θ (G Θ) (D Θ * pinpr P.R.L Θ) (μ Θ) (K Θ) (RootBook Y i k s) k0) (s':s<Y.uv k)(l:20 ≤ (RootBook Y i k s).p.B):
    let E:=fun x=> D x * pinpr P.R.L x
    PostPins Y s i k m a b (G Θ) (D Θ) (winL k0 E μ Θ) (wakeK k0 μ Θ) (putTip 2 E Θ) (putTip 3 E Θ) k0 J T X W:=by
  intro E; refine ⟨t,fun {I} _ _ σ p=>?_⟩
  obtain ⟨F,D,H⟩:= pricedQuill (d:=E) Y σ v p (fun j=> tested Y (σ j) X J k m) (puffKey Y X J k m ∘ σ) (fun j=> rootBud Y (σ j) m k) (fun j=> (CartPins.window Y (σ j) t).2) (fun j=> (t.for_all (σ j))) s'
  refine ⟨F,D,H,fun L y => ?_⟩
  let x:=(Rm).p; let b:= x.B
  have hu:L.Pairwise (fun i j=> node (σ i)≠ node (σ j)):= List.pairwise_map.mp y
  refine hu.imp ?_; intro i j h
  have v:= p.1 i j h
  have hb : 24*m ≤ b:=t.curtain
  apply Contact.spacing 0
  change b + 12 + 2*m + (b + 12 + 2*m)< _
  change b^3+b^3+b+b<_ at v
  refine lt_of_le_of_lt ?_ v; change 20≤ b at l; have hu : b ≤ b^3 := le_self_pow₀ (by omega) (by norm_num); omega
end Preparation
end LocalLimit
end YM.CF.Py.Rate
