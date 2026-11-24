import YM.CF.DPress.Yarn.Furnish
set_option autoImplicit false
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
set_option maxHeartbeats 400000
noncomputable section
namespace YM.CF.Py.Kay
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
open Lich.Muster Lor
open Jet Vol Rel
open Cascade
open Fief
open Yaw Pig
open Wray
open Lich.Muster Push.AbsoluteSums
open Iva Eire
open Trees Footprint Iva Eire
open Jade
open Oath Feu Feu.Corset Ione Nor Haro Beau Siete PhysicalNext.JointLoad.Heir Vow
open AnalyticBridge.VerifiedReset
open DPress DPress.Fees Finance Rosy
open scoped YM.CF.Mew
open Oise Larch  Bake
open Sour Tap Heath Tutor Docket Resident Campus Flight Moral Rosy
open Act Harvester WagesC Urban
namespace FitD
variable {B:Side}{K:Teller SU.group}{R:Patch}{L:ChartRatio SU.group} {d:ℝ} {V:Grace K R L} {U:Grasp V.U B d}{W:GivenX V U}
 {M':Side} {J:Robes M' V W}{C:Tew W}{P_:Campus C}
 {x:ℝ}{A:Harvester P_}
variable {M:Side}{n i j k:ℕ}{Δ :ΛFit P_ x}{Λ:Thrift A}
open Thrift RoomF
variable {F: RoomF J Λ M Δ}(D:Crib F n)
@[ext] structure LogH (d:Side) where
 fuel : Yds d
 δ : ℝ
 r : Haro.SpaceM
 v : ℂ
namespace LogH
instance {d:Side}:Zero (LogH d):=⟨⟨0,0,0,0⟩⟩
instance (d:Side): Inhabited (LogH d):=⟨0⟩
-- backwards arrow: build any Good sequence of certificates. Stage given spine and inputs funded.
lemma book (X:ℕ → Type*) [∀ i,Inhabited (X i)] (u t:ℕ)(h:u ≤ t)(P: ∀ i:ℕ,X i → Prop)(G:∀ i:ℕ,X (i+1) → X i → Prop)(b:X t)(q:P t b)(p:∀ i:ℕ,u ≤ i →  i < t  → ∀ V,P (i+1) V → ∃ y,P i y∧ G i V y):∃ (y:∀ i,X i), y t=b ∧(∀ i,u ≤ i → i ≤ t  →  P i (y i)) ∧∀ i,u ≤ i →  i < t  →  G i (y (i+1)) (y i):=by
 suffices h: ∀ k:ℕ,k+u  ≤  t → ∃ y:∀ i,X i,y t=b∧(∀ i,t-k ≤ i → i ≤ t  → P i (y i))∧ ∀ i,t-k ≤ i  →  i < t  →  G i (y (i+1)) (y i) by simpa only [show t-(t-u)=u from by omega] using h (t-u) (by omega)
 intro k; induction k with
 | zero=> let y:= Function.update (fun i=> (default:X i)) t b; refine fun h=> ⟨y,Function.update_self ..,fun i p v=>?_ , fun i p v=>by omega⟩; have h :i=t:=by omega
          rw [h,show y t=b from Function.update_self ..]; exact q
 | succ k ih=>
    intro h; obtain ⟨y,w,s,g⟩:= ih (by omega); let j:= t-(k+1); have he: u ≤ j:=by unfold j; omega
    have hp:j+1=t-k:=by unfold j; omega
    have ht:j<t:=by unfold j; omega
    obtain ⟨b,P',q⟩:= p j he ht (y (j+1)) (s _ (by omega) (by omega)); let y':= Function.update y j b; have hb:y' j=b:=Function.update_self ..; have hv(i)(h:i≠j):y' i=y i:= Function.update_of_ne h ..
    refine ⟨y',(hv t ht.ne').trans w,fun i p v=>?_,fun i p v=>?_⟩; · change j ≤ i at p; rcases p.eq_or_lt with h|h; rw [←h,hb]; exact P'; rw [hv _ (by omega)]; exact s _ (by omega) v
    change j ≤ i at p; rw [hv (i+1) (by omega)]; by_cases t:i=j; rw [t,hb]; exact q; rw [hv i t]; exact g _ (by omega) v
end LogH
namespace Crib
abbrev L0(j:ℕ):=LogH (cell M B R.L j)
abbrev render(j:ℕ)(v:LogH (cell M B R.L j))(b:ℝ):= Kay.arm (venue D j) b v.fuel v.v
abbrev stipend_h (j:ℕ)(v:LogH (cell M B R.L j))(e:ℝ)(q:RankX):Prop:= Provides R.L K.j (render D j v 1) C.h e q
local notation "PY" j:max=> (venue D j)
variable (r:LogH (cell M B R.L j))(s:ℝ)
lemma essentially(B:ℝ) (q:RankX): (Provides R.L K.j (render D j r B) C.h s q)↔stipend_h D j r s q:=by
 cases q with
 | none=> exact ⟨fun u=>⟨u.1,rfl,u.3,u.4,u.5⟩,fun (u:Laurel (D.render _ r 1) K.j C.h s s R.L.val)=>⟨u.1,rfl,u.3,u.4,u.5⟩⟩
 | some i=> rfl -- tune defeq Provides.Laurel depends proof.
local notation "vΠ"=> venue D j
local notation "vℓ"=> Δ.a
variable {h:i<n}(Ω:ℝ)(E:Lobby (D.locale i h) (Λ.O (hat R.L x i)) Ω)
lemma yearβ (g:i<n)(z:ℝ): z∈Year R (hat R.L x i) ↔ matchedX (hat R.L x (i+1)) z:=by rw [hat_succ]; rfl -- orientation
abbrev LobbyP(h:i<n)(z:ℝ):=Lobby (D.locale i h) (Λ.O (hat R.L x i)) z
lemma HrelP(h:i<n) : Silo.Hrel (σp D i h) Ω= D.paid i Ω:=by
 let Q:=D.locale i h; let p:= (σp D i h).p; change Kay.arm _ (Ω+(p.Hm.ang+p.Hm.fee)) 0 0 = _; rw [p.hp,p.hf, paid,D.κt h]; rfl
variable (Wν:Blend (cell M B R.L i) A.μ)(α:ℝ)(p:HonestL E)(t:Silo.Can (D.locale i h) P_ (Λ.O (hat R.L x i)).δ α)
local notation "qH"=> D.locale i h
local notation "K*"=> σp D i h
abbrev postH : LogH (cell M B R.L i) :=⟨(K*).duo Wν α E p,(K*).Δa α E p,(K*).Ξy E p,(K*).vπ Wν α E p t (monus _)⟩
lemma packaged : let L0' := postH D Ω E Wν α p t; render D i L0' (Ω+toll D i - L0'.δ)= (K*).D Wν α E p ((K*).vπ Wν α E p t (monus _)):=by intro y; rw [Silo.D,HrelP]
end Crib
end FitD
end YM.CF.Py.Kay
