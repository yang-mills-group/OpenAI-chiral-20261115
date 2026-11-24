import YM.SU5.SatinWard.Resolution.GrainJ
import YM.SU5.SatinWard.Resolution.Sailfin
set_option synthInstance.maxSize 24000
set_option maxHeartbeats 85000
noncomputable section
set_option linter.unusedSectionVars false
set_option quotPrecheck false
namespace YM.CF.Py.Rate.LocalLimit.Preparation
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open CF.Appel CF.Newt CF.Char CF.Neige CF.Summit Next Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Schur MultiNext.SignedSource Lyre Banjo Analysis Pressure AnalyticBridge.MarginalMultiplier3b1d PatchReads SectorNext.Remainder SectorNext.Remainder.Scales Planned.AtomRegular Extra.Iteration Extra.Iteration.Scales
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
open BScale Vow.TreasuryFog Sour Roots Exa Vow Rive Mew Stax Swell Porticus QuadClock Ione.Clock Moto Neon Taxi Lor
open Oise Buffered
open Pitching Focus QuadClock.ShapeLab
open Oise Buffered
variable {P:Preparation}{ℓ:ℕ}(Y:Course P (VolumeCape.Dream.Nimbus ℓ)) (Γ:ℝ)(Pay kc:ℝ)(Tξ:Hove.Grant P.K.j 2)(nmc m:ℕ) (Z V K W:ℝ→ℝ)
variable (uZ:BladeQ P.R Z W V K)(proofW:∀ᶠ s:ℕ in atTop,∀ᶠ i in atTop,∀ k,s<Y.uv k → stockedTap Y Pay kc Γ Tξ nmc m Z V K W s i k)(flag:∀ i k, ((Y.voyage i).X k).Prepared P.P P.delay)
variable {η ι:Type}[Fintype ι][DecidableEq ι][Fintype η](F:ResolutionFrame ι)(C H A u0:ℝ)


open Pail.Dew Swell.Porticus QuadClock.ShapeLab.ResolutionFrame
open Lampshade SignSlot Waxy Tap
set_option linter.flexible false
variable {a b c d U ε f r ψ:ℝ}{s i k:ℕ}
local notation "Bα"=> RootBook Y i k s
local notation "pβ" => (Bα).p
local notation "Λ" => P.Ctor (Y.ir i) s
local notation "V₀"=> (Y.voyage i).CapeT s
local notation "θ"=>lapQ Y s
local notation "ωs"=> hat P.R.L P.x s
local notation "ARE"=>stockRate (Bα).p
local notation "L★"=> P.R.L

open Hove
variable (p:GardenPlan Y s i k a b ψ f c (stencilReserve P.R.L)) (pB:0 ≤ b)(pH:0<c)(vΩ: CartRoom P.U ((Y.voyage i).CapeT s) (RootBook Y i k s) P.R.L.val Γ P.h)
variable (Hw:0<lapQ Y s)(w:s< Y.uv k)

open ShapeLab
open SweepSign
namespace Tabletop
open LitCurrent Sonar Chamber Next.Rank.Spindle
variable {j:ℕ}{v:ℝ}(P₀:MaskPoint Y j s i k a b)(E:eraτ Y s i k j a v)
local notation "o₀"=> (0:Site Λ)
local notation "p★"=> (RootBook Y i k s)

open Motet
local notation "rate"=> (dewy P s)
local notation "ψe" => vigorΩ P s
local notation "χX" N:max i:max=> spinCharacter N i
variable {S:Side}
variable (q:Axis) (l:Wage3) (j:ℕ)
variable {F:Site S→ Mark S} (u:SignBent (spinCharacter S q) BodyPull F)
-- Define as two unnormalized arms; downstream subtract 2* Z_v using normalization relation algebraically.
def counterArc {A:Type*}[AddCommGroup A](S:Side)(j:ℕ)(a:Axis)(F:Site S→A)(y:Site S):=F (y+j • step a)+ F (y-j • step a)
include u
lemma arcSpin(a:Axis): SignBent (spinCharacter S q) BodyPull (counterArc S j a F):=by
 intro s v x y h; rw [counterArc, counterArc, map_add, smul_add]
 let K:=BodyPull s; obtain ⟨m,t,d⟩:= (mem_spin ..).1 v
 let k:=s⁻¹; have he:k.s⁻¹=s.s:=by unfold k; rw [show s⁻¹.s=s.s⁻¹ from rfl, inv_inv]
 have hv:LitCurrent.pose s⁻¹ y=x:= by unfold LitCurrent.pose; rw [inv_inv]; exact (earlier_mills s x y).mp h
 have Pτ (b:FaceDir) : K (F (destSite y j b))= (χX S q).sgn s • F (destSite x j (faceAt s⁻¹ b)):=by
    apply u s v; apply (earlier_mills s _ _).mpr; have P0:= pose_hop s⁻¹ y j b; rw [hv,LitCurrent.pose, inv_inv] at P0; exact P0
 have h₁:= Pτ (a,false); have h₂:= Pτ (a,true)
 change BodyPull s (F _)+BodyPull s (F _)=_; unfold faceAt at h₁ h₂ -- let simpl.Sweep.inv.scope
 have he:s⁻¹.s⁻¹=s.s:=he
 rw [he] at h₁ h₂ -- t inside Step.rotate ! unfolds?
 cases b:s.s.flip a
 · simpa [counterArc,K,destSite,strideD, Step.vec,sub_eq_add_neg, Step.rotate,t,b] using (congrArg₂ (·+·) h₁ h₂)
 rw [add_comm ((χX S q).sgn s • F (x+j • step a))]; simpa [counterArc,K,destSite,strideD,Step.vec,sub_eq_add_neg, Step.rotate,t,b] using (congrArg₂ (·+·) h₁ h₂)
omit u
abbrev clearArc(Y:Course P (VolumeCape.Dream.Nimbus ℓ))(s i:ℕ)(j:ℕ)(a v:Axis)(l:Wage3):= dewy P s • counterArc (P.Ctor (Y.ir i) s) j a (spinClass Y s i v l)
lemma spinCoat : SignBent (spinCharacter Λ q) BodyPull (spinClass Y s i q l):= by let F:=dynamicSpin (ShapeLab.leg l); have he:ChiralX 0 F:=(Θc.equivFun.symm (ShapeLab.leg l)).property; exact bend_scale _ _ (Jattired _ he.herm q)
lemma stageSpin (a:Axis):SignBent (spinCharacter Λ q) BodyPull (clearArc Y s i j a q l):= bend_scale _ _ (arcSpin q j (spinCoat Y q l) a) -- notation dots
abbrev verseRate (a b d:ℝ)(P:Preparation)(x:ℝ):ℝ:= 2*matterTrace a b d P x
lemma verseFunds (p:0<a):Chill_v (verseRate a b d P) ∧ Chill_v (boreLeg P (verseRate a b d P)):=by obtain ⟨u,v⟩:=earning (P:=P) a b d p; let H:=v.cheap 2; exact ⟨u.cheap _,H.trend (Eventually.of_forall fun i=> le_of_eq (by unfold verseRate boreLeg; rw [mul_assoc]))⟩ -- implicit b/d variables
include p pB pH Hw w
lemma verseBank (v:Axis)(z:ΛcrestF d)(hp:j ≤ (RootBook Y i k s).p.B)(q₀: P.J.n+27≤(RootBook Y i k s).p.B) : let x:= verseRate a b d P; preBank Y (boreLeg P x) x (spinFrame q) s i k (clearArc Y s i j v q l):=by
 intro x; let F:= dynamicSpin (ShapeLab.leg l); have he:ChiralX 0 F:=(Θc.equivFun.symm (ShapeLab.leg l)).property; apply bent _ (spinFrame q) _ (stageSpin Y q l j v)
 let W(o:Site Λ)(g:separation o₀ o≤ (Bα).p.B) := highP Y p pB pH Hw w q₀ o g (pathSpin l q) (z.1 l q) (fun i=> (commutes_petal ..).2 (he.color i))
 let T:=Swell.stopBeam (0:Site Λ) v j; change Sail _ _ _ _ (2*_ :ℝ) (rate • (_+ _)); rw [two_mul,smul_add]; exact Motet.plus _ (W _ (T.1.trans hp)) (W _ (T.2.trans hp))
omit p pB pH Hw w
open ResolutionFrame Rue Advance Hove Yoke Buffered Afterglow Journey
open ResolutionFrame Rue Advance Tower.SlabMark Tower.Tilted VelourBoard
open StressFlux AnalyticBridge.VerifiedReset Ione.Clock Harmonic Shrine
variable {f0 v:ℕ}(h:s≤v)(D:Coords Wage3)(rℓ:ℝ) -- classical instance ok
include u
lemma reflected_arc (x:Site S) (i:Axis)(d:ℤ)(Hp:AtSupport false univ (F x)): reflMark i d (F x)= StressFlux.sign (Signed.mirror i) q • F ((plane i d).mills S x):=by
 let p_:= Advance.tagMove i d S; let h:= turned_m i d x; let w':= (plane i d).mills S x
 have v0:p_∈(spinCharacter S q).group:= (mem_spin q p_).mpr ⟨mirror_l _,rfl,rfl⟩; have tp:= (mem_spin ..).1 v0
 have hu:= u _ ((spinCharacter S q).group.inv_mem v0) w' x h.backward
 rw [spin_sgn_inv q p_ tp.2.1, BodyPull,LinearMap.coe_mk, AddHom.coe_mk, inv_inv] at hu -- Body defeq tagMove
 rw [←flies_theta _ _ _ Hp]; exact hu
omit u
variable {Q:Site (P.Ctor (Y.ir i) v)→ Mark (P.Ctor (Y.ir i) v)} (g:SignBent (spinCharacter (P.Ctor (Y.ir i) v) q) BodyPull Q)
local notation "A_"=>spinClass Y v i q
local notation "ψb"=> (Q- ShapeLab.columns (spinClass Y v i q) D)
include g
lemma lapTwist (p:SeatsPriced A Y s i k v (armF Y (spinClass Y v i q) Q D h) rℓ): TwistP Y i s v (armF Y (spinClass Y v i q) Q D h):=by
 let z (i:Axis):=StressFlux.sign (Signed.mirror i) q; let f:=sprintCost P.R.L^(v-s)*(1/2:ℝ); let X:= spinCharacter (P.Ctor (Y.ir i) v) q
 have hc :SignBent X BodyPull (ShapeLab.columns (A_) D):=by
    intro a v x y h; simp only [ShapeLab.cols_apply,Finset.sum_apply,map_sum,smul_sum,Pi.smul_apply]; apply sum_congr rfl; intro i' _; rw [map_smul,(spinCoat Y q i') a v x y h, smul_comm (D i')]
 have he:SignBent X BodyPull (Q-ShapeLab.columns (A_) D):=by rw [sub_eq_add_neg,←neg_one_smul ℝ]; exact bend_add _ g (bend_scale _ _ hc)
 intro i' t; let W:=armF Y A_ Q D h
 refine ⟨z i',normUnit _ _, fun x=>?_⟩; change reflMark _ _ (W x)= _ • W _
 have hp (x): W x=(f • (Q-ShapeLab.columns A_ D)) (upRoot Y i h x):=by unfold W armF f; rw [Pi.smul_apply, mul_smul]; rfl
 rw [hp,hp,heel_swing]; exact reflected_arc _ (bend_scale _ f he) _ _ _ ((hp x) ▸ p.fieldT x)
omit g
end Tabletop
end YM.CF.Py.Rate.LocalLimit.Preparation
