import Anomaly.Chosen.Gray
import Anomaly.Compass.Tension
import Anomaly.Gab.Choose
import Anomaly.M13
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
open Eire Girt
open VolumeRate
open BScale Vow.TreasuryFog Sour Roots Exa Vow Rive Mew Stax Swell Porticus QuadClock Ione.Clock Moto Neon Taxi Lor
open Oise Buffered
variable {a b c v d s f x y w h:ℝ}{k r:ℕ}{P':BudgetPoint}
open Pitching Focus
namespace LocalLimit
namespace Preparation
variable {P:Preparation}{ℓ:ℕ}(Y:Course P (VolumeCape.Dream.Nimbus ℓ)) (Γ:ℝ) (Γ0:Taxi.DayT 6 Γ) (g0:0≤Γ)
-- check binder names
variable (kk η:ℝ)(T:Hove.Grant P.K.j 2)(kκ mc:ℕ)
variable (Z V F W:ℝ→ℝ)
open SketchA Turning Salt
-- holds Melon for vote & wages. any A Bon.Cop. Surge is ANY at large m after Pose braces ready. Note both s and s+1 reindex for Haven. nFlags uses calculated count.Concert.Ea.
abbrev Tansy (Y:Course P (VolumeCape.Dream.Nimbus ℓ))(W:ℝ→ℝ)(s i k:ℕ):Prop:= let L:=P.R.L; let X:=RootBook Y i k s; let U:= RootBook Y i k (s+1); let w:=lapQ Y s; let w':=lapQ Y (s+1);
    10≤X.p.B∧ 10≤U.p.B ∧ w' ≤ w ∧ w ≤ 2*w'∧∀ a:ℝ,0≤a→∀ x:Site (P.Ctor (Y.ir i) (s+1)),Melon L X.p U.p (nun_ω U.F x) P.h w' a (W (hat P.R.L P.x s))
local notation "ΩK"=> P.R.L
lemma plumeΦ (t:∀ᶠ s:ℕ in atTop,∀ᶠ i:ℕ in atTop,∀ k:ℕ,s<Y.uv k→ stockedTap Y kk η Γ T kκ mc Z V F W s i k) (b:BladeQ P.R Z W V F):∀ᶠ s:ℕ in atTop,∀ᶠ i:ℕ in atTop,∀ k,s+1<Y.uv k→ Tansy Y W s i k:=by
 let L:= P.R.L; obtain ⟨v,v',p⟩:=book_ε L
 let h(x):= hat P.R.L P.x x
 let H:∀ᶠ s:ℕ in atTop, 10 ≤ radiusB (hat P.R.L P.x s):= (Work.E01.radiusB_tendsto.comp (turnover P)).eventually_ge_atTop _
 filter_upwards [H,(tendsto_add_atTop_nat 1).eventually H,t,(turnover P).eventually (nut_V _ 1 le_rfl v 2 Z W V F b)] with s YL Wt U B
 filter_upwards [U] with i t k w
 let P':=t k (by omega); unfold Tansy; intro L X U a a'; obtain ⟨t,p₁,p₂,p₃,p₄⟩:=p_meters Y i k s (by omega); obtain ⟨u,v,w',t',l⟩:= p_meters Y i k (s+1) w
 change _= _ at u
 have ht:a'= allotΨ L (hat P.R.L P.x s+Vale.billX L):=by unfold a' lapQ; rw [hat_succ]; rfl
 have hm:0<a':= ht.symm ▸ B.day.1
 have hq:a'≤ a:=ht.symm ▸ B.day.2.1
 have hp:a ≤ 2*a':= ht.symm ▸ B.day.2.2
 obtain ⟨tq,hx,hv,hw⟩:=P'.shore.life; refine ⟨(by change 10 ≤ (RootBook Y i k s).p.B; rwa [t]),(by change 10 ≤ (RootBook Y i k (s+1)).p.B; rwa [u]),hq,hp,?_ ⟩
 intro v V i; have hz:‖nun_ω U.F i‖=|tq|:= by rw [hx]; simp
 refine ⟨B.pays.trans ?_, V,P.height,hm, hz.symm ▸ hv,hz.symm ▸ hw,P'.shore.rate.2⟩
 let L':= ΩK
 refine le_trans (mul_le_mul_of_nonneg_left hp (le_of_lt (book_ε _).1)) ?_
 nlinarith only [show 2*PongR L * a' ≤ ((L.val:ℝ)⁻¹)^5*a' from mul_le_mul_of_nonneg_right p hm.le]
-- Palm B uses rate p flags.A.G.Payment uniform hire post. Need Ξ.Flint grants after rotation and basis bank.
abbrev leafΨ (Γ:ℝ):= |gaugeStone Γ| -- Aolo normalization.
abbrev brusks:= strive_E 6
abbrev prelH:= duty_Q 6 2
abbrev brickP (Γ:ℝ):ℝ:=max 1 |prelH| * Δv HI Γ * leafΨ Γ
abbrev routeK(Γ:ℝ)(q0:ℕ)(x:ℝ):= max 1 |brusks| * Extr_h q0 HI Γ * leafΨ Γ * x
abbrev PaintRes (Γ:ℝ)(W Y:ArmorK): Prop:=W = Y
lemma SapP (Γ:ℝ)(k:ℕ)(x:ℝ)(p:0 ≤ x):0 ≤ brickP Γ ∧ 0 ≤ routeK Γ k x:=by
 unfold routeK brickP leafΨ Extr_h Δv; constructor <;> positivity
-- paint EST and rotor actions. all these costs from the drill. When paying start Jade use Barrage downRate. store extra w split on top later.
variable {i j:ℕ}
abbrev QuayPaint (Y:Course P (VolumeCape.Dream.Nimbus ℓ))(Γ:ℝ)(x v:ℝ)(s i k:ℕ):Prop:= let X:=RootBook Y i k s; let p:=X.p; let q':=lapQ Y s;
    ∀ (o:Site (P.Ctor (Y.ir i) s))(G:Bag _)(j:ℕ)(Φ:ArcΦ),Drill p P.J.n j P.R.L.val o P.h (stockRate p) G Φ x (q'*leafΨ Γ) 0 → ∃ Q W ξ,‖ξ‖≤ q'*leafΨ Γ ∧ Flint p G (grooveB j p (node o)) Q W ξ Φ o P.R.L.val P.J.n P.h (stockRate p) v v (brickP Γ*q') (routeK Γ P.R.L.val q') (q'*leafΨ Γ) ∧ ∀ (p':Sweep (P.Ctor (Y.ir i) s))(o':Site (P.Ctor (Y.ir i) s)),mPath p' o'=o → p'∈ Whirl (P.Ctor (Y.ir i) s)→ Flint p (cartTurn p' G) (actY p' (grooveB j p (node o))) (dashF p' Q) (dashK p' W) (Spire.payZ p' ξ) (arc_s p'.s (Levier.spinU false p'.s) Φ) o' P.R.L.val P.J.n P.h (stockRate p) v v (brickP Γ*q') (routeK Γ P.R.L.val q') (q'*leafΨ Γ)
include Γ0 g0
lemma bookedQuay (X':ℕ→ℝ)(u:∀ᶠ s:ℕ in atTop,0≤X' s) (D:∀ᶠ s:ℕ in atTop,∀ᶠ i:ℕ in atTop,∀ k:ℕ,s<Y.uv k→ stockedTap Y kk η Γ T kκ mc Z V F W s i k) :∀ᶠ s:ℕ in atTop,∀ᶠ i:ℕ in atTop,∀ k,s<Y.uv k→ QuayPaint Y Γ (X' s) (max 1 |brusks| * X' s) s i k:=by
 filter_upwards [u,D,(turnover P).eventually (Oath.progP 2 6 100), (Work.E01.radiusB_tendsto.comp (turnover P)).eventually_ge_atTop 10] with s P' T H t; filter_upwards [T,Y.ir_grows.tendsto_atTop.eventually_gt_atTop 32] with i T x k y
 unfold QuayPaint; intro X p q' o G j Φ h
 obtain ⟨Z',hw,hu,hh,hθ⟩:=p_meters Y i k s y
 change p.B=_ at Z'; change p.order=6 at hu; change p.power=2 at hh
 let n:=P.Ctor (Y.ir i) s; let R:=ΩK
 have h0:=T k y; have hx:32<n.val:=x.trans_le (amplit ..); have hp:10 ≤ p.B:=Z'.symm ▸ t
 obtain ⟨A0,K,t,tz⟩:= drillSlope h P.height (hu.symm ▸ Γ0) g0 (hu.symm ▸ hh.symm ▸ H) hp hw (by omega) ((show 20 < n.val from by omega).trans_le (Nat.le_mul_of_pos_right _ two_pos)) (show 3≤n.val from by omega)
 -- Pre-cal
 have f:Δv p Γ=Δv HI Γ:=by apply Ves; exact hu; exact hh; exact hθ -- tune binders
 let w:= q'*leafΨ Γ; have he:0≤w:=mul_nonneg (sq_nonneg _) (abs_nonneg _)
 have b:Extr_h R.val p Γ= Extr_h R.val HI Γ:= by apply μφ_c; exact hu; exact hh; exact hθ
 have hv:Δv p Γ*w ≤ brickP Γ*q':=by
    unfold brickP; rw [← f]; apply le_trans (le_mul_of_one_le_left (by unfold Δv; positivity) (le_max_left (1:ℝ) (abs prelH))) (Eq.le ?_); unfold w; ring
 have hv':Extr_h R.val p Γ*w ≤ routeK Γ R.val q':=by
    unfold routeK; rw [←b]; apply le_trans (le_mul_of_one_le_left (by unfold Extr_h; positivity) (le_max_left (1:ℝ) (abs brusks))) (Eq.le ?_); unfold w; ring
 have hk:X' s≤ max 1 |brusks| * X' s:=le_mul_of_one_le_left P' (le_max_left ..)
 refine ⟨A0,K,t,(Flint_emit tz).2.1,Flint_gain tz hk hk hv hv' le_rfl,fun i j g p' => ?_⟩
 have hV:strive_E p.order* X' s≤ max 1 |brusks| * X' s:= by rw [hu]; exact mul_le_mul_of_nonneg_right ((le_abs_self _).trans (le_max_right ..)) P'
 refine Flint_gain (yardPull tz P.height j g h0.chamber p') hV hV ?_ ?_ le_rfl
 · unfold brickP; rw [hu,hh,← f]; exact (mul_le_mul_of_nonneg_right ((le_abs_self (duty_Q 6 2)).trans (le_max_right 1 (abs prelH))) (show 0 ≤ Δv p Γ* w by unfold Δv; positivity)).trans_eq (by unfold w; ring)
 unfold routeK; rw [hu,show Extr_h _ p Γ=_ from b]; exact (mul_le_mul_of_nonneg_right ((le_abs_self (strive_E 6)).trans (le_max_right 1 (abs brusks))) (show 0 ≤ Extr_h R.val HI Γ*w by unfold Extr_h; positivity)).trans_eq (by unfold R w; ring)
end Preparation
end LocalLimit
end YM.CF.Py.Rate
