import GaugeFieldConstruction.Avatara
set_option autoImplicit false
set_option maxHeartbeats 48000
set_option synthInstance.maxSize 24000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.XGarden.MastTin.ArtCart
open Function Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG WilsonStartup Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Matrix.Norms.L2Operator Classical
open Buffered Buffered.Region FlightFlux Fluxim Work Tensor
open Fock Tulip Lat Spire Phase Cube Scroll Paige Vault Phase Spire Branch
open Push.SectorMeasure
attribute [local instance] opCStarAlgebra
variable {n:Side}
open Shield Echo Ledger Jet Salt Pastry Hake Urn Levier Hive Nacre Rush Peaks
local notation "GS"=>SU.group
open Next.SectorChange.Motion Ione
open TableF.Lenten TableF.Lenten.Housing TableF.Lenten.Layout
open Haro
open scoped YM.CF.Mew
open Buffered Lifted Girt Skye Window Vale
open TableF TableF.Lenten Layout Flot Moto Tap Bank ModuleB Haro Hove Fren Work.F03 Taxi Ember Fir HushP
variable {G H:Paper n}{p:BudgetPoint}{c v h:ℝ}(M: Male){o:Seat n}
open Spectrix Simmer Next.Rank.Spindle
open Gleam Gleam.Guide Fock.Flux
open Py.Rate.LocalLimit.Papal Py.Rate.LocalLimit.Papal.FrameP
open AnalyticBridge VerifiedReset
open Gleam.Guide.Pitcher Coins Fock.Flux Fock.Flux.Pacts
open YM.GaugeFieldConstruction.Wick.Yacht YM.GaugeFieldConstruction.Wick.Yacht.Vesper Violets
-- Epoch hull as quadratures. standard cost coupons
open scoped Kronecker
open YM.GaugeFieldConstruction
variable (x:Cover)(w:300<n.val)
open Phys
local notation "Jφ" => Cauchy.J Phys.Spair
-- Mixed.Dial.P.D. derivative correction. use goldΦ.J bin. oX tag.Force Σ.Assumption.
variable (p:BudgetPoint)(h:ℝ)
def MastP (x:Cover)(Q:Paper n):WaC x→ℂ:= Function.uncurry (SipF n x Q)
lemma nerf (G:Paper n):MastP x (Genre.pure.coinB p h • G) = Marlox x (orbitPH (AlphaY G 1)) h:=by
 have hx:Genre.pure.coinB p h=h^2:=by unfold Genre.coinB; simp [Genre.orderB]
 rw [hx]; ext1 i; rcases i with ⟨i,j⟩; unfold MastP SipF Marlox Skor; let u:=Γpay n x i j; let v:=AngleP n x false i; let y:=AngleP n x true j; let K:=h^2; let F:= (K • G : Paper n)
 change u* orbitPH (AlphaY F 1) v y=(h:ℂ)^2* (u* orbitPH (AlphaY G 1) v y)
 rw [(bpu_T ..).1,(bpu_T ..).1]; change u* (K • G _ _ + -(K • G _ _))= (h:ℂ)^2*(u*thrust G _ _ _); rw [← smul_neg,← smul_add,Complex.real_smul]; change u*( (K:ℂ)*thrust G _ _ _)=_; unfold K; push_cast; ring
lemma stockColor (G:Paper n)(b:p.power≤3)(t:p.order≤6)(k:0<h)(T:TrackD p (Pach (Θk n x)) h G c)(V:Tuned G) (u:tangD n): Dialat x (Paint (AlphaY G) u):=by
 intro i j e; by_contra H; apply e; unfold Paint; have he(v:tangD n): portE (AlphaY G) i j v=0:= Classical.byContradiction fun l=> H (Stock x T V _ i j l) -- tune
 rw [Matrix.of_apply,funext he]; simp
-- use matron & micro_Mgrad directly. transfer at unscaled.S.
local notation "oX" => Θk n x
lemma bill_TZ(G:Paper n)(pA:ready_D G)(u v:ArcK x)(φ:Confab (Θk n x))(k:ℝ): SipM n x (k • G) φ u v=k • SipM n x G φ u v:=by
 let K:= caster oX φ; let ζ:=Γpay n x u v; let X:=AngleP n x false u; let Y:=AngleP n x true v
 let P(w:tangD n):=portE (AlphaY G) X Y w
 have hp : P=PressAt (G (hereV n (bet0 _ true u v)))-PressAt (G (hereV n (bet0 _ false u v))):= Oscar_P ..
 have hk: portE (AlphaY (k • G)) X Y=k • P:=by
    rw [show _= _ from Oscar_P n x (k • G) u v]; rw [hp]; ext1 i; rw [smul_sub]; rfl -- tune
 have ht: DifferentiableAt ℝ P 0:= by rw [hp]; exact ((pA _).differentiableAt (by simp)).sub ((pA _).differentiableAt (by simp))
 unfold SipM Paint; simp only [Matrix.of_apply]; rw [hk,fderiv_const_smul ht]; change ζ*(k • fderiv ℝ P 0 K)= k • (ζ* fderiv ℝ P 0 K); rw [mul_smul_comm]
lemma transitMu (G:Paper n)(u v:ArcK x)(φ:Confab (Θk n x)):∑ i:StampSet n x, φ i • SipeQ n x G i u v= SipM n x G φ u v:=by
 let K(n':Confab (Θk n x)):=SipM n x G n' u v; let i:=AngleP n x false u; let j:=AngleP n x true v; let Z:= Γpay n x u v
 let H(f:Confab (Θk n x)):= fderiv ℝ (portE (AlphaY G) i j) 0 (caster oX f)
 let Q(k:StampSet n x):Confab (Θk n x):= Pi.single k 1
 have he: SipM n x G φ u v= SipM n x G (∑ i,φ i • Q i) u v:=by congr 1; ext1 j; simp [Q,Finset.sum_apply, Pi.single_apply]
 rw [he]; change ∑ i,φ i • (Z*H (Q i))= Z* H (∑ i,φ i • Q i); unfold H; simp only [map_sum,map_smul,Finset.mul_sum,mul_smul_comm]
include w
lemma pics_Phi (G:Paper n)(T:TrackD p (Pach (Θk n x)) h G c)(H:portable G)(V:Solon Genre.mixed G)(A:tangD n)(q:Confab (Θk n x))(g:cast_P (Θk n x) A=p.threshold • q) (i j:ArcK x):
 ∑ k:StampSet n x,q k • SipeQ n x (Genre.mixed.coinB p h • G) k i j= Skor h x (Paint (AlphaY G) A) i j:=by
 rw [transitMu x _,bill_TZ x G (readiness _ T)]; let B:=p.threshold; let φ:= Γpay n x i j; let z:=AngleP n x false i; let y:=AngleP n x true j; let Q:=caster oX q; let C:=AlphaY G; let D:=Paint C (caster oX (cast_P oX A)); have he: D z y=Paint C A z y:=by
    obtain ⟨g,r⟩:= torn_K A oX w; let Y:=A - caster oX (cast_P oX A); let L:=fderiv ℝ (portE C z y) 0; have hv:L Y=0:=by
       let a:=PressAt (G (hereV n (bet0 _ true i j))); let b:=PressAt (G (hereV n (bet0 _ false i j))); change fderiv ℝ (portE _ z y) 0 Y= _; rw [show portE C z y=a-b from Oscar_P ..,fderiv_sub (show DifferentiableAt ℝ a 0 from (readiness _ T _).differentiableAt (by simp)) (show DifferentiableAt ℝ b 0 from (readiness _ T _).differentiableAt (by simp))]; change fderiv ℝ a 0 Y - fderiv ℝ b 0 Y= _; rw [show fderiv ℝ a 0 Y=0 from micro_Mgrad _ T H g V.2 _ r _,show fderiv ℝ b 0 Y=0 from micro_Mgrad _ T H g V.2 _ r _, sub_zero]
    unfold Y at hv; rw [map_sub,sub_eq_zero] at hv; exact hv.symm
 rw [Skor,←he, SipM]; change Genre.mixed.coinB p h • (φ * Paint C Q z y)=(h:ℂ)^2 *(φ * D z y)
 unfold D Paint; simp only [Matrix.of_apply]; rw [g, map_smul, map_smul]; rw [Complex.real_smul,Complex.real_smul,show Genre.mixed.coinB p h=h^2*B from by simp [Genre.coinB,Genre.orderB,B]]; change _=(h:ℂ)^2*(φ*((B:ℂ)* Paint C Q z y)); change (↑(h^2*B):ℂ)*(φ*Paint C Q z y)= _; push_cast; ring
abbrev MesaP (G:Paper n)(r s t:ℕ): Cauchy.J Phys.Trip:= ∑ i:ArcK x,∑ j:ArcK x,∑ k:StampSet n x,SipeQ n x G k i j • Cauchy.times' (Cauchy.times' (Rift x false r i) (Rift x true s j)) (waxG x t k)
lemma MixedLead (P:Paper n)(Ltt:Waves)(G: MetaB (Θk n x) M Ltt (AlphaY P) p h) -- tune Ltt
 (b:p.power≤3)(t:p.order≤6)(k:0<h)(T:TrackD p (Pach (Θk n x)) h P c)(H:Solon .mixed P)(U:portable P)(V:Tuned P) (i:Spair)(j:Pen): let W:= hem (E_G j.1) (dye j.2); let Q:=Genre.mixed.coinB p h • P; test (i,j) (MesaP x Q 0 0 0)= test i (goldΦ ((bm5 Ltt).val W)):=by
 intro W Q; let A:=gateC oX p.threshold W; let Z:=AlphaY P; let X:= Paint Z A; have hp:=stockColor x p h P b t k T V A; have he:(bm5 Ltt).val W=(markJet oX X h).1:= (congrArg (fun V:ComG→L[ℝ]Pal=>V W) G.mixed).trans (Servers M x w X hp _|>.1)
 unfold MesaP; rw [he, ←Ph0 _ x w X hp]; simp only [map_sum]; apply Finset.sum_congr rfl; intro a _; apply sum_congr rfl; intro l _
 let μ:=pitchX (n:=n) x j; let Zc:= Skor h x X a l; have ht:Zc=∑ t,μ t • SipeQ n x Q t a l:= (pics_Phi x w p h P T U H A μ (funext fun t=> ΨK _ _ t j w _) a l).symm -- order tune
 change _= test i (Zc • _); rw [ht, Finset.sum_smul,map_sum]; apply sum_congr rfl; intro v _; rw [map_smul,tested,Rift_0,Rift_0,wax_c,map_smul]; change SipeQ _ _ Q _ _ _ * (test i (wedgeCR a.2 l.2)*(μ v:ℂ))=(μ v • SipeQ _ _ _ _ _ _) * test i _; rw [Complex.real_smul]; ring -- tune
end YM.CF.XGarden.MastTin.ArtCart
end
