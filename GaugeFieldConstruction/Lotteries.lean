import GaugeFieldConstruction.Braille
import GaugeFieldConstruction.Fangs
/-! graded operator shape & comparison.-/
set_option autoImplicit false
set_option maxHeartbeats 50000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Oath
open Nor
open Function NormedSpace Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
open Atala Forge Cloak Rill Hive Fock Stilo Palot Scion
open Cube Lat Tenant Tulip
open Pastry Hake Levier Urn Peaks Fock Laic Branch Drapes
attribute [local instance] opCStarAlgebra
open Rush Scroll Paige Vault Phase Acorn Spire
open Tarn Cay Slate Cour Hest
open Hom Vale Vale.Grace Next.Free Thera Nacre Dial Fock
open Fief Jet Vol Rel
open Yaw Pig
open Feu Feu.Corset Haro
section
open Py Riant Lattice Prism Tap FlightFlux TableF Boom Axon Flot Taxi
open Lenten.ModuleB
open Lich.Muster
open Hake Vow Bake Rue Larch
open TableF Lenten.Bank Lenten Lenten.Layout Fren
open Frugal
open scoped YM.CF.Mew
open BellPrice PinRack
abbrev Rateκ (L:Side)(r:ℕ):= αN L^(3+r)
lemma Rate_pr (L:Side) (r:ℕ): 0 <Rateκ L r:= pow_pos (α_pos _) _
private lemma slashy {E:Type}(P:TPack E){s t u v:ℝ}(e:s*(u*v)=t): letI:=P.G; letI:=P.S; ∀ x:E,(s:ℂ) • (u:ℂ) • (v:ℂ) • x=(t:ℂ) • x:=by letI:=P.G; letI:=P.S; intro i; simp only [smul_smul,←e,Complex.ofReal_mul,mul_assoc]
private lemma softB {E:Type}(P:TPack E){u v z w:ℂ}:letI:=P.G; letI:=P.S;∀ x:E,x=0→ u • v • z • x=w • x:=by letI:=P.G; letI:=P.S; rintro x rfl; simp
lemma ChimeP (s z t r:ℝ)(X:Waves)(j:ℕ) : MSlot j (Crown s z t r X) =Crown s z t r (MSlot j X):=by -- use zero
 unfold MSlot; split_ifs <;> apply Prod.ext <;> first|rfl|apply Prod.ext <;> first|rfl|exact Prod.ext (Troot_z PackG _).symm (Troot_z PackP _).symm| exact Prod.ext (Troot_z PackH _).symm (Prod.ext (Troot_z PackM _).symm (Troot_z PackS _).symm) -- Troot import! use smul_f move
-- h that g.* projections. 
set_option maxHeartbeats 200000 in
lemma fees_ideal (f:Waves)(r j:ℕ)(e:r≤j)(v:j≤2)(P Q:BudgetPoint)(K:Side)(Z:Waves)(s t:ℝ)(h:0<t)(u: ΓProj j Z=(s:ℂ) • f)(k:∀ i:ℕ, ΓProj i f =if r ≤ i then f else 0): let x:=Rateκ K r; let q:=P.threshold / Q.threshold; (((t*x)⁻¹:ℝ):ℂ) • MoonIdeal r K P Q Z= PrintQ (s/t) q f:=by
 intro x q; let T:= Rateκ K r; let X:=αN K; let u₀:=Λgear 1 P.threshold Q.threshold K; let u₁:=Λgear 2 P.threshold Q.threshold K
 have hz: ΓProj r f=f:= by rw [k, if_pos (by omega)]
 have hv:MSlot r Z=(s:ℂ) • f:=by change ΓProj r Z=_; rw [←show ΓProj r (ΓProj j Z)=ΓProj r Z from MStore Z e,u,map_smul,hz]
 change (((t*T)⁻¹:ℝ):ℂ) • MSlot r (Crown T (u₀*u₀) (u₀*u₁) (X^3*u₀) Z)= _; rw [ChimeP,hv]
 have hr : T≠0:= (Rate_pr ..).ne'; have hd: t≠0:=h.ne'; have hX : X≠0:= (α_pos ..).ne'
 have ht:(t*T)⁻¹*(T*s)=s/t:=by field_simp -- tune
 have hs:u₀=X^2*q:=by rfl -- tune unitStep defin
 have hw:u₁=X^3*q:=by rfl
 refine Prod.ext (slashy PackL ht _) (Prod.ext (Prod.ext ?_ (slashy PackP ht _)) (Prod.ext ?_ (Prod.ext (slashy PackM ht _) ?_)))
 · by_cases u:r=1
   · refine slashy PackG (show (t*T)⁻¹*(u₀*u₀*s)=(s/t)*q^2 from ?_) _; rw [hs,show T=X^4 from (by unfold T Rateκ; rw [u])]; field_simp -- tune
   refine softB PackG (bF4 f) ?_; by_cases p:r<1
   · nth_rw 1 [←hz]; unfold bF4; change (if 1 ≤r then f.2.1 else 0).1=_; rw [if_neg (by omega)]; rfl -- tune
   have H:ΓProj 1 f=0:=by rw [k,if_neg (by omega)]
   exact congrArg (fun x=> bF4 x) H -- definitional tune
 · by_cases p:r=2
   · refine slashy PackH (show (t*T)⁻¹*(u₀*u₁*s)=(s/t)*q^2 from ?_) _; rw [hs,hw,show T=X^5 from (by unfold T Rateκ; rw [p])]; field_simp
   refine softB PackH (bF5 f) ?_; nth_rw 1 [←hz]; unfold bF5; change (if 2 ≤r then f.2.2 else 0).1=_; rw [if_neg (by omega)]; rfl
 by_cases p:r=2
 · refine slashy PackS (show (t*T)⁻¹*(X^3*u₀*s)= s/t*q from ?_) _; rw [hs,show T=X^5 from (by unfold T Rateκ; rw [p])]; field_simp
 refine softB PackS (bm5 f) ?_; nth_rw 1 [←hz]; unfold bm5; change (if 2 ≤r then f.2.2 else 0).2.2=_; rw [if_neg (by omega)]; rfl
end
end YM.CF.Oath
end
