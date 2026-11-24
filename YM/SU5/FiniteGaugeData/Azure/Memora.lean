import YM.SU5.FiniteGaugeData.Cirrus.Blanc
import YM.SU5.FiniteGaugeData.Indigo.First
set_option autoImplicit false
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option maxHeartbeats 410000
set_option linter.unusedVariables false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Hierarchy.LyraBill
open Function Filter NormedSpace SU Lat Lattice Cube Finset MeasureTheory RG Wilson Metric
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Kronecker Topology ComplexOrder
open Rush Scroll Peaks Stencil Tenant Tap Tulip Branch Fir Scree Advance Reflect Window Laurent Next.Free Bloch Drapes Spire Lifted Skye Sound Precision Tree Push.SectorMeasure Next.SectorChange Common Fock Pastry Satin
open Window.Brique
open Reed (Fine)
attribute [local instance] opCStarAlgebra
set_option quotPrecheck false
open Heat Quest Fock.Brique
open Nacre Heat Charm Chrono Journey
open Py Py.Rate LocalLimit Preparation Journey Fiber Vale VolumeCape FullBill
open SalonG
open Quest.Chaperone
open Steam
variable {Λ:Preparation}{l:ℕ}(Y:Course Λ (VolumeCape.Dream.Nimbus l)) {g:ℝ}{u v:ℕ→ℕ}
open Eight YM.SU5.FiniteGaugeData.CodaT YM.SU5.FiniteGaugeData.Cuprite.Spirit YM.SU5.FiniteGaugeData.Cuprite.Spirit.Vapors Fock.Relief Rhythm.Hush Rhythm.CodaT Dial Aria Reduction.Drama.Pack
open Rhythm.Dolores Rhythm.Ergo Hills Gamer Fock.Reduction Turnist Alts Alts.Emblem Window.Presidio.Nigra
namespace Chiffon
open Moorend Rhythm.CodaT
open Reduction.Loyd Reduction.Dijon Reduction.Loyd.Art Reduction.Celeste
namespace Sesame
open Reduction Lycan Niagara Chisel Largo Mirage Cascade Ember PolarF Onyx
open Reduction.Plush Window.Trigo
namespace FlakeNight
open Fock Tint -- gauge
local notation "Υ" n:max=> SU.Slot × Fin n
variable {n m:ℕ}
local notation "Δ"=> Fin (projCard n)
open CF.Stent Buffered.Stent
namespace Succulent
open Strata
open CF.Indigo
namespace SpineV
open YM.SU5.FiniteGaugeData.Lapis Lumi
open LapisS LapisS.Stadium
open Chiffon.Prato
open YM.SU5.FiniteGaugeData.Indigo Taper
open Fock
namespace Licor
namespace Lychee
open Tint Eight.Bonbon
open YM.SU5.FiniteGaugeData.LapisQ WinkQ Exterior Work.F03 Cordon
open LapisS.ArenaQ
variable (H:RadioCity.Hypothesis Λ l g Y) (h:Real.exp 1 ≤ Λ.x)
local notation "Kₜ"=> tent Y h
local notation "Q"=> wageL Λ
local notation "η"=> nodeC (specialM Λ.R.L)
local notation "Πx"=> μX Λ
local notation "ν"=> zoomP Λ
local notation "ρ"=> WideLake Λ
local notation "Γ"=> cradle Λ.R
variable (t:ℝ)(q:0<t)(x:Cover)(s i k:ℕ){p b C ε c:ℝ}
local notation "W₁" => Charm.W (tent Y h)
local notation "Σ"=> AverPX Y h s x t q
local notation "Ψ"=> Snear Y h s t q
local notation "G"=> SU.group
local notation "A₁"=> ace (Λ:=Λ) s Kₜ
local notation "J"=> Jeanne (Λ:=Λ) s Kₜ
variable {I:ℕ→ Family (tent Y h)→ℕ→ℂ}{E:ℕ→ Family (tent Y h)→ℂ}
variable (K:Universal Y h u v I E){P:Call Λ l}{Jk:Wicket Λ l}(R:Rolled Y h u v Jk P)(A:∀ i:Axis, Repertory Y h K R i)
local notation "B₁"=> Beacon Y h
local notation "Xλ"=> HomeX (Λ:=Λ) x
open TulleV
local notation "ρE" => estate h Y (HomeX (Λ:=Λ) x) g
local notation "RX"=> regnal Λ l Y h g x
-- real transfer.Matter.
namespace Slate
variable (g₀:0≤g)(P':Titan Λ)
variable (f: Fin (n+1)→ Trigo.Chamber true)(f':Fin (n+1)→ Trigo.Chamber false)
namespace AzureM
open Verne
-- `MNative`
set_option maxHeartbeats 400000
local notation "G₀"=> GNative Kₜ
local notation "Φ₀"=> Φ -- no implicit.
variable {Φ:ℕ→ Charm.W (tent Y h)→ₗ[ℂ]ℂ}(S':Sphere Y h K R A Φ)
variable (a b:Axis)(z:ℤ)(U V:W (tent Y h))
local notation "β"=> fire Kₜ
open CF.Indigo
lemma fireNativeA (p:GNative Kₜ U): GNative Kₜ (fire Kₜ a 0 U):=by
 obtain ⟨F,S,p,rfl⟩:=p; let T:= moveC a 0; let f(z:LinksC):=star (F (T z)); let A:= refract a 0 S; have hv: Anorak A f:=by
    let h:T=Lattice.pull (Signed.mirror a) 0:=by unfold T moveC; -- moveC expects V variable; funext
                                                         simp
    refine ⟨fun i u=>?_, (p.continuous.comp (move_cont ..)).star,fun x y t=>congrArg star (p.loc _ _ (moved_agree a _ t))⟩
    unfold f; rw [h, Work.G06.pull_gauge_zero, p.walk] -- spelling
 refine ⟨f,A,hv, ?_⟩; apply Subtype.ext; funext m W; rw [ice_print]; unfold reflector reflMark; let P:= ( Kₜ).c m; change theta _ ( (F (onC P (fling a 0 P W.1))) • (1:FC _))= f (onC P W.1) • _; rw [reflect_onC,theta_smul,theta_one] -- rfl
lemma fireNativeB (p:MNative Kₜ U): MNative Kₜ (fire Kₜ a 0 U):=by intro i x y; rw [ice_print,reflector,reflMark]; unfold reflMark; rw [p] -- rewrite.Twist
include K R
lemma fireNative (p:LiftNat Y h K R U s): LiftNat Y h K R (β a 0 U) s:=by
 rcases p with p|⟨t,x,y,rfl,q,hx,rfl⟩; · exact Or.inl (fireNativeB Y h a U p)
 refine Or.inr ⟨t,β a 0 x, β a 0 y,rfl,fireNativeB Y h a x q,fireNativeB Y h a y hx,?_⟩; rw [next_mir, ice_join,mul_zero]
omit K R
variable (ℓ:ℕ)(S T: Finset Cover)
lemma glows (A:LeadsC ℓ b S T) (v:a≠ b): LeadsC ℓ b (refract a 0 S) (refract a 0 T):=by rintro k p i q; obtain ⟨k,pk,rfl⟩:=mem_image.mp p; obtain ⟨i,qk,rfl⟩:=mem_image.mp q; rw [fling_move,fling_move, if_neg v,if_neg v]; exact A _ pk _ qk
lemma viridian (A:LeadsC ℓ a S T): LeadsC ℓ a (refract a 0 T) (refract a 0 S):=by intro x i y j; obtain ⟨x,p,rfl⟩:=mem_image.mp i; obtain ⟨y,q,rfl⟩:=mem_image.mp j; simp only [fling_move,mul_zero,ite_true,add_zero]; specialize A y q x p; omega
lemma flipping (A: AwayP ℓ S T): AwayP ℓ (refract a 0 S) (refract a 0 T):=by
 intro i; by_cases e:a=i; · subst i; exact (A a).elim (fun t=>Or.inr (viridian a ℓ S T t)) (fun t=>Or.inl (viridian a ℓ T S t)) -- args order header earlier Duplicate b:ℝ implicit
 exact (A i).imp (fun t=> glows a i ℓ S T t e) (fun t=> glows a i ℓ T S t e) -- check order
include S' K R
lemma stol (hh:Beacon Y h (Φ s) U V ≠0): Beacon Y h (Φ s) (fire Kₜ a 0 U) (fire Kₜ a 0 V) ≠0 :=by -- h shadow Kₜ issue
 have hz(X:W Kₜ): Φ s (β a 0 X)=star (Φ s X):= by
    rw [← show Heat.gaugeShift Λ.block 0=0 from ?_]; · exact S'.mirror s a 0 X
    unfold Heat.gaugeShift; ring
 rw [show Beacon _ _ _ _ _=star (Beacon Y h (Φ s) U V) from ?_]; · exact fun e=> hh (star_injective (by rw [star_zero]; exact e));
 unfold Beacon; rw [←ice_join,hz,hz,hz,star_sub,star_mul, mul_comm (star (Φ s V))] -- lean coerc prob
structure Lodged (F F': Charm.W (tent Y h))(S T: Finset Cover): Prop where
 v₁:Locator Kₜ F S
 v₂:Locator Kₜ F' T
 k: GNative Kₜ F
 b: LiftNat Y h K R F' s
 e: Beacon Y h (Φ s) F F'≠0
 pv:AwayP ℓ S T
 hs:S.Nonempty
 ht:T.Nonempty
local notation "ℵ"=> Lodged Y h s K R (Φ:=Φ) ℓ
lemma Lodged.glint(p: Lodged Y h s K R (Φ:=Φ) ℓ U V S T) : Lodged Y h s K R (Φ:=Φ) ℓ (β a 0 U) (β a 0 V) (refract a 0 S) (refract a 0 T):=⟨locate_cold _ _ _ _ p.v₁
   ,locate_cold _ _ _ _ p.v₂,fireNativeA Y h a U p.k, fireNative Y h s K R a V p.b,stol Y h s K R A S' a U V p.e, flipping a ℓ S T p.pv,p.hs.image _,p.ht.image _⟩
lemma orienting (u':ℵ U V S T): ∃ (F F': Charm.W (tent Y h))(E E':Finset Cover), Lodged Y h s K R (Φ:=Φ) ℓ F F' E E'∧∀ a:Axis,LeadsC ℓ a E E':=by
 let B:=Terrace.scheduleL; suffices h:∀ L: List Axis, ∃ (F F':W Kₜ) (E E':Finset Cover), ℵ F F' E E'∧∀ a∈L, LeadsC ℓ a E E' by obtain ⟨F,F',E,E',p,v⟩:= h B; exact ⟨F,F',E,E',p,fun i=>v i (Terrace.scheduleV _)⟩
 intro L; induction L with
 | nil=> exact ⟨U,V,S,T,u',by simp⟩
 | cons a L ih=>
    obtain ⟨F,F',E,E',p,v⟩:= ih; by_cases k:a∈ L; · exact ⟨_,_,_,_,p,fun i x=> v i ((List.mem_cons.mp x).elim (fun h=>h ▸ k) id)⟩
    rcases p.pv a with z|z; · exact ⟨_,_,_,_,p,fun i t=>(List.mem_cons.mp t).elim (fun u=>u ▸ z) (fun t=>v i t)⟩ -- ambiguity precedence
    refine ⟨_,_,_,_,Lodged.glint Y h s K R A S' a F F' ℓ E E' p,fun i x=> ?_⟩; rcases List.mem_cons.mp x with rfl|t; exact viridian _ ℓ E' E z; exact glows _ i ℓ E E' (v i t) (fun p=> k (p.symm ▸ t))
#print axioms orienting
end AzureM
end Slate
end Lychee
end Licor
end SpineV
end Succulent
end FlakeNight
end Sesame
end Chiffon
end YM.CF.Buffered.Afterglow.Hierarchy.LyraBill
