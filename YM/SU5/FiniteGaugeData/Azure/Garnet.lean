import YM.SU5.FiniteGaugeData.Azure.Memora
import YM.SU5.FiniteGaugeData.PeakR.Border
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
open Quest Chaperone Corners
open Mist Dover
local notation "β"=> fire Kₜ
local notation "φ"=> Φ s
variable (ℓ:ℕ)(S T:Finset Cover)(p:Cover)
abbrev swept(p:Cover)(S:Finset Cover):= temple ((tic Kₜ:ℤ) • p) S
private lemma moves_ℓ (s t: Cover)(S:Finset Cover): temple s (temple t S)= temple (t+s) S:=by unfold temple; rw [image_image]; apply congrArg (fun f: Cover → Cover => S.image f); funext i; exact add_assoc .. 
private abbrev bounce(p:Cover)(a:Axis):Cover:= ((tic Kₜ:ℤ)*p a) • step a
private def coil(p:Cover)(B:List Axis):Cover:= (B.map (bounce Y h p)).sum
include Y in
private lemma bonus_ℓ(p:Cover): coil Y h p Terrace.scheduleL= (tic Kₜ:ℤ) • p:=by
 funext i; fin_cases i<;> simp [coil,bounce, Terrace.scheduleL]
lemma swept_lit (p:Cover)(u:Locator Kₜ U S): Locator Kₜ (Mist.orbitW Kₜ p U) (swept Y h p S):=by
 have hh(B:List Axis): Locator Kₜ (Mist.hourS Kₜ p U B) (temple (coil Y h p B) S):=by induction B with
  | nil=>simpa [coil,Mist.hourS,temple] using! u
  | cons i B ih=> rw [Mist.hourS.eq_2,coil,List.map_cons,List.sum_cons,add_comm, ←moves_ℓ]; exact loc_tic _ _ _ _ ih
 simpa only [bonus_ℓ] using! hh Terrace.scheduleL
lemma mirror_swept (p:Cover): Mist.orbitW Kₜ (update p a (-p a)) (fire Kₜ a 0 U) = fire Kₜ a 0 (orbitW Kₜ p U):= eye Terrace.scheduleL
where eye (i:List Axis): Mist.hourS Kₜ (update p a (-p a)) (fire Kₜ a 0 U) i = β a 0 (hourS Kₜ p U i):=by
       induction i with
       | nil=>rfl
       | cons j B ih=>
         rw [Mist.hourS.eq_2,Mist.hourS.eq_2,ih]; by_cases p':j=a; · subst a; rw [clock_neg,update_self]
         rw [clock_normal,update_of_ne p']; exact Ne.symm p' -- orientation
-- choose shift <$L_a$ boundary with Heat target k.
noncomputable abbrev costE(Y:Course Λ (VolumeCape.Dream.Nimbus l))(h: Real.exp 1 ≤ Λ.x) (ℓ:ℕ):= ℓ+ℓ+(tic (tent Y h))
local notation "Yℓ"=> costE Y h ℓ
lemma pinY(t:LeadsC Yℓ a S T)(h':S.Nonempty) : ∃ z:ℤ,(∀ i∈S,i a+(tic Kₜ:ℤ)*z≤-(ℓ:ℤ))∧ (∀ i∈T,(ℓ:ℤ)≤ i a+(tic Kₜ:ℤ)*z):=by
 let P(i:Cover):= i a; obtain ⟨i,p,q⟩:= S.exists_max_image P h'; let C:ℤ:= tic Kₜ; let d:= -(ℓ:ℤ)-P i; let z:= d/C; have hp:0<C:=by unfold C; exact_mod_cast tic_pos Kₜ
 have ht:= Int.emod_nonneg d hp.ne'; have hx:= Int.emod_lt_of_pos d hp; have he:= Int.emod_add_mul_ediv d C; change d % C + C*z=d at he; refine ⟨z,fun x u=>?_,fun x u=>?_ ⟩
 · change P x+C*z≤_; have hh:= q x u; change _= -(ℓ:ℤ)-P i at he; omega
 have hh:= t _ p _ u; unfold costE at hh; change P i+(↑(ℓ+ℓ+tic Kₜ):ℤ)<P x at hh; change _≤ P x+C*z; change _= -(ℓ:ℤ)-P i at he; unfold C at *; omega
include Y
lemma ends_lac (u:∀ i:Axis, LeadsC Yℓ i S T)(h':S.Nonempty):∃ t:Cover,(∀ a, Ahead a 0 ℓ (refract a 0 (swept Y h t S))) ∧∀ a,Ahead a 0 ℓ (swept Y h t T):=by
 choose f u v using fun i=> pinY Y h i ℓ S T (u i) h'; refine ⟨f,fun i p t=>?_,fun i p t=>?_⟩
 · obtain ⟨p,tW,rfl⟩:= mem_image.mp t; obtain ⟨x,qW,rfl⟩:= mem_image.mp tW; rw [fling_move,if_pos rfl]; have hZ:= u i x qW; change _ ≤ -(x i+(tic Kₜ:ℤ)*f i)+_
   omega
 obtain ⟨x,p',rfl⟩:=mem_image.mp t; have hc:=v i x p'; change 0+(ℓ:ℤ) ≤ x i+(tic Kₜ:ℤ)*f i; omega
#print axioms ends_lac
omit Y in
lemma hcNon(x: Cover): (Halo Λ.R x).Nonempty:= ⟨_,mem_biUnion.mpr ⟨ (),mem_univ _, mem_image_of_mem _ (show (0:Cover) ∈ Kilt.stencil from (mem_union_left _ (by simp [Kilt,visits])))⟩⟩
include H S' g₀ P'
lemma iceWalk : ∃ (s:ℕ)(x y: Charm.W Kₜ)(S V:Finset Cover), Lodged Y h s K R (Φ:=Φ) (costE Y h ℓ) x y S V ∧∀ i:Axis,LeadsC (costE Y h ℓ) i S V:=by
 let D:= costE Y h ℓ; obtain ⟨n,f,f',ξ,B⟩:= indigo Y H h K R A g₀ P' ∅; let S:= LoomArea f f' Λ l; obtain ⟨c,v,N,p⟩:= B.holds D; obtain ⟨x,h₁,hx⟩:= (p.and self_mem_nhdsWithin).exists; obtain ⟨s,t,gV,r,p,hP,xp,q,fT⟩:= (h₁ hx).exists; let S':= Halo Λ.R t -- shadow S' sphere adjust
 let U:= AverPX Y h (s+1) t x hx; let V:= Φ (s+1); obtain ⟨z,q,e,rV⟩:= (fT Φ (by assumption)).grantD;
 have hZ:(LoomArea f f' Λ l).Nonempty:=⟨_,Finset.mem_union_right _ (zero_in (Λ:=Λ) (l:=l))⟩; have hz:AwayP D S' S:=fun i=>(p i).symm
 have hL: Lodged Y h (s+1) K R (Φ:=Φ) D U z S' S:=by
    refine ⟨hP,?_,?_,?_,e,hz,hcNon _,hZ⟩
    · exact litC Y h (s:=s) K R f f' (W':=z) (ξ s) (q.imp_right fun w=> Or.inr (Or.inl w)) -- order implicit named.s. liftedT $orir` family
    · obtain ⟨F,S,r⟩:= attach Y h x hx t (s+1); exact ⟨F,_,S,r⟩
    rcases q with rfl|rfl; exact Or.inl (baseK Kₜ f f'); exact inspectM .. -- tune dot inference
 obtain ⟨F,y,E',Z,f,u⟩:= orienting Y h (s+1) K R A ‹Sphere Y _ K R A Φ› U z D S' S hL; exact ⟨(s+1),F,y,E',Z,f,u⟩
#print axioms iceWalk
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
