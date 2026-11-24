import YM.SU5.FiniteGaugeData.Stent.Sinfonia
import YM.SU5.FiniteGaugeData.Strata.Dct
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
local notation "X"=> Trigo.Chamber true -- Window opened
local notation "Y₀"=> Trigo.Chamber false
local notation "Υ" n:max=> SU.Slot × Fin n
variable {n m:ℕ}
local notation "Δ"=> Fin (projCard n)
open CF.Stent Buffered.Stent
open Tint Next.Rank
variable (k:Spindle.Rules SU.group){t α:ℝ}(h:Real.exp 1≤Λ.x)
local notation "Kₜ"=> (tent Y h)
local notation "D₁"=> aliasLaw Λ
variable (f:Fin (n+1)→ X)(g':Fin (n+1)→ Y₀)(s i:ℕ)
local notation "N"=> side Y i s
local notation "σ"=> Λ.R.L
local notation "F₁"=> fieldQ Λ.R.L
local notation "IdB"=> bedfield (Λ.R.L) Λ.J.n
local notation "B"=> bedH (bedfield Λ.R.L Λ.J.n) t
-- RAW BIGNESS mask for evaluating, nodeC gather geometry.
abbrev backwood (Λ:Preparation):=scape (zeroL Λ.R.L) (sphereR (Λ.R.L.val/2) Λ.J.n)
abbrev Flatwoods (Λ:Preparation):= carpetB (zeroL Λ.R.L) (sphereR (Λ.R.L.val/2) Λ.J.n) Λ.J.n
abbrev Platform (Λ:Preparation)(t:ℝ):= bedH (Flatwoods Λ) t
noncomputable abbrev Natural (Λ:Preparation)(t:ℝ)(K:Calibration):= shunt K false (Platform Λ t) (healCare ..)
local notation "ξ"=> Auxiliary Λ t Kₜ
local notation "A₁"=> Natural Λ α Kₜ
abbrev Hairpin(Λ:Preparation)(t α:ℝ):Prop:=0<α ∧ 2*α≤t ∧ 2*α≤Λ.J.k
lemma Hairpin.choose_{x:Preparation}{t:ℝ}(p:0<t):∃ α:ℝ,Hairpin x t α:=by
 let b:= min x.J.k t; have hv:b ≤ x.J.k:= min_le_left ..; have he:b≤t:=min_le_right ..; refine ⟨b/2,half_pos (lt_min x.J.ht p),by linarith,by linarith⟩
variable (v':Hairpin Λ t α)
local notation "U"=> (Y.voyage i).CapeT s
local notation "ν"=> Neon Λ false Kₜ
local notation "μ"=> Neon Λ true Kₜ
section
variable (V:Orbit (side Y i s))
noncomputable abbrev shapeA(F:W (tent Y h)):FC (Single (side Y i s)):= sold Y h s i F.val (drawn ((Y.voyage i).CapeT s) V)
local notation "Φ"=> shapeA Y h s i V
@[simp] lemma do_one: Φ 1=1:= by unfold shapeA; rw [identityW,sold_one]; rfl
@[simp] lemma do_times (G H:W Kₜ): Φ (G*H)= Φ G*Φ H:= by unfold shapeA; rw [joinW,sold_mult]; rfl
@[simp] lemma do_sub (G H:W Kₜ): Φ (G-H)= Φ G-Φ H:= by unfold shapeA; rw [Subalgebra.coe_sub,map_sub]; rfl
@[simp] lemma do_smul (G:W Kₜ) (c:ℂ): Φ (c • G)= c • Φ G:=by unfold shapeA; rw [Subalgebra.coe_smul,map_smul]; rfl
abbrev knotC :∀ b:Bool,LinksC:= fun b=> if b then onC N (U V) else onC N V.1
local notation "A₂" b:max=> knotC Y s i V b
@[simp] lemma do_stamp {S:Finset Cover}(b:Bool)(F:LinksC→ℂ)(P:Anorak S F): shapeA Y h s i V (shunt (tent Y h) b F P)=F (knotC Y s i V b) • 1:=by cases b <;> (unfold shapeA; rw [sold_shunt] <;> rfl)
include v'
private lemma Basal (e:shapeA Y h s i V (Natural Λ α Kₜ)≠0):Agrees (backwood Λ) (A₂ false) (A₂ true) ∧ Φ (Auxiliary Λ t (tent Y h)) =1:=by
 have he:∀{x:ℝ},¬x < x:=fun {x}=>lt_irrefl _; let m:= Λ.R.L.val/2; let w:= zeroL Λ.R.L; have hR: m ≤ sphereR m Λ.J.n:= (by unfold sphereR; omega); have hx: IdB ⊆ Flatwoods Λ:= fun v u=>by obtain ⟨q,r⟩:=mem_product.mp u; exact mem_product.mpr ⟨scape_mono (Nat.add_le_add_right (Nat.add_le_add_right hR _) _) q,r⟩ -- q def?
 unfold Natural at e; rw [do_stamp] at e; have hp: Platform Λ α (A₂ false) ≠0:= fun p=>e (by rw [p,zero_smul]); have hf:= glowB α w (sphereR m Λ.J.n) Λ.J.n N V _ v'.1 v'.2.2 (posters_p Y s i) hp; have hm: Agrees (backwood Λ) (A₂ false) (A₂ true):= on_agree (side Y i s) hf; refine ⟨hm,?_⟩
 unfold Auxiliary; let X':= carpet (bedfield Λ.R.L Λ.J.n); have hv:X'⊆ backwood Λ:=sap_marks ..;
 rw [do_stamp,← bedH_local (bedfield Λ.R.L Λ.J.n) t _ _ (fun i p v=> hm i (hv p) (hv v)), bed_lords (by linarith only [v'.1,v'.2.1]) ?_,one_smul];  rintro ⟨i,p,v⟩; exact v.not_ge ((bed_works (A:=Flatwoods Λ) v'.1 hp i (hx p)).trans v'.2.1)
 -- `rw _ _ _ _`: first _ unify any conclusion with variable. choose args 
private lemma weather (e:Φ (Natural Λ α Kₜ) ≠0): Φ (Auxiliary Λ t Kₜ) =1 ∧ Φ μ=Φ ν:=by
 obtain ⟨a,b⟩:= Basal Y h s i v' V e;  have he: F₁ ⊆ backwood Λ:=scape_mono (by unfold sphereR; omega)
 refine ⟨b,?_⟩; unfold Neon; rw [do_stamp,do_stamp]; exact congrArg (fun c:ℂ=> c • (1:FC _)) ((Nylon.loc Λ.R Λ.V.tallX (A₂ false) (A₂ true) (fun i u v=> a i (he u) (he v))).symm)
#print axioms weather
end
section
variable {P:Call Λ l}{J:Wicket Λ l}{I:ℕ→Family (tent Y h)→ℕ→ℂ}{E:ℕ→Family (tent Y h)→ℂ}
variable (K:Universal Y h u v I E)(R:Rolled Y h u v J P)(A:∀ i:Axis,Repertory Y h K R i)
variable {Φ':ℕ→ W (tent Y h)→ₗ[ℂ]ℂ} (S':Sphere Y h K R A Φ')
include S'
lemma makes (F F': W Kₜ)(p:∀ (i:ℕ)(V:Orbit (side Y i s)),shapeA Y h s i V F= shapeA Y h s i V F'): Φ' s F=Φ' s F':=by
 obtain ⟨S,q⟩:= testimony Kₜ (F-F'); let a:= F-F'; let Q:= reading Kₜ S a q; let C:=‖Q‖+1; have hc:0<C:=by unfold C; positivity
 apply sub_eq_zero.mp; rw [←map_sub]; by_contra t; let u:= Φ' s a; have ht:0<‖u‖:=norm_pos_iff.mpr t; have hu:Stratus.SupplyP Y h S s (fun _=> Q):=by
    intro i p'; refine Eventually.of_forall fun x=>?_ ; have h:shapeA Y h s i x (F-F')=0:=by rw [do_sub,p,sub_self]
    unfold Q; simp_rw [reading_p]; exact h ▸ tendsto_const_nhds -- Eq substitution wrong
 obtain ⟨i,E⟩:= (Stratus.flex Y h K R A S s (fun i=>a) (fun i=>q) C hu (fun i=> le_add_of_nonneg_right zero_le_one) hc (half_pos ht)).exists; exact (E Φ' S').not_gt (half_lt_self ht) -- params. tune
include v'
-- Haar bills.L.signed reading at s+1 on EVERY nonflat, auxiliary prices removed from observable, any multiply probe.Algebra hardware. Need no guess kernel-limit support movement.
lemma abandon (G G': W Kₜ)(c:ℂ)(Y':Auxiliary Λ t Kₜ * G= c •(Auxiliary Λ t Kₜ*(μ*G'))) (X': W Kₜ): Φ' s (X'*(Natural Λ α (tent Y h)*G))= c * Φ' s (X'*(Natural Λ α (tent Y h)*(ν*G'))):=by
 rw [←smul_eq_mul c,← map_smul]; apply makes Y h s K R A S'; intro i W; let l:= shapeA Y h s i W; simp_rw [do_smul,do_times]; by_cases p:l A₁=0; · change _*(l A₁*_)=c • (_*(l A₁*_)); rw [p,zero_mul,zero_mul,mul_zero,smul_zero]
 obtain ⟨a,q⟩:= weather Y h s i v' W p; have hx:= congrArg (shapeA Y h s i W) Y'; simp_rw [do_smul,do_times] at hx; rw [a,one_mul,one_mul,q] at hx; rw [hx]; simp_rw [Algebra.mul_smul_comm] -- occurrence p
#print axioms makes
#print axioms abandon
end
end FlakeNight
end Sesame
end Chiffon
end YM.CF.Buffered.Afterglow.Hierarchy.LyraBill
