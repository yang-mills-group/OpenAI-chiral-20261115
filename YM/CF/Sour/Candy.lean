import YM.CF.Sour.Stip
import YM.CF.Sour.Plate
import YM.CF.Ione.Tape
import YM.CF.Ione.Rake
import YM.CF.Exa.Water
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Sour
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open Skye Scree Cadre Palot
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
open Cube Lat Tulip Fock Rush Scroll Paige Vault Phase Acorn Spire
open Pastry Vow Rue
attribute [local instance] opCStarAlgebra
variable {n:Side}
local notation "SA"=> Seat n
local notation "VX"=> Aura n
local notation "Hk"=> hook SA
open Hake Jet Sault Stax
attribute [local instance] loreM loreN
variable {P:BudgetPoint}{X Y Z:Aura n}{V W:Firing n}{D:Support (More n)}
open Branch Tenant Drapes Rill Sault
attribute [local instance] Rill.boreKSpace Rill.boreXN
local notation "JS"=> Single n
local notation "SO"=> Support (More n)
local notation "Γ"=> (FC (Dwell n))
open Exa Tap Dial
-- sweep weight.TIO. openc slice.S.inverse. erosion
open Levier Thera Urn Nacre Salt
variable (s t:Sweep n)(a:ℝ)
local notation "p₀"=> s.charge
local notation "x₀"=> castX s
local notation "T"=> γS s
local notation "Ω"=> Openc (More n) a
-- real quarry stitches, frame max constants preserve before.L. Only Real lemma Focus perf stencils, new Lawn.s sigma orientation.Open τ.
variable {κ:Type}[TopologicalSpace κ][Nonempty κ]
-- axis behavior.Tag conditions. REAL only.
variable {T':BeatL n}{S':BeatL n}{Z':χL n κ}(v:κ)
open Tap
local notation "φ"=> Tulip.profile
abbrev TagT (U_ S:BeatL n)(Z:χL n κ)(d:ℝ):Prop:=∀ (x:Pane n),Guard x d→IsStarProjection (U_ (Tulip.profile x)) ∧ ∀ (s:Sweep n),let p:=U_ (Tulip.profile x)
 let y:=flashA s x
 U_ (Tulip.profile y)=swapX (det_S s) (ech s p)∧ S (Tulip.profile y)=bolt s (S (Tulip.profile x))∧∀ i,Mind (Z i) -- notation same issue
lemma plight (z:Op SU.Slot)(p:Mind z):bolt s (plankP n z)=plankP n z:=by
 let R:= detX s.s; let Z:=waveB z; let U:=spinU s.charge s.s; let A:=plankP n z; let H:=jump (Equiv.refl (Site n)) (fun _=>Z); have h :plankP n z=love n H:=rfl
 let K:=mealU x₀ U (xtra p₀) n; let V:= sings p₀ K H
 have he(i j:Site n):Scroll.tap H i j= if i=j then Z else 0:=by
    ext x y; change jump (Equiv.refl (Site n)) (fun _=>Z) (i,x) (j,y)= _; rw [jump_apply]; by_cases p:i=j<;>simp [p]
 have hp: sings p₀ (spinQ U (xtra p₀)) Z= Thera.jazz R Z:=(symWave _ p).rise _ _ _ (spinZ p₀ s.s) 0 (by simpa [bout_zero] using bout_h 0 0 (by norm_num))
 have ht : V= Thera.jazz R H:=by
    suffices h:∀ i j:Site n,Scroll.tap V i j= Scroll.tap (Thera.jazz R H) i j by ext ⟨i,b,c⟩ ⟨j,d,e⟩; exact Matrix.ext_iff.mpr (h i j) (b,c) (d,e)
    intro i j
    have hl: Scroll.tap (Thera.jazz R H) i j=if i=j then Thera.jazz R Z else 0:=by
       by_cases g:i=j; · subst j; rw [if_pos rfl]; cases R; exact he i i|>.trans (if_pos rfl); change -(Scroll.tap (star H) i i)=_; rw [tap_s,he i i,if_pos rfl]; rfl -- tune
       rw [if_neg g]; cases R; · change Scroll.tap H i j=_; rw [he,if_neg g]
       change -(Scroll.tap (star H) i j)= _; rw [tap_s,he,if_neg (Ne.symm g),star_zero,neg_zero]
    rw [hl,tap_sg,he]; by_cases q:i=j; swap
    · rw [if_neg q,if_neg ((Tofu x₀ _).injective.ne q),win_z,mul_zero,zero_mul] -- order
    subst j; rw [if_pos rfl,if_pos rfl]; change sings p₀ (milU x₀ U (xtra _) i) Z=_; rw [Scroll.wingM]; exact hp
 unfold bolt hitL; rw [h, Scroll.wingX]; change Thera.jazz R ((love n) V)=(love n) _; rw [ht] 
 cases R; rfl; simp only [Thera.jazz,ite_true,map_neg,map_star,star_neg,star_star,neg_neg]
variable (p:TagT T' S' Z' a)(U:Pane n)(t': Guard U a)
local notation "Yc"=> φ U
local notation "Yk"=> φ (flashA s U)
local notation "Q'"=> κR n Z'
local notation "K'"=> fC n S' Z'
local notation "A'"=> T'
local notation "P₀"=> tickA n
include p t'
lemma sense :bolt s (Q' v)=Q' v:=by
 let A:=plankP n (Z' v); have he:=plight s (Z' v) ((p U t'|>.2 s).2.2 _)
 have hv:bolt s (-A)= -(bolt s A):=by unfold bolt hitL Thera.jazz; split <;>simp
 rw [κR,hv]; exact congrArg Neg.neg he
lemma intact: bolt s (K' v Yc)= K' v Yk:=by
 let A:=S' (φ U); let Pz:=Q' v; change hitL p₀ (det_S s) (γS s) ((1-A)*Pz*(1+A))=(1-S' _)*Pz*(1+S' _); rw [←Sault.rake,(p U t'|>.2 s).2.1, show hitL p₀ (det_S s) (γS s) Pz=_ from sense s a v p U t'] -- wrong rw RHS;

lemma heads :let V:= A' Yc*K' v Yc; let W:= K' v Yc * (1-A' Yc)
 A' Yk*K' v Yk=bolt s (if det_S s then W else V)∧ K' v Yk*(1-A' Yk)=bolt s (if det_S s then V else W)∧ A' Yk*K' v Yk*(1-A' Yk)= bolt s (A' Yc*K' v Yc*(1-A' Yc)) ∧ Sault.tally (A' Yk) P₀ (K' v Yk) (Q' v)=foeL s (Sault.tally (A' Yc) P₀ (K' v Yc) (Q' v)):=by
 intro V W; let q:= K' v Yc; let x:= A' Yc; let R:=det_S s; let A:= (A' Yk); have he:A=swapX R (ech s x):= (p U t'|>.2 s).1
 rw [show T' _=_ from he, ←intact s a v p U t']; obtain ⟨hq,hv,ht,hl⟩:= Sault.gild p₀ R (γS s) x q ((p U t').1.isSelfAdjoint)
 refine ⟨hq,hv,ht,?_⟩; have hx: swapX R (ech s (tickA n))=tickA n:=by rw [touchP,show ech s _= swapX R (cutM (Tset n)) from tickR x₀ (xtra p₀) (spinU p₀ s.s) (spinZ p₀ s.s) n]; cases R<;>simp [swapX] -- shadow mv
 have hg: star (tickA n)=tickA n:=by rw [touchP]; exact (cutM_idp ..).isSelfAdjoint
 have hp: Sault.rise P₀ (Q' v) =foeL s (Sault.rise P₀ (Q' v)) :=by
    nth_rw 1 [←sense s a v p U t']; nth_rw 1 [←hx]; exact (Sault.gild p₀ R T (tickA n) (Q' v) hg).2.2.2
 have hu(A B:Op JS): foeL s (A-B)=foeL s A-foeL s B:=by unfold foeL doveL; split <;>simp
 unfold Sault.tally; rw [hl,hu,←hp]
end YM.CF.Sour
