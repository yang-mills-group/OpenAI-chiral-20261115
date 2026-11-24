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
-- ACT relative.Seen.Real.Guard.
variable {d e v:ℝ}{A:Type*}(E:Elm n κ d e v)(F:κ→BeatL n)
abbrev NearL(E:Elm n κ d e v)(F:κ→BeatL n):Prop:=∀ i,∀ (x:↥(Openc (More n) d)),∀ V:Pane n,Guard V d → x.val=Tulip.profile V → F i x.val=∑ S,E.F S i x
lemma share (W:Pane n)(v:Guard W d):Guard (flashA s W) d:=keepC (xtra s.charge) (castX s) W d v -- tune
lemma storm_P {P:Sweep n→Elm n κ d e v}(x:∀ i,NearL (P i) F):NearL (chime P) F:=by
 intro i u W p h; change _=∑ Y:SO,(↑(avg n):ℂ) • (∑ k:Sweep n,(P k).F Y i u); rw [←smul_sum,sum_comm]; simp_rw [←show ∀ k:Sweep n,F i u.val=_ from fun k=>x k i u W p h,sum_const,card_univ]; rw [avg_s]
variable (P0:A→Elm n κ d e v)(f:A→ κ→BeatL n)(ϕ:Sweep n→A→A)(u:Bool)(m:∀ s t:Sweep n, ϕ t ∘ ϕ s= ϕ (s*t))
def haloB(a:A):Elm n κ d e (Tenant.quota^2*v):=chime fun s=>(P0 (ϕ s a)).Utar s u
local notation "Μ'" x:max=> haloB P0 ϕ u x
include m
lemma flare_o(j:A)(k:κ)(S:SO)(W:Pane n)(x:↥(Openc (More n) d))(h:x.val=Tulip.profile W)(i:Sweep n):((P0 (ϕ i (ϕ s j))).Utar i u).F (actY s S) k (Sour.fog s d x)=realR s u (((P0 (ϕ (s*i) j)).Utar (s*i) u).F S k x):=by
 let Y:=Sour.fog s d x; let V:= flashA s W; have ht:Y.val=Tulip.profile V:=real_box s d _ _ h
 have hx(S: Sweep n): (Sour.fog S d Y)= Sour.fog (s*S) d x:=Subtype.ext ((real_box S d V Y ht).trans ((congr_arg Tulip.profile (show flashA S V=flashA (s*S) W from lights s S W)).trans (real_box (s*S) d W x h).symm)) -- tune orientation
 rw [show ϕ i (ϕ s j)= ϕ (s*i) j from congrFun (m s i) j]; let T':= P0 (ϕ (s*i) j); rw [T'.wren i u (actY s S) k V Y ht, hx, T'.wren (s*i) u S k W x h,Ione.tape_B, vale_d, mul_inv_rev, inv_mul_cancel_right]
omit m
variable (pF:∀ i,NearL (P0 i) (f i))
variable (h:∀ (S:Sweep n)(i:κ)(W: Pane n), Guard W d→∀ j:A,f (ϕ S j) i (Tulip.profile (flashA S W))=realR S u (f j i (Tulip.profile W)))
include pF h
lemma hush_t (i:A): NearL (Μ' i) (f i):=by
 apply storm_P; intro t j x V v l; let E:= P0 (ϕ t i); rw [show f i j x.val= realR t⁻¹ u (realR t u (f i j x.val)) from ?_, l,←h t j V v i, ←real_box t d V x l,pF _ _ _ (flashA t V) (share t V v) (real_box t d V x l), real_f]; swap; · rw [vale_d,mul_inv_cancel,real_i]; -- tune
 symm; refine sum_bij (fun x _=>actY t x) (fun _ _=>mem_univ _) (fun i _ j _ g=>map_injective _ g) (fun i _=>⟨actY t⁻¹ i,mem_univ _,?_⟩) ?_; · ext; simp [actY,sitU]
 intro i v; exact E.wren t u i _ _ _ l -- shadow
omit h pF
include m
-- Dim.ch.F
lemma flash_P (j:A)(i:κ)(W:Pane n)(x:↥(Openc (More n) d))(h:x.val=Tulip.profile W)(S:SO): (Μ' (ϕ s j)).F (actY s S) i (Sour.fog s d x) = realR s u ((Μ' j).F S i x):=by
 let Y:=Sour.fog s d x; change (avg n:ℂ) • (∑ J:Sweep n,((P0 (ϕ J (ϕ s j))).Utar J u).F (actY s S) i Y)=realR s u ((avg n:ℂ) • (∑ J:Sweep n,((P0 (ϕ J j)).Utar J u).F S i x)); rw [real_t s u,real_f s u]; refine congrArg (((avg n:ℂ) • ·):Op JS→ Op JS) ?_
 refine sum_bij (fun (a:Sweep n) _=> s*a) (fun _ _=>mem_univ _) (fun a _ b _ g=>mul_left_cancel g) (fun q _=>⟨s⁻¹*q,mem_univ _,mul_inv_cancel_left ..⟩) (fun a _=>flare_o s P0 ϕ u m j i S W x h a)
end YM.CF.Sour
