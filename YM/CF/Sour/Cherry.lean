import YM.CF.Sour.Candy
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
variable {P:BudgetPoint}{X Y Z:Aura n}{V W:Firing n}
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
variable {T' S':BeatL n}{Z':χL n κ}{d e v w:ℝ} (X:Elm n κ d e v)
-- transformations coupling Bolt.Frame.Support.X Guard.
abbrev leafJ(b:Bool)(F G:Elm n κ d e v):Prop:=∀ (x:κ)(Y:Support (More n))(V:Pane n)(y:Openc (More n) d), y.val=Tulip.profile V→ G.F (actY s Y) x (Sour.fog s d y)=realR s b (F.F Y x y)
abbrev loopF(Q:Elm n κ d e v)(b:Bool):=haloB (fun _:Unit=>Q) (fun _=> id) b ()
lemma fla(V:Elm n κ d e v)(b:Bool):leafJ s b (loopF V b) (loopF V b):=fun k Y W t v=> flash_P s _ (fun _=> id (α:=Unit)) b (fun _ _=>rfl) _ k _ _ v Y
lemma port_k (X:Elm n κ d e v)(V:κ→BeatL n)(b:Bool)(p:NearL X V)(h:∀ (s:Sweep n)(i:κ)(W:Pane n),Guard W d→ V i (Tulip.profile (flashA s W))=realR s b (V i (Tulip.profile W))):NearL (loopF X b) V:=hush_t _ (fun _:Unit=>V) (fun _=> id) b (fun _=>p) (fun s i w p _=>h s i w p) ()
abbrev Elm.tip(F: Elm n κ d e v)(G:κ→BeatL n):Prop:=NearL F G
abbrev tipQ(s:Sweep n)(u:Bool):= u.xor (det_S s)
lemma pathL(s t:Sweep n):tipQ t ∘ tipQ s=tipQ (s*t):= funext fun i=> by unfold Function.comp tipQ; rw [Bool.xor_assoc]; change _=Bool.xor i _; rw [show det_S _= _ from (show det_S (s*t)=(det_S s).xor (det_S t) from det_p ..)]
variable {b:ℝ}(A:LedgerS T' S' Z' e v w d) (D:TagT T' S' Z' d)
local notation "T0"=> Tenant.quota^2
local notation "U"=> T0*v
local notation "U0"=> T0*w
local notation "K'" => fC n S' Z'
local notation "Q'"=> κR n Z'
abbrev leB(h:Bool)(A:BeatL n)(F:κ→BeatL n)(i:κ)(x: Chin n):Op JS:=if h then F i x*(1-A x) else A x*F i x
local notation "Φ"=>fun b:Bool=> leB b T' K'
lemma meetD (A:LedgerS T' S' Z' e v w d) (D:TagT T' S' Z' d)(s:Sweep n)(i:κ)(W:Pane n)(p:Guard W d)(b:Bool) : Φ (tipQ s b) i (Tulip.profile (flashA s W))=realR s true (Φ b i (Tulip.profile W)):=by
 let X:=Tulip.profile W; let Y:= Tulip.profile (flashA s W); obtain ⟨w,v,_⟩:=heads s d i D W p; cases g: det_S s <;> cases b <;>simp only [g,Bool.xor_false,true_or,Bool.false_xor,Bool.false_eq_true, ↓reduceIte] at w v <;> (unfold tipQ; rw [g]) <;>first|exact w|exact v
-- Certified Sym Data.D.Probe.Anal.Ang ν
structure BondL (P S:BeatL n)(E:χL n κ)(v w a d:ℝ) where
 ela:Elm n κ d a v
 elt:Elm n κ d a w
 coreS:Elm n κ d a v
 cosY :Bool→Elm n κ d a v
 heel: Elm n κ d a v
 Yh:NearL ela (fun i _=> κR n E i)
 Th:NearL elt (fun i x=> fC n S E i x-κR n E i)
 Ch:NearL coreS (fun i x=> Sault.tally (P x) (tickA n) (fC n S E i x) (κR n E i))
 Hh:∀ b:Bool, NearL (cosY b) (leB b P (fC n S E))
 Hc:NearL heel (fun i x=> P x*fC n S E i x*(1-P x))
 sQ:∀ s:Sweep n, leafJ s true ela ela ∧ leafJ s true elt elt ∧ leafJ s false coreS coreS ∧ leafJ s true heel heel ∧ ∀ b:Bool,leafJ s true (cosY b) (cosY (tipQ s b))
def hull {G:κ→ BeatL n}(X:Lawn n d G e v):Elm n κ d e v:=⟨X.F,X.W,X.coat,X.store⟩
lemma hull_r{G:κ→BeatL n}(X:Lawn n d G e v):NearL (hull X) G:=fun j W _ _ _=> X.shape j W
abbrev choo (A:LedgerS T' S' Z' e v w d)(b:Bool):Elm n κ d e v:= if b then hull A.lo else hull A.hi
include D
lemma locP (i:κ)(W:Pane n)(p:Guard W d): K' i (Tulip.profile (flashA s W))-Q' i= realR s true (K' i (Tulip.profile W) - Q' i):=by
 -- include D issue tune
 have ht(X Y:Op JS):realR s true (X-Y)= bolt s X-bolt s Y:=by by_cases c:detX s.s=true <;>simp [realR,bolt,hitL,Thera.jazz,c] <;> abel
 rw [ht,intact s d i D W p,sense s d i D W p]
omit D
def compD(A:LedgerS T' S' Z' e v w d)(D:TagT T' S' Z' d) :BondL T' S' Z' U U0 e d:=by
 refine ⟨loopF (hull A.openX) true,loopF (hull A.tint) true,loopF (hull A.art) false, haloB (choo A) tipQ true, loopF (hull A.cav) true, port_k _ _ _ (hull_r A.openX) ?_, port_k _ _ _ (hull_r A.tint) ?_,port_k _ _ _ (hull_r A.art) ?_,?_,port_k _ _ _ (hull_r A.cav) ?_,?_⟩
 · exact fun s i W k=> (sense s _ _ D W k).symm
 · exact fun s i W k=> locP s D i W k -- tune implicit
 · exact fun s i W k=> (heads s _ _ D W k).2.2.2
 · apply hush_t _ (fun b=>leB b _ (fC n S' Z')); · intro b; cases b; exact hull_r A.hi; exact hull_r A.lo
   intro s i W r j; exact meetD A D _ i _ r j
 · intro s i W h; exact (heads s d i D W h).2.2.1
 intro s; exact ⟨fla s _ _,fla s _ _,fla s _ _,fla s _ _,fun b i V K t v =>flash_P s _ tipQ true pathL b i K t v V⟩ -- fla issue
end YM.CF.Sour
