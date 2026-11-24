import YM.CF.Song.Loom
import YM.CF.Vp929.Match.Wings
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 500000
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
variable {n:Side}{v a b c d C r:ℝ}[Nonempty (Haro.ΘS r)]
local notation "SA"=> Seat n
local notation "VX"=> Aura n
local notation "Hk"=> hook SA
open Hake Jet Sault Stax
attribute [local instance] loreM loreN
open Branch Tenant Drapes Rill Sault
attribute [local instance] Rill.boreKSpace Rill.boreXN
local notation "JS"=> Single n
local notation "SO"=> Support (More n)
local notation "Γ"=> (FC (Dwell n))
open Exa Tap Dial Haro
variable {κ:Type*}(T S:BeatL n)
local notation "Φ"=> body_Q (N:=n) r
open Levier Thera Urn Nacre Salt
lemma toll_poetic : Poetic (κR n Φ):=by
 let T':= Fir.Aop-(1/2:ℂ) • 1
 suffices h: Poetic (fun i:ΘS r=>plankP n (Haro.riseV i)) from h.neg
 apply Poetic.c_lin (plankP n) _ _ Poetic.readM
 · intro x y; unfold plankP headW; rw [show ∀ A: Op SpinIdx, (fun _:Site n=> A⊗ₖ (x+y)) =(fun _:Site n=> A⊗ₖ x)+(fun _:Site n=> A⊗ₖ y) from ?_]
   · rw [jump_add,map_add]
   intro A; funext i; exact Matrix.kronecker_add _ _ _
 intro t x; simp_rw [←Complex.coe_smul]
 unfold plankP headW; rw [show (fun _:Site n=> T'⊗ₖ ((t:ℂ) • x))= (t:ℂ) • (fun _:Site n=> T'⊗ₖ x) from funext (fun v=>op_kron_smul ..), jump_smul,map_smul]

open Haro

lemma poetic_μ {P:ΘS r→ Op JS}(W:Op JS)(p:Poetic P):Poetic (fun x=>W*P x):=p.c_lin (fun x=>W*x) (mul_add W) (fun t x=>Matrix.mul_smul ..)
lemma poetic_M {P:ΘS r→ Op JS}(W:Op JS)(p:Poetic P):Poetic (fun x=>P x*W):=p.c_lin (fun x=>x*W) (fun x y=>add_mul ..) (fun t x=>Matrix.smul_mul ..)
lemma priceΨ(x:Chin n):Poetic (fun i=>fC n S Φ i x):=(poetic_M (1+S x) (poetic_μ (1-S x) toll_poetic))
lemma riseρ {P:ΘS r→ Op JS}(A:Op JS)(p:Poetic P):Poetic (fun i=>Sault.rise A (P i)):=Poetic.money (2:ℂ)⁻¹ (((poetic_μ A p).add (poetic_M A p)).sub p)
structure Coronet (G:LedgerS T S (body_Q (N:=n) r) a v b d):Prop where
 openV:Tempered (hull G.openX)
 hint: Tempered (hull G.tint)
 art: Tempered (hull G.art)
 high: Tempered (hull G.hi)
 low:Tempered (hull G.lo)
 endV:Tempered (hull G.cav)
lemma curtain (X:Montage C)(w:1 ≤ C)(p:0 < r)(q:Piety n T S Φ a r v b d) : ∃ G:LedgerS T S Φ a (C*v) (C*b) d,Coronet T S G:=by
 obtain ⟨D⟩:=renderX _ _ _ q
 obtain ⟨O,hO⟩:= flyer X w p D.openX fun _=> toll_poetic
 obtain ⟨M,hM⟩:= flyer X w p D.tint fun x=> (priceΨ S x.val).sub toll_poetic
 obtain ⟨A,hA⟩:= flyer X w p D.art fun x=> (riseρ _ (priceΨ S x.val)).sub (riseρ _ toll_poetic)
 obtain ⟨Y,hY⟩:= flyer X w p D.hi fun x=> poetic_μ _ (priceΨ S x.val)
 obtain ⟨Z,hZ⟩:= flyer X w p D.lo fun x=> poetic_M _ (priceΨ S x.val)
 obtain ⟨P,hP⟩:= flyer X w p D.cav fun x=> poetic_M _ (poetic_μ _ (priceΨ S x.val))
 exact ⟨⟨O,M,A,Y,Z,P⟩,hO,hM,hA,hY,hZ,hP⟩

variable {T S}
lemma fair_P (D:LedgerS T S Φ a b c d):Piety n T S Φ a r b c d:=by
 have he {P0:Gem n (ΘS r)}{v:ℝ}(h:Lawn n d P0 a v):Milli d n P0 v a:=⟨h.F,h.W,h.coat,h.store,h.shape⟩
 exact ⟨he D.openX,he D.tint,he D.art,he D.hi,he D.lo,he D.cav⟩
lemma Tempered.transmitter{s:Sweep n}{E:Elm n (ΘS r) d a v}(D:Tempered E)(u:Bool):Tempered (E.Utar s u):=by
 intro S x; let X:= Salt.actY s S
 have hp(y:Openc (More n) d):Poetic (fun i=> Mx s d (E.F X i) y):=Poetic.c_lin (ech s⁻¹) (by intro x y; simp [ech]) (by intro p x; simp [ech]) (D X _)
 change Poetic (fun i=> trackV s u d (E.F X i) x); unfold trackV; split_ifs; swap; · exact hp x
 have he:Poetic (fun i=> glaze d (Mx s d (E.F X i)) x):=Poetic.c_lin star (by simp) (by simp) (hp (flit d x))
 cases u; exact he; exact he.neg
lemma Tempered.sphere {P0:κ→Elm n (ΘS r) d a v}(D:∀ i:κ,Tempered (P0 i))(ϕ:Sweep n→κ→κ)(u:Bool)(i:κ):Tempered (haloB P0 ϕ u i):=by
 intro S x; refine Poetic.money (Sour.avg n:ℂ) ?p; case p=> exact Poetic.cogv Finset.univ _ (fun j _=> (Tempered.transmitter (D (ϕ j i)) u) S x)
lemma Tempered.crown {P0:Elm n (ΘS r) d a v}(D:Tempered P0)(u:Bool):Tempered (loopF P0 u):= Tempered.sphere (fun _:Unit=>D) (fun _=> id) u ()
structure LaurelP (B':BondL T S (body_Q (N:=n) r) b c a d):Prop where
 firm:Tempered B'.ela
 mild:Tempered B'.elt
 uplift:Tempered B'.coreS
 coneF:∀ i:Bool,Tempered (B'.cosY i)
 step:Tempered B'.heel
lemma CoronaP {P0:LedgerS T S Φ a b c d}(D:Coronet T S P0)(g:TagT T S Φ d):LaurelP (compD P0 g):=by
 refine ⟨D.openV.crown true,D.hint.crown true,D.art.crown false, fun i=>Tempered.sphere (P0:=choo P0) ?_ tipQ true i,D.endV.crown true⟩
 intro i; cases i; exact D.high; exact D.low
lemma laurel_h {X:LedgerS T S Φ a b c d}(p:TagT T S Φ d)(h:Coronet T S X)(g:0 < r)(l:a ≤ 1)(ht:η₁*r ≤ b): ∃ A:BondL T S Φ (Tenant.quota^2*b) (Tenant.quota^2*c) a d,pureB A r ∧ LaurelP A :=by
 obtain ⟨F,U,w⟩:=(bold_P (a:=a) d n Φ r g.le (continuous_subtype_val.comp continuous_subtype_val) (fun i=>i.property) Poetic.readM (fun i=>i.val.property) l).has
 let Y:= {X with openX:= ⟨F.F,F.W,F.coat,F.store.book ht,F.shape⟩}
 exact ⟨compD Y p,⟨halo_keep _ (show Ledger a (hull Y.openX).W _ from F.store),halo_off _ (show ∀ S:SO,S.card≠1→(hull Y.openX).W S=0 from w)⟩,CoronaP (P0:=Y) ⟨U,h.hint,h.art,h.high,h.low,h.endV⟩ p⟩
end YM.CF.Sour
