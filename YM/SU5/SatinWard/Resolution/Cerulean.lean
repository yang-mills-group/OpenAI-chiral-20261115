import YM.SU5.SatinWard.Resolution.Presidential
import Velour.Board.Birth
import ForceSatin.Ramp
import ForceSatin.SwitchC
set_option autoImplicit false
set_option maxHeartbeats 520000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Py
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
open Lich.Muster Lor
open Jet Vol Rel
local notation "G5"=>SU.group
open Cascade
open Fief
open Yaw Pig
open Wray
open Lich.Muster Push.AbsoluteSums
open Iva Eire
open Trees Footprint Iva Eire
open Jade
open Oath Feu Feu.Corset Nor
open Chaff Gloss Maize Tye RP RP.Str
open Brace
namespace Rate
open Pitching Focus CF.Mint
namespace LocalLimit
open Preparation
variable {P:Preparation}{l:ℕ}(Y:Course P (VolumeCape.Dream.Nimbus l))

open Buffered
open CF.Pannier.Damask
open YM.CF.Velvet
open Pannier
namespace Papal
local notation "ℶ" => hat P.R.L P.x
local notation "💠" => P.K.j
open CF.Papyrus.Franc Verses CF.Pannier.Chancel Checkers Flint Gleam Gleam.Luster Gleam.Luster.Almanac Grade Graph
local notation "pio"=> P.R.L
open CF.Window CF.Velvet CF.Pannier.Damask

open CF.Papyrus.Franc.SatinForce
open Pannier
local notation "nₛ" s:max i:max => count Y s i
local notation "χf" x:max => parcelF x
open CF.Lamour CF.Lamour.Bridge.Celeste Afterglow Journey

open _root_.YM.Gleam.Luster.Risa Gentle Tiling
open BProof (scaleY PL)
open _root_.YM.Work.F03 _root_.YM.Regis
local notation "Uₛ" s:max i:max k:max => gram Y s i k
local notation "Kₛ" s:max k:max => Y.uv k - s
local notation "π₀"=> P.K.top.clip


-- Wick checker on the whole Presid bargain, no matter if formed using `Veil...'
open Afterglow.Tower Afterglow.Tower.SlabMark
open Tapestry
namespace SkyTax
open VelourBoard
local notation "Β" =>P.block
variable {b C:ℝ} (m:ℕ) (rate:ℝ)
variable (s i k:ℕ)(H:Real.exp 1 ≤ P.x)
local notation "K" => tent Y H
local notation "N₀" => Journey.side Y i s
local notation "rσ" => coveredWidth P.R.L (hat pio P.x s)
noncomputable abbrev waxPage (rate:ℝ) (m:ℕ) {c:Side} {r:Lattice.Ratio c (More (Journey.side Y i s))} (T:Tiling c (Journey.side Y i s) r) (q:Wave (Single (Journey.side Y i s))) :=
 let t:= hat pio P.x s
 Page (Journey.side Y i s) T pio m (P.V.L.mood (Y.uv k-s)) (P.V.L.tied (Y.uv k-s)) (Uₛ s i k).p rate (Uₛ s i k).beta t (coinD t) (foamD t) (coinD t) (rayD t) q
variable {m rate s i k}
noncomputable abbrev waxMark {c:Side}{r:Lattice.Ratio c (More (Journey.side Y i s))}{T:Tiling c (Journey.side Y i s) r}{q} (A:waxPage Y s i k rate m T q) := (1+toMark A.test_: Mark (Journey.side Y i s))
local notation "tℋ"=> hat pio P.x s
-- disjointness & feasibility for any Page in cubicles; no specialized loans for tilted K. PencilHeight reusable.
abbrev Dapper (K₁:Calibration) (_o:VelourBoard.Cell) (w:ℕ) (A:ℝ) := (↑(2*pitch K₁ w:ℕ):ℝ)^4 ≤ poseTill A -- `o` open future
lemma capitalization (K₁:Calibration)(w:ℕ)(A:ℝ) {f:Buffered.Family K₁} (d:List (VelourBoard.Tile K₁)){m':Side}{L U o:VelourBoard.Cell}(h:Deck m' w o f d L U) (v:Dapper K₁ o w A) : sites (K₁.c m') ≤ d.length*poseTill A:=by
 apply le_trans (b:= d.length*((↑(2*pitch K₁ w:ℕ):ℝ)^4)) _ (mul_le_mul_of_nonneg_left v (Nat.cast_nonneg _))
 have hm:= h.fill.1
 unfold sites
 exact_mod_cast (show (More (K₁.c m')).val^4 ≤ d.length*(2*pitch K₁ w:ℕ)^4 from by change ((K₁.c m').val*2)^4 ≤ _; linarith only [Nat.mul_le_mul_left 16 hm])
variable {c:Side} {r:Lattice.Ratio c (More (Journey.side Y i s))}{T:Tiling c (Journey.side Y i s) r} {w:ℕ} {U:Support (More (Journey.side Y i s))}{q:Wave (Single (Journey.side Y i s))}{o:VelourBoard.Cell}
def waxBox (w:ℕ)(o:VelourBoard.Cell) (a:VelourBoard.Cell) (C:waxPage Y s i k rate m T q) := ∀ y∈C.S, Shield K w o (K).ℓ a y -- w o explicit below
variable (G:waxPage Y s i k rate m T q) {M:Male}(h:HaloTw 4 (count Y s i)) (v:Sea (FlatPaneP 4 M (count Y s i)) q)
include h v in
lemma waxTurns {a:VelourBoard.Cell}(j:Axis)(d:ℤ)(p:waxBox Y H w o a G) : ∃ G':waxPage Y s i k rate m T q, waxBox Y H w o (tipped j d a) G' ∧ reflMark j (PaneCut K w o j d) (waxMark Y G)=waxMark Y G':=by
 let J':=PaneCut K w o j d; let F':=Buffered.refl j J' G.test_; let S':= G.S.image ((Buffered.plane j J').anon (count Y s i)); let G':waxPage Y s i k rate m T q:=⟨F',S',reflW h v G.permit j J'⟩
 refine ⟨G',fun y hy=>?_,?_⟩
 · obtain ⟨z,p',rfl⟩:= mem_image.mp hy; exact VelourBoard.turned j d z (p _ p')
 funext y; let U:= carR j J' (count Y s i); change theta U (1+toMark G.test_ _) = 1+toMark (Buffered.refl j J' G.test_) y; rw [reflEval, theta_add, theta_one]; rfl
lemma waxDifferent (a b:VelourBoard.Cell){L U:VelourBoard.Cell}(fits:FitsSide K w (count Y s i) L U) (pa:RangeAt L U a)(pb:RangeAt L U b)(u:a≠b)(G':waxPage Y s i k rate m T q)(g:waxBox Y H w o a G) (g':waxBox Y H w o b G') : Disjoint G.S G'.S:=by
 apply Finset.disjoint_left.mpr; intro y hy hy'; have he:= VelourBoard.separates fits pa pb u (g _ hy) (g' _ hy'); rw [separation_self] at he; change 2*Journey.reserve P l ≤ 0 at he; unfold Journey.reserve at he; omega

structure Populus (rate:ℝ)(m s i k:ℕ):Prop where
 checks (c:Side)(r:Lattice.Ratio c (More (Journey.side Y i s)))(T:Tiling c (Journey.side Y i s) r) (p:coveredWidth pio (hat pio P.x s) r) (q:Wave (Single (Journey.side Y i s))) (v:Sea (FlatPaneP 4 (gram Y s i k).J.M (count Y s i)) q) (L:List (waxPage Y s i k rate m T q)) (d:L.Pairwise (Disjoint on Page.S))(y: sites (count Y s i) ≤ L.length*poseTill (hat pio P.x s)): ‖Journey.compass Y i k s (veilProd (Page.test_ ∘ L.get) (List.finRange L.length))‖ ≤ Real.exp (2*integralTill (hat pio P.x s))^L.length

variable (rate m)
-- Prove Populus at all s etc by Ripoff
lemma populate (p:0<b)(mail:CF.Papyrus.Franc.postage 4 b)(a:0<rate)(f:rate≤1): ∀ᶠ s:ℕ in atTop,∀ (i k:ℕ), s ≤ Y.uv k→ (Y.voyage i).kick ≤ k→ TiltWorld Y s i k b C → ChannelWorld Y s i k b C → Populus Y rate m s i k:=by
 filter_upwards [veilCommerce Y m rate a f p mail,(turnover P).eventually (roar m b),(turnover P).eventually (plaster_area 1 zero_lt_one),(turnover P).eventually_gt_atTop 0] with s h y0 v0 r i k V v1 i3 i4
 let rF:=hat pio P.x s
 constructor
 intro c r' T hV q qv L v' y
 let S₀(a:Fin L.length):= (L.get a).S
 let V₀(a:Fin L.length):= (L.get a).test_
 let A:= List.finRange L.length
 have hr:0≤rayD rF:=by unfold rayD forceDose waxRay; have hb:0<rF:=r; positivity
 let hb:= veil_purse Y rate m T hV q qv (coinD rF) (foamD rF) (coinD rF) (rayD rF) y0.1 hr ((v0 r'.count T.odd_width hV.1).1) A S₀ V₀ (List.nodup_finRange _) (show Set.PairwiseDisjoint (A.toFinset:Set (Fin L.length)) S₀ from fun a _ b _ p=>(lt_or_gt_of_ne p).elim (fun v=>v'.rel_get_of_lt v) (fun x'=> Disjoint.symm (v'.rel_get_of_lt x'))) (fun i=>(L.get i).permit)
 rw [←Real.exp_nat_mul]
 apply (h i k V v1 i3 i4 _ _ _ hb (by unfold A; rw [List.length_finRange]; exact y)).trans (Real.exp_monotone ?_); unfold A; rw [List.length_finRange]; linarith only [mul_le_mul_of_nonneg_right y0.2.1 (Nat.cast_nonneg (α:=ℝ) L.length)]

variable {rate m} {F:Buffered.Family (tent Y H)}
lemma sealC (P₁:Populus Y rate m s i k)(q':Dapper K o w (hat pio P.x s))(e: coveredWidth pio (hat pio P.x s) r)(h:HaloTw 4 (count Y s i))(v:Sea (FlatPaneP 4 (gram Y s i k).J.M (count Y s i)) q)
 (g:waxBox Y H w o 0 G)(z:exhibit Y H s i F=waxMark Y G)(d:List (VelourBoard.Tile K)) (L U:VelourBoard.Cell) (p:Deck (momentm Y i s) w o F d L U): ‖sharp Y H s i k (VelourBoard.Representation d)‖ ≤ Real.exp (2*integralTill (hat pio P.x s))^d.length:=by
 let N:= count Y s i; have hp:(K).c (momentm Y i s)=N:= terrain Y H (Y.ir i) s; have a:FitsSide K w (count Y s i) L U:=by have h:=p.fits; change FitsSide K w N L U; rw [←hp]; exact h
 obtain ⟨d',u,z',_,x'⟩:= VelourBoard.inscribe Y H s i (waxBox Y H w o) (fun W:waxPage Y s i k rate m T q=>waxMark Y W) ⟨G,g,z⟩ (fun a G0 g j d=> waxTurns Y H G0 h v j d g) p.paved (fun _=>True) (fun _ _ _=>trivial) (Disjoint on Page.S) (fun i j r s' t x' y h₁ h₂=> waxDifferent Y H x' i j a r s' t y h₁ h₂)
 rw [actualRead,z',←u,Page.swipe d' Page.test_ (fun W:waxPage Y s i k rate m T q=>waxMark Y W) (fun _=>rfl)]; apply P₁.checks _ _ _ e _ v _ x' ; have h:=capitalization K w _ d p q'; rw [hp] at h; rw [u]; exact h

end SkyTax
end Papal
end LocalLimit
end Rate
end YM.CF.Py
