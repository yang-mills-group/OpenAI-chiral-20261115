import Bay.E.Axis
import Bay.E.Inlay
import Bay.Rosace

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 3000
set_option synthInstance.maxSize 24000
set_option quotPrecheck false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Bay
open Function Filter Topology NormedSpace Lattice Wilson Fock Pastry Scree Sault Sour Stax Skye Jet Scroll Finset Palot Cadre Vow
open RG MeasureTheory Rue
open Metric Drapes Tulip Lat Branch Cube Tenant
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Topology Classical
attribute [local instance] opCStarAlgebra
open Rush SU Tap Levier Thera Oath Font Spire Dial Rill
open Kennel Swell


namespace Silk
open Buffered Lifted D StressExchange

open Buffered.Afterglow.Tower SlabMark
open Girt
open scoped YM.CF.Buffered

local notation "Ways" => Buffered.Family

open Py Py.Rate LocalLimit Preparation Buffered.Afterglow Journey Tower Tapestry VacuumSelection
local notation "VΩ"=>VacuumSelection.Spine
set_option maxRecDepth 5000


variable {α:Type}{o:Cover}{b:ℕ}{f:Silo α o b}
variable {K:Calibration}{N:Side}

lemma givenW (n:Side)(e:K.c n=N)(j:α):arrange _ _ e (wing K f j n)=winN _ f j:=by subst N; rfl
lemma givenN(n:Side)(e:K.c n=N):arrange _ _ e (nips K f n)=nipsN _ f:=by subst N; rfl
abbrev instrument(w:Berth): Ways w.P.calibration→ₗ[ℂ] Mark w.side:= exhibit w.P.run w.P.large w.s w.i

variable {w:Berth}
local notation "ce" => wrap w.side -- origin matter site
lemma atN {S:Finset Cover}{x: Ways w.P.calibration}
   (p:InTest w.P.calibration true S false x)
   (e:AtEase S w.side)(h:covariant (instrument w x)):
   Neutral _ x:=by
 let n:=momentm w.P.run w.i w.s
 have y:= terrain w.P.run w.P.large (w.P.run.ir w.i) w.s
 refine onceNeutral (m:=n) p (show Satin.Hosp S _ from ?_) ((ct y _).mp h)
 exact ⟨y.symm▸e⟩
where
 ct{R M:Side}(g:R=M)(D:Mark R):covariant (arrange _ _ g D) ↔ covariant D:=by subst M;rfl

def grain (w:Berth)(x:Site w.side)(F:w.First):Foal Axis w.side:=
 ⟨fun i=>bayonet w.K w.p (node x) (F.J i),bayonet w.K w.p (node x) F.X⟩
abbrev sticker (w:Berth)(z:Cover)(F:w.First)(b:ℕ): Silo Axis (nodeC z) b:=ingo _ _ (grain w (wrap _ z) F)
variable {F:w.First}{a c L t d:ℝ}{m:ℕ}{z:Cover}

-- poses align independent of extraction
abbrev XC (w:Berth)(x:Site w.side)(F:w.First)(i j:Axis)(u:ℤ):Stencil w.side:=
    tooth w.K w.p x (x+wrap w.side (u • Lattice.step i)) (F.J j)

structure Button(w:Berth)(F:w.First)(L t d:ℝ)(z:Cover)(b:ℕ):Prop where
 pay: ∀i,SilkPay (nodeC z) b t d L (sticker w z F b i)
 atJ(j:Axis):instrument w (wing _ (sticker w z F b) j)=toMark (toothAt w.K w.p (wrap w.side z) (F.J j))
 atZ:instrument w (nips _ (sticker w z F b))=toMark (blankS w.K w.p (wrap w.side z) F.X)
 holds(j):Neutral _ (wing w.P.calibration (sticker w z F b) j)
 hue:Neutral w.P.calibration (nips _ (sticker w z F b))
 oriented(i j:Axis)(u:ℤ):instrument w (chime _ i u (wing _ (sticker w z F b) j))=toMark (XC w (wrap w.side z) F i j u)

lemma quilt (r:w.Rig a c m)(v:w.Before a L m (ce z) F)
 (g:w.p.B=b)(d₁:w.th=t)(d₂:w.d=d)
 (e:AtEase (Band (nodeC z) b) w.side):
 Button w F L t d z b:=by
 subst d
 let h:=Berth.clearance r
 have hp:hymnT w.p (w.p.B/10) w.d L (nodeC z) (grain w (ce z) F):=by
   rw[show nodeC z=nodeC z from rfl] -- tmp
   constructor
   · intro i
     rw[←node_of]
     exact saleAwning h (boxSeal (v.arm i) r.pulse.hint.le)
   rw[←node_of]
   exact saleAwning h (boxSeal v.stone r.pulse.hint.le)
 have h1:=inPay g (r.threshold.trans d₁) (g ▸ Nat.div_le_self _ _) e hp

 obtain ⟨hn,hj⟩:=inExact g (by omega) e hp
 let n:=momentm w.P.run w.i w.s
 have q:=terrain w.P.run w.P.large (w.P.run.ir w.i) w.s
 let R:=sticker w z F b
 have hangs:Hangs t w.d L (fun _ :ℕ=>R) R:=⟨fun i _=>h1 i,h1,fun i=>Metric.tendstoUniformly_iff.mpr fun ε p=> Eventually.of_forall fun i x=> lt_of_eq_of_lt (dist_self _) p⟩
 obtain ⟨u,s⟩:=hangs.bloom w.P.calibration
 have pubZ : instrument w (nips _ R)=toMark (blankS w.K w.p (ce z) F.X):=(givenN n q).trans hn
 have pubJ (j): instrument w (wing _ R j)=toMark (toothAt w.K w.p (ce z) (F.J j)):= (givenW n q j).trans (hj j)
 refine ⟨h1,pubJ,pubZ,fun j=>atN (s j|>.landing) e ?_,atN u.landing e ?_,?_⟩
 · rw [pubJ]
   exact (atomDyed h (boxSeal (v.arm j) r.pulse.hint.le)).pay.paid
 · rw[pubZ]
   exact (glint_fit (saleAwning h (boxSeal v.stone r.pulse.hint.le))).paid
 intro i j g
 have a: instrument w (chime _ i g (wing _ R j))=
   reflMark i g (reflMark i 0 (instrument w (wing _ R j))):=(displayRef q ..).trans (congrArg _ (displayRef q ..))
 rw[a,pubJ]
 have hx:= (atomDyed h (boxSeal (v.arm j) r.pulse.hint.le)).pay.basis.mono (Finset.subset_univ _)
 exact toothChime i g (ce z) h (boxSeal (v.arm j) r.pulse.hint.le) hx
end YM.CF.Bay.Silk
