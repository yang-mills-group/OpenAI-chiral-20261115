import YM.SU5.Same.BareProbe
import Velour.Quilt.Sleek
import YM.SU5.Aria.Impresario
/-!
# Withdrawing the physical comparator 
-/
set_option autoImplicit false
set_option maxHeartbeats 1050000
set_option synthInstance.maxSize 28000
set_option maxRecDepth 4500
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common Ballad Cordial
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
open Germ Alliance Lamour.Bridge.Celeste Designs Twah Prototype
open Lamour.Bridge.Celeste.Morn
namespace Spine
open Aria Casting Six OS.Semigroup.Balloon



open MacroGrid SatinNucleus Velour

open SatinJets OS.Semigroup

variable (P:Spine)(j:Axis)(x:P.Spectrum0 j)
lemma Apron.kissed (D:P.Apron)(a:ℝ):
 star (D.velour P j x a)=(D.kiss P j).velour P j x a:=by
 unfold velour dye
 rw [(P.physicalEnergy j x).star_pad,D.peer P j x, D.kiss_width]
variable {P j x}{T:ℕ→P.Apron}
lemma Veloured.mirrorGleams (h:P.Veloured j x T){t:ℝ}(p:0<t) :
   Gleams (P.ColorHil j x) (fun i=> ((T i).kiss P j).velour P j x t) (star (h.printOp t)):=by
 have v:= (h.printed p).swap
 rwa [show (fun i=>star ((T i).velour P j x t)) = (fun i=> ((T i).kiss P j).velour P j x t) from
            funext fun i=> Apron.kissed P j x (T i) t] at v
lemma Veloured.mirror (h:P.Veloured j x T) :
    P.Veloured j x (fun i=> (T i).kiss P j):=by
 refine ⟨h.thin,fun t p=>⟨_,h.mirrorGleams p⟩,?_⟩
 simp_rw [← Apron.kissed,norm_star]
 exact h.bill
lemma Veloured.mirror_print (h:P.Veloured j x T){a:ℝ}(p:0<a):
   h.mirror.printOp a=star (h.printOp a):=(h.mirror.printed p).unique (h.mirrorGleams p)


end Spine
namespace Spine
open Aria Casting Six OS.Semigroup.Balloon MacroGrid SatinNucleus Velour SatinJets
variable (P:Spine) (Z:Lead.Clan)(x:P.Spectrum0 3)(G:P.Apron)
variable {s:ℕ}(n:ℕ)
local notation "ξ"=> P.advocate 3 x 3
local notation "σ"=> P.physicalEnergy 3 ξ
local notation "D₀"=>P.stitchApron Z G s n
local notation "G₀"=>P.gaugeStitch Z G s n
local notation "π'"=> (purePrice Z:ℂ)
local notation "e"=> (G₀).realWidth P 3
local notation "d"=> G.realWidth P 3
local notation "Q"=> P.shifts 3
local notation "F"=>Q (G.zoom P s 3) (G.full P s)

lemma silver_gauge (h:G.s ≤ s){t:ℝ}(p:e ≤t):
 (G₀).velour P 3 ξ t=π' • G.dye P 3 ξ (t+d) (t-d):= by
 let u:=(G₀).u 3
 have q:= (P.unstitch Z n G ξ h).smul π'
 have y:π' • (Q u (F))= Q u (G₀).F:= (map_smul (Q u) π' (F)).symm
 have r:= (G₀).sewn (j:=3) (x:=ξ)
 have f:=r.unique (q.mono rfl y)
 have b:2*d≤e:=P.doubled_width Z n G h
 have z:=G.real_width_pos P 3
 have Y:=G.dye_twice P 3 ξ (show d≤e+d by linarith only [b,z])
    (show d≤e-d by linarith only [b]) (show e+d≤t+d by gcongr) (show e-d≤t-d by gcongr)


 rw [add_sub_add_right_eq_sub, sub_sub_sub_cancel_right] at Y
 change (σ).pad (t-e) (t-e) ((G₀).engine P 3 ξ)=_
 have eq:e=(D₀).realWidth P 3:=rfl
 rw [←eq] at f
 rw [f,map_smul,Y]

end Spine
namespace Spine
open Aria Casting Six OS.Semigroup.Balloon MacroGrid SatinNucleus Velour SatinJets
variable (P:Spine) (Z:Lead.Clan)
local notation "π₀"=> (purePrice Z:ℂ)
variable (x:P.Spectrum0 3)(A:ℕ→P.Apron) {c r n:ℕ→ℕ}
local notation "ξ"=> P.advocate 3 x 3
local notation "σ"=> P.physicalEnergy 3 ξ
local notation "𝒞"=> P.ColorHil 3 ξ
local notation "τ"=> P.macroStep
variable (m:P.HandleWith x c r A n) (h:P.VelvetHandle c r A x n)
  (v:P.Veloured 3 (P.advocate 3 x 3) A)
local notation "Q₀" i:max=> (P.stitchApron Z (A i) (c (n i)) (r (n i)))
local notation "G₀" i:max=> (P.gaugeStitch Z (A i) (c (n i)) (r (n i)))
local notation "d" i:max=> (A i).realWidth P 3
variable (g:Tendsto (fun i=> (P.stitchApron Z (A i) (c (n i)) (r (n i))).realWidth P 3) atTop (𝓝 0))
include g m


lemma dull: P.readyDye ξ (fun i=>G₀ i) (fun t=>π₀ • v.printOp t):=by
 have u:Pays (𝒞) τ (fun t i=> (A i).dye P 3 ξ (t+d i) (t-d i)) v.printOp:= by
    refine v.seen.grounds («d»:=fun t=>t) fun t p=>⟨half_lt_self p,?_,?_⟩
    · simpa using v.thin.const_add t
    simpa using (tendsto_const_nhds (x:=t)).sub v.thin
 refine ⟨g,(u.smul π₀).agree P.macroStep_pos (fun t p=> ?_) fun _ _=>rfl⟩
 exact (g.eventually_le_const p).mono fun i b=> (P.silver_gauge Z x _ _ (m.already _) b).symm

include h
lemma bright:P.readyDye ξ (fun i=>Q₀ i) (fun t=>π₀ • v.printOp t):=
  ⟨g,P.stitch_printed Z x A m h v g,
     (P.stitched_cap Z x A m h v g).bill⟩
variable (W:Lead.Clan→Prism)
local notation "TS"=> P.soldTrumpet A c r n W Z
local notation "TG"=> P.gaugeTrumpet A c r n W Z
local notation "L"=> trims (σ) (W Z) (fun t=>π₀ • v.printOp t)
lemma combed: P.readyDye ξ TS L ∧ P.readyDye ξ TG L:=
  ⟨(P.bright Z x A m h v g).crop _,(P.dull Z x A m v g).crop _⟩


omit g
variable {K:P.Register}{R:P.Ellis 3 x}
theorem combed_night (z:P.Experiment K c r x R):
   P.readyDye ξ TS L ∧ P.readyDye ξ TG L:=
  P.combed Z x A m h v (P.night_stitch Z x A m h v z|>.thin) W
include v
/-- In particular: these two particular charges, the ACTUAL mixed
soldTrumpet, and the lamp removed and replaced with a scalar, are
identical if judged on full two-sided positive-heat operator norm-costed
strong star (i.e. caps with operator-norm PRICE, strong star convergence).
We don't need to project. Holds with every clan.
-/
theorem combed_night' (z:P.Experiment K c r x R):
   ∃(s:P.Veloured 3 ξ TS) (u:P.Veloured 3 ξ TG),
      ∀ t:ℝ,0<t→ s.printOp t = u.printOp t:=by
 obtain ⟨q,w⟩:= P.combed_night Z x A m h v W z
 exact ⟨q.gets,w.gets,fun _ a=> (q.dyes a).trans (w.dyes a).symm⟩

#print axioms combed_night'
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
