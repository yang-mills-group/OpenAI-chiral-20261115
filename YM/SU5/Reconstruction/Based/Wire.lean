import YM.SU5.Reconstruction.Based.Sensor
import YM.SU5.Reconstruction.FirstWindows.Link
set_option autoImplicit false
set_option synthInstance.maxSize 32000
set_option maxRecDepth 5000
set_option maxHeartbeats 900000
noncomputable section
namespace YM.CF.Buffered.Afterglow.Rooted
open Function Filter NormedSpace Metric Lattice Wilson Laurent Finset Fock Lat Cube SU Spire Scroll Peaks Stencil Tenant Tap Tulip Branch Fir Scree Advance Reflect Window Next.Free Bloch Drapes Lifted Skye Girt Nacre Sound Tapestry Satin MeasureTheory Rush
open scoped Topology BigOperators Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace Classical
attribute [local instance] opCStarAlgebra
open WalkRoots Push.SectorMeasure
set_option quotPrecheck false
variable {S:Finset Cover}(R:RouteMap S)
namespace Orbitals
open _root_.YM.CF.Buffered.Afterglow.Tower Vacancy Selected SlabMark FirstWindows
open Centre YM.CF.Signal.Ovation.Transit
-- transporting genuine indicator of *first-field* influence even when these are used in
-- Wick frame movements (at inspecting resolution). Connect to THIS transferred U.
noncomputable def atGauge (n:Side)(x:Cover): Seat n→ E:= fun i=> if i=wrap (More n) x then SU.central else 1
noncomputable def spun (i:Axis)(z:ℤ)(x:Cover):= (plane i z).motion x
variable (K:Calibration)
def Communicates (n:Side)(x:Cover)(z:ℂ)(f: Mark n):Prop:= ∀ U U':Pane n, f (gauge (atGauge n x) U,U')=z • f (U,U')
lemma communicate_mirrors {n:Side}{x:Cover}{z:ℂ}{f:Mark n}(i:Axis)(b:ℤ)(p: Communicates n x z f): Communicates n (spun i b x) (star z) (reflMark i b f):=by
 let W:=(plane i b).anon n; have he: atGauge n (spun i b x) ∘ W=atGauge n x:=by
    funext y; have h: wrap (More n) (spun i b x)=W (wrap _ x):=(Shape.anno ..).symm
    let e:Injective W:= (show Involutive W from fling_there i b).injective
    simp only [atGauge, comp_apply,h,e.eq_iff]
 intro U V; unfold reflMark reflFields; dsimp only [Prod.map]; rw [show fling i b n (Lattice.gauge (atGauge n (spun i b x)) U)=_ from (van (plane i b) (atGauge n _) U),he,p]; exact Fock.theta_smul ..
lemma any_anchor {k:ℕ}(b: Fin k→ Cover)(W:Slot) {μ:Multiset Cover}{f:Family K}(h:f∈ raw S K (family W) b μ)(p:Neutral K f)(i:Fin k)(t:b i∈ μ)(q:Injective b)(x:nodeC (b i)∈ S){m:Side} (v:Hosp S (K.c m)) : Communicates (K.c m) (nodeC (b i)) (star (zeta W)) (f m):=by
 let R:RouteMap S:= Classical.choice (WalkRoots.routes_any S) -- tune
 have y:= fromComponent R K _ b h p
 have e: atGauge (K.c m) (nodeC (b i))=centerT (b i) (K.c m):=by unfold atGauge; rw [← node_of]; rfl -- unfold
 intro U V; rw [e]; exact (coupled R K W b i v x p y q t U V).1
noncomputable def spinCoord (i:Axis)(z:ℤ)(x:Cover): Cover:= spun i (gaugeT K z) (spun i 0 x)
noncomputable def carried(v:Cover)(x:Cover)(t:List Axis): Cover:= t.foldr (fun i=> spinCoord K i (v i)) x
lemma transport_center {n:Side}{f:Family K}{x:Cover}{z:ℂ}(t:List Axis)(v:Cover)(p:Communicates (K.c n) x z (f n)): Communicates (K.c n) (carried K v x t) z (cad K t v f n):=by
 induction t with
 | nil=>exact p
 | cons i t h=> let e:=communicate_mirrors i (gaugeT K (v i)) (communicate_mirrors i 0 h); rw [star_star] at e; exact e
lemma carried_in {x:Cover}(p:x∈ S)(t:List Axis)(v:Cover): carried K v x t∈ drivePlot v K t S:=by
 induction t with
 | nil=>exact p
 | cons i t h=>
    let T':= drivePlot v K t S; let F:=gaugeT K (v i); let Rr (x):=spun i x; let Z:= carried K v x t; change Rr F (Rr 0 Z)∈ Tower.address i F T'
    have e : Tower.address i F T'=reflectedBox i F (reflectedBox i 0 T'):=by rw [support_translation,sub_zero]
    rw [e]; exact mem_image_of_mem (Rr F) (mem_image_of_mem (Rr 0) h)
lemma shifted_detects (n:Side)(x:Cover)(z:ℂ)(f: Dome K)(h:Communicates (K.c n) x z (f.val n))(j:Axis)(p q:Cover):
    Communicates (K.c n) (spun j 0 (carried K p x ordinate)) (star z) ((FirstWindows.leg j p f).val n) ∧ Communicates (K.c n) (carried K q x ordinate) z ((FirstWindows.reposition K q f).val n) := ⟨communicate_mirrors j 0 (transport_center K ordinate p h),transport_center K _ q h⟩
end Orbitals
end YM.CF.Buffered.Afterglow.Rooted
