import YM.SU5.FiniteGaugeData.Indigo.Ariadne
import YM.SU5.FiniteGaugeData.Indigo.Camora
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
namespace Succulent
open Strata
variable (R:Patch)
open CF.Indigo
namespace SpineV
open YM.SU5.FiniteGaugeData.Lapis Lumi
open LapisS LapisS.Stadium
open Chiffon.Prato
variable {ι:Type}[Fintype ι] (A:ι→RG.Slot)(x:Cover)
local notation "χ"=> SU.group.Color
abbrev Shuf (U:LinksC)(i:ι):= (A i).eval (G:=SU.group) (Lattice.translate x U)
noncomputable abbrev rimS (A:ι→RG.Slot)(x:Cover): Finset Cover:= univ.biUnion fun i=> (A i).stencil.image (fun z:Cover=> z+x)
lemma shuffle_cont : Continuous (Shuf A x) := continuous_pi fun i=> (RG.Slot.cont _).comp (show Continuous (fun U:LinksC=>Lattice.translate x U) from (by unfold Lattice.translate; fun_prop))
lemma shuffle_local : Lattice.LocalOn (rimS A x) (Shuf A x):=by
 intro U V h; funext i; refine (A i).covered _ _ ?_; intro e y z; have hy: e.1+x∈ rimS A x:= mem_biUnion.mpr ⟨i,mem_univ i, mem_image_of_mem _ y⟩; have hv:(e.1+x)+step e.2∈rimS A x:=by rw [add_right_comm]; exact mem_biUnion.mpr ⟨i,mem_univ _,mem_image_of_mem _ z⟩ -- scoped h
 exact h (e.1+x,e.2) hy hv
lemma shuffle_equiv (u:Cover→ SU.E)(U:LinksC): Shuf A x (Lattice.gauge u U)= fun i=> SU.group.adjoint (u x) (Shuf A x U i):=by
 let v(i:Cover):= u (i+x); have hx:Lattice.translate x (Lattice.gauge u U)=Lattice.gauge v (Lattice.translate x U):=by funext e; unfold Lattice.translate Lattice.gauge v; simp only; rw [add_right_comm]
 have h(i:RG.Slot)(F:LinksC): entryW (Lattice.gauge v F) i= v 0*entryW F i*(v 0)⁻¹:=by unfold entryW; rw [face_gauge,travel_gauge]; simp only [RG.Slot.offset]; group
 funext i; unfold Shuf; rw [hx,← melodyP,←melodyP, h,SU.group.curvature_conjugate,show v 0= u x from (by unfold v; rw [zero_add]) ] -- rw v definition
structure Lariat (ι:Type)[Fintype ι](F:(ι→ SU.group.Color)→ℝ):Prop where
 p0:Continuous F
 phase(u:SU.E)(x:ι→ SU.group.Color):F (fun i=> SU.group.adjoint u (x i))=F x
variable (F:(ι→SU.group.Color)→ℝ) (u':Lariat ι F)
noncomputable abbrev cladF (r:ℝ)(U:LinksC):ℂ:= ↑(F (r • Shuf A x U)) -- x notation issue Terra
lemma auth_f (r:ℝ)(u:Lariat ι F) : Anorak (rimS A x) (cladF A x F r):=by
 refine ⟨fun t y=>?_, Complex.continuous_ofReal.comp (u.p0.comp ((continuous_const (y:=r)).smul (shuffle_cont A x))), fun i j p=>?_⟩
 · unfold cladF; rw [shuffle_equiv, show r • (fun i=> SU.group.adjoint (t x) (Shuf A x y i))= (fun i=> SU.group.adjoint (t x) ((r • Shuf A x y) i)) from funext (fun i=> ((SU.group.adjoint (t x)).map_smul r (Shuf A x y i)).symm), u.phase]
 unfold cladF; rw [shuffle_local A x _ _ p]
noncomputable abbrev suede (K:Calibration)(r:ℝ) : W K:= shunt K false (cladF A x F r) (auth_f A x F r u')
lemma sheer [DecidableEq ι] (p:Lumi.Duct SU.group ι)(P:Clip)(K:Calibration)(r:ℝ)(v:A=p.beam) (q:Lariat ι p.seen): suede A x p.seen q K (r*Real.sqrt P.direct)= Stadium.pole p P r K x 1:=by
 apply Subtype.ext; funext m b; let U:= onC (K.c m) b.1; subst A; change ( (↑(p.seen ((r*Real.sqrt P.direct) • Shuf p.beam x U)):ℂ) • 1) = ( (↑(p.seen ((r*Real.sqrt P.direct) • Stadium.chart7 p x 1 U)):ℂ) • (1:FC _)); congr 4; -- expose congr only; test
 funext i; let V:= Lattice.translate x U; have h:= (Lumi.marker 1 (G:=SU.group) (p.beam i)).2 V; rw [pull_id] at h; exact h
-- pure raw rendering narrow & unaffected sensor
lemma unitL [DecidableEq ι] (A:Lumi.Duct SU.group ι): Lariat ι A.seen:= ⟨A.registered.continuous,A.orbs⟩
lemma raw_skin(K:Calibration)(r:ℝ)(t:Lariat ι F): RawG K (suede A x F t K r):=fun i=> ⟨fun v=> cladF A x F r (onC _ v),fun _=>rfl⟩
lemma sup_skin (K:Calibration)(r:ℝ)(t:Lariat ι F): Locator K (suede A x F t K r) (rimS A x):=loc_shunt ..
lemma suede_read(t:Lariat ι F)(K:Calibration)(r:ℝ)(N:Side)(i:Fields (K.c N)): (suede A x F t K r).val N i = cladF A x F r (onC (K.c N) i.1) • 1:= rfl
#print axioms auth_f
end SpineV
end Succulent
end FlakeNight
end Sesame
end Chiffon
end YM.CF.Buffered.Afterglow.Hierarchy.LyraBill
