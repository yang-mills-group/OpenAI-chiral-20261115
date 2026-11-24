import SatinFixedContrastNovember4
import SatinThinJetsOrder

/-! # CP14-I Pure gauge stencils after promotion

A mark that only takes values in the identity line is pure gauge, including the
existence of cover coefficients on the witnessing stencil; this survives every
resolution change. We'll need this to dress matter at a NEW registration
without abandoning the raw marginal test there.

Use the same infrastructure as `Six/CoverLetters,Bipocket,KeepCharge`
(essentially copying those arguments for the identity line).
-/

set_option autoImplicit false
set_option quotPrecheck false
set_option synthInstance.maxSize 24000
set_option maxHeartbeats 500000
noncomputable section
namespace YM.CF.Buffered.Afterglow.Six
open Function Filter NormedSpace SU Lat Lattice Cube Finset MeasureTheory RG Wilson Metric
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Kronecker Topology ComplexOrder ENNReal Classical
open Rush Scroll Peaks Stencil Tenant Tap Tulip Branch Fir Scree Advance Reflect Window Laurent Next.Free Bloch Drapes Spire Lifted Skye Sound Precision Tree Push.SectorMeasure Next.SectorChange Common Fock
open Satin
attribute [local instance] opCStarAlgebra
open Mir Haro Tap Dial Cascade Girt Pastry
open Afterglow.Tapestry Tower

abbrev fockOne (N:Side): Submodule ℂ (FC (Single N)):=Submodule.span ℂ {(1:FC _)}
def pinCoefficient (N:Side): (FC (Single N)) →ₗ[ℂ] ℂ where
 toFun M:= M ∅ ∅
 map_add' _ _ := rfl
 map_smul' _ _ := rfl
lemma pin_one (N:Side) : pinCoefficient N 1=1:= Matrix.one_apply_eq _
lemma pin_reads {N:Side}{x : FC (Single N)} (h:x∈fockOne N): x=pinCoefficient N x • 1:=by
 obtain ⟨c,rfl⟩:=Submodule.mem_span_singleton.mp h
 rw [map_smul,pin_one,smul_eq_mul,mul_one]
def Paleness (K:Calibration)(F:Buffered.Family K): Prop := ∀ m x,F m x∈fockOne (K.c m)
variable (K:Calibration)(m:Side)(D:Finset Cover)
lemma pale_scalar (F:PairsC→ℂ):Paleness K (scalar K F):=fun m x=>Submodule.mem_span_singleton.mpr ⟨_,rfl⟩
lemma pure_pale {F:Dome K}(h:PureGauge K F): Paleness K F.val:=by
 obtain ⟨S,f,p,e⟩:=h; rw [e]; exact pale_scalar K f
lemma pale_descends {F:Buffered.Family K}(p:Tivoli D (K.c m))(v:InTest K true D false F)
    (w:∀ x,F m x∈fockOne (K.c m)):
    ∃ f:PairsC→ℂ, Coeff true D f ∧ F=scalar K f:=by
 let V:=F m; let q:= pinCoefficient (K.c m); let f(x:PairsC):ℂ:= q (V (replant D _ x)); let E:= v.support m
 have he: Coeff true D f:= by
    refine ⟨fun _=> by contradiction,Girt.pole_w (V ∘ replant D _) q (q.continuous_of_finiteDimensional) (Env.along E.env (replant_b ..)),?_⟩
    intro x y a b; exact congrArg q (E.dep _ _ (based D _ p _ _ a) (based D _ p _ _ b))
 refine ⟨f,he,Tower.box_ext K D v (.seed he) p.hosp ?_⟩
 funext x
 have ht:V (replant D _ (onC _ x.1,onC _ x.2))= V x:= E.dep _ _ (graft_native D _ p _) (graft_native D _ p _)
 change V x=q (_ ) • _; rw [ht]; exact pin_reads (w x)
lemma mirror_pale (F:Buffered.Family K)(h:Paleness K F)(j:Axis)(z:ℤ): Paleness K (Tower.mirror K j z F):= by
 intro n x; unfold Tower.mirror reflMark; rw [pin_reads (h n _),Fock.theta_smul,Fock.theta_one]; exact Submodule.mem_span_singleton.mpr ⟨_,rfl⟩
lemma relocate_pale (F:Buffered.Family K)(h:Paleness K F)(j:Axis)(z:ℤ): Paleness K (SlabMark.relocate K j z F):=
 mirror_pale K _ (mirror_pale K F h j 0) _ _
section push
variable {N P:Side}(G:Ratio N P)(j:ℕ)(Q:Haro.SpaceM)(M:Male)(ho: Odd G.count.val)
    {R:ℕ}(p:LaurentRadius j G.count R)(A:StepData (More N) (More P))(q:Chi)(d β:ℝ)(l:Loom N)
include p ho
lemma push_pale (t:Measurable l)(u:A.patch.Branches A.kernel SU.group)(a:0<d)(b:2*d<firstRadius SU.group)
    (f:Mark N)(he:Envelope f)(h:∀ x,f x∈fockOne N)(v:Fields P):
    pushMark G A j Q.val M ho q d β l f v∈fockOne P:=by
 rw [outright G A j Q.val M ho q d β l p t u a b _ he]
 let X:= (fockOne P).restrictScalars ℝ
 apply X.convex.integral_mem X.closed_of_finiteDimensional _ (pushIntegrable G A j Q.val M ho q d β l f p t u a b he v v.1)
 apply Eventually.of_forall; intro i
 apply X.smul_mem
 unfold gathered avgF
 apply X.smul_mem
 apply X.sum_mem; intro j' _; unfold Advance.before; rw [pin_reads (h _), map_smul,sub_one]; exact Submodule.mem_span_singleton.mpr ⟨_,rfl⟩ -- perhaps before is admissible
end push
open Py Py.Rate LocalLimit Preparation Journey Vale
variable {Λ: Preparation} {l : ℕ} (Y:Course Λ (VolumeCape.Dream.Nimbus l))
variable (s i k:ℕ)
local notation "N" => side Y i s
local notation "P" => side Y i (s+1)
local notation "G"=> (Vale.apt (Y.ir i) Λ.block Λ.R.L s)
local notation "Z"=> ((Y.voyage i).X (Y.uv k))
lemma ascend_paleness(f:Mark N)(he:Envelope f)(v:∀ x,f x∈ fockOne N)(p:Satin.PairIdx Y s i k)(x:Fields P):
    Tapestry.ascender Y s i k f x∈fockOne P:=by
 have a:=(fullness Y i k p.1).cap_grant; obtain ⟨L⟩:=a.grant s p.2
 exact push_pale G Λ.K.j (patternQ Y s i k) ((Z).gram (s+1)).J.M
    Λ.R.odd_side (Journey.legal Λ) (steps Λ.V (Y.ir i) Λ.block (Y.uv k) s) Chi.canonical Λ.J.d
    ((Z).gram (s+1)).beta ((Y.voyage i).CapeT s) ((Y.voyage i).ownership s).paid.bill (a.branch s p.2)
    L.legal.1 L.legal.2 f he v x
end YM.CF.Buffered.Afterglow.Six
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common Ballad Cordial
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Heat Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
open Germ Alliance Lamour.Bridge.Celeste Designs Twah Prototype
open Lamour.Bridge.Celeste.Morn
open Tapestry.Exhibition
namespace Spine
open Six
variable (P:Spine)(D:Finset Cover)(s:ℕ)
local notation "Y"=>P.run
local notation "H"=>P.large
local notation "K"=>P.calibration
local notation "G"=>P.projection
local notation "A₊" X:max=>wingspan P.par P.width X
private lemma pale_ship {N N':Side}(h:N=N')(f:Mark N): (∀ x,f x∈fockOne N) ↔ ∀ x,ship h f x∈fockOne N':=by subst N; rfl
private lemma block_paleness {i k:ℕ}{F: Buffered.Family P.calibration}(w:InTest K true D false F)(u:Paleness K F)
    (h:legalAt Y s i k)(p:Tivoli (A₊ D) ((K).c (momentm Y i (s+1)))): Paleness K (block Y H s i k D F):=by
 let f:= distribute Y H s i F
 let B:= block Y H s i k D F
 have e:∀ x,B (momentm Y i (s+1)) x∈fockOne _:=by
    refine (pale_ship (terrain Y H _ (s+1)) _).2 ?_
    change ∀ x,distribute Y H _ i (block Y H s i k D F) x ∈ _; rw [reserved Y H s D i k h w p]
    exact ascend_paleness Y s i k f ((stationed Y H s D i w).env) ((pale_ship (terrain Y H _ s) _).1 (u _)) h
 obtain ⟨g,y,q⟩:=pale_descends K _ _ p (show InTest K true (A₊ D) false B from booked ..) e
 change Paleness K B; rw [q]; exact pale_scalar _ _
lemma advance_paleness {F: Buffered.Family P.calibration}(w:InTest K true D false F)(u:Paleness K F) : Paleness K ((G).refine s F):=by
 let r(i):=P.period ((G).rows i); let m(i):=P.cutoff ((G).columns i)
 have ht : Tendsto r atTop atTop := P.law.pick.grow_i.tendsto_atTop.comp P.history.growsA.tendsto_atTop
 intro J x
 apply (fockOne ((K).c J)).closed_of_finiteDimensional.mem_of_tendsto (P.block_hist s D _ w J x)
 filter_upwards [ht.eventually (turning Y H (s+1) (A₊ D)), P.history.finance (s+1)] with i v e
 exact P.block_paleness D s w u (i:=r i) (k:=m i) (show legalAt Y s (r i) (m i) from ⟨e.depth,e.enters⟩) v J x
lemma pale_iff (F:P.Test): Paleness K F.val ↔ PureGauge K F:=by
 obtain ⟨X,h⟩:= findsBay K F
 obtain ⟨m,hp⟩:= (turning Y H 0 X).exists
 exact ⟨fun u=>⟨X,pale_descends K _ _ hp ((Tapestry.locates ..).1 h) (u _) ⟩, pure_pale K⟩
lemma shifts_pure (F:P.Test)(j:Axis)(z:ℤ)(p:PureGauge K F): PureGauge K (P.shifts j z F):=
 (P.pale_iff _).mp (relocate_pale K _ (pure_pale K p) _ _)
lemma convey_pure (F:P.Test)(p:PureGauge K F)(n:ℕ): PureGauge K (P.conveying s n F):=by
 induction n with
 | zero=> exact p
 | succ n h=>
   let Q:= P.conveying s n F; obtain ⟨X,hp⟩:=findsBay K Q; exact (P.pale_iff _).mp (P.advance_paleness X (s+n) ((Tapestry.locates ..).1 hp) ((P.pale_iff Q).mpr h))
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
#print axioms YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine.convey_pure
