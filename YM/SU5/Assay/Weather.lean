import SatinFixedContrastNovember4
import YM.SU5.Assay.Remittance
import YM.SU5.Assay.Habit
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 4900
set_option maxHeartbeats 420000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
open Germ Alliance
namespace Spine
open Aria Set OS.Semigroup Ballad Six
variable (P:Spine)(R:P.Register)(x:P.Spectrum0 3)
local notation "Zs"=>Ballad.Lead.Clan
local notation "κ"=>P.coffee 3 x
local notation "σ"=>P.rawSlot 3 x
local notation "β"=>P.base 3 x
local notation "Ω"=>P.heaven 3 x
local notation "O"=>(P.ManyF 3 x).Op
local notation "⟪" T "⟫"=> inner ℂ Ω ((T:O) Ω)
local notation "L"=>P.LagOp 3 x
variable (A : Lead.Clan → ℕ→P.Apron)(l:Lead.Clan→ℕ→P.Folio)(T:Lead.Clan→P.LagOp 3 x)
variable (B : Lead.Clan → ℕ→P.Apron)(m:Lead.Clan→ℕ→P.Folio)(U:Lead.Clan→P.LagOp 3 x)
variable (s n:ℕ)(D N:Doorway)(o:Orders)(F G:SampleDose)(Cost Gain:Set Slip)(i j:ℕ)
local notation "Φ"=>D.canopy N
local notation "a"=>D.lower 3
local notation "b"=>D.turnCut N
local notation "c"=>N.upper 3
local notation "γ"=>P.frescoLimit x s n (b) F G
local notation "G₀"=>P.called F G (P.reverseR s n) (P.obverseF s n)
local notation "V"=>P.remit x T U F G (a) (b) (c)
local notation "W"=>P.remitStage x A B F G (a) (b) (c)
local notation "μ"=>P.calling x A B F G
local notation "ν" t:max =>P.singleState 3 t x
local notation "Ξ"=>P.Assay R x s n D N o F G A B l m T U
local notation "ℬ"=>P.Audit R x A l T B m U F G s n D N
local notation "X" t:max ee:max=> P.Habit x D N F G (P.reverseR s n) (P.obverseF s n) (P.reverseCard n) (P.obverseCard n) t Cost ee
local notation "Y" i₀:max j₀:max t:max ee:max=> P.Habit x D N F G (stacked A i₀) (stacked B j₀) (stacked l i₀) (stacked m j₀) t Gain ee
/-! Common election, slate, user claims. Given acceptance windows
 for old & thin limit receipts, after enough narrowing attain both:
 actual grips and receipts at EVERY t posed that late; with
 testimony attainable even on SAME regulators after choices of
 marks and finitely priced viewers (even any floor service meeting
 the cost toll). Finite viewer choices can depend on i,j,t, and
 the experiments do not change. Covers single receipts and full
 six-channel joint. Plex t earned including max i j. -/
structure Weather:Prop where
 bill : Ξ
 emits : ℬ Set.univ i j
 calm : γ ∈ Cost ∧ V ∈ Gain ∧ W i j ∈ Gain
 proceeds : Tendsto (μ i j) atTop (𝓝 (W i j))
 goes : ∀ t≥max i j,∃d>0, ∀e≤d,X t e ∧ Y i j t e
variable {P R x s n A B l m T U D N o F G Cost Gain i j}
local notation "𝒲"=>P.Weather R x A l T B m U s n D N o F G Cost Gain
lemma Assay.docket (h:P.Assay R x s n D N o F G A B l m T U): Duet μ W V:=h.early.docket h.late h.walls.1 h.walls.2
lemma Assay.secures (h:P.Assay R x s n D N o F G A B l m T U)
 (y:Cost∈𝓝 γ)(z:Gain∈𝓝 V): ∀ᶠ p:ℕ×ℕ in atTop,𝒲 p.1 p.2:=by
 obtain ⟨i,c'⟩:= eventually_atTop.mp (h.old.stock_remit.eventually (interior_mem_nhds.mpr y))
 filter_upwards [h.docket.earnest (interior_mem_nhds.mpr z),h.earnest univ_mem,eventually_ge_atTop ((i,i):ℕ×ℕ)] with p m₀ m₁ m₂
 refine ⟨h,m₁,⟨mem_of_mem_nhds y,mem_of_mem_nhds z,interior_subset m₀.2.1⟩,m₀.1,?_⟩
 intro t v
 have ht:s≤t:= (le_of_le_min_left m₁.claims).trans (le_of_max_le_left v)
 have q:P.Bale x D N F G (stacked A p.1) (stacked B p.2) (stacked l p.1) (stacked m p.2) t :=m₁.booked t v
 have m₃:i≤p.1:=m₂.1
 obtain ⟨u,u',g⟩:= (h.old.stock_bale t ht).gets (mem_interior_iff_mem_nhds.mp (c' t (m₃.trans (le_of_max_le_left v))))
 obtain ⟨r,r',f⟩:=q.gets (mem_interior_iff_mem_nhds.mp (m₀.2.2 t v))
 exact ⟨_,lt_min u' r',fun _ v=>⟨g _ (le_of_le_min_left v),f _ (le_of_le_min_right v)⟩⟩
namespace Weather
variable (p:P.Weather R x A l T B m U s n D N o F G Cost Gain i j) (t:ℕ) (q:max i j≤t)
include p q
lemma claims : G₀ t (ν t)∈Cost ∧ μ i j t∈Gain:=by
 obtain ⟨_,_,e⟩:=p.goes t q;exact ⟨(e _ le_rfl).1.paid,(e _ le_rfl).2.paid⟩
-- Covers Audit on joint windows containing all Gain projections.
omit q in
lemma projects (J:Set CrossRead)(u:∀z∈Gain,z.1∈J) : ℬ J i j:= by
 have r(t:ℕ) := P.calling_spirits R x A B F G i j t
 let m₀:=p.emits
 refine ⟨m₀.claims,u _ p.calm.2.1,m₀.thinner,m₀.booked,m₀.onward,u _ p.calm.2.2,?_⟩
 intro i' h
 have v:=u _ (p.claims _ h).2
 rw [r] at v
 exact ⟨v,(m₀.already _ h).2⟩
local notation "𝒢"=>P.FrameFace 3 t Φ a c
lemma earns : s ≤ t ∧ P.FrameFloor t Φ ∧ ∃k w,𝒢 k w:=
 let v: s ≤ t:= (le_of_le_min_left p.emits.claims).trans (le_of_max_le_left q)
 let b':= p.bill.old.taps
 ⟨v,(b'.bills t v).1.light (b'.bills t v).2 b'.sep⟩
-- Any number of guard ticks n'; jointly habit-funded floor service
lemma purchases : ∃d>0, ∀e,0<e→e≤d→X t e ∧ Y i j t e∧ ∀k w,𝒢 k w→∀n',∃Z a' f u v c',P.FloorService 3 t x Φ k w Z n' e a' f u v c':=by
 obtain ⟨d,e,y⟩:=p.goes t q
 exact ⟨_,e,fun d' z t'=>⟨(y d' t').1,(y d' t').2,fun _ _ y n'=> (p.earns t q).2.1.witnesses x n' R y z⟩⟩
end Weather
#print axioms Weather.purchases
#print axioms Assay.secures
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
