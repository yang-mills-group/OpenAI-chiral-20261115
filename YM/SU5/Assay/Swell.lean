import SatinFixedContrastNovember4
import YM.SU5.Assay.Weather
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
variable {P R x s n A B l m T U D N o F G Cost Gain i j}
local notation "𝒲"=>P.Weather R x A l T B m U s n D N o F G Cost Gain
/-!
 Even one service at each t for all pledges at once. At any demanded
 precision schedule; buys Duet of *actual* pricings on even these
 (co-stationed) regulators. `grid distance` set via Slip metric, not a
 choice of relative error units carried into the exposures.
-/
variable {e:ℕ→ℝ}
private lemma seen_dist {I J:Type*}[PseudoMetricSpace I]{f g:J→I}{L':Filter J} {d:J→ℝ} {z:I}
 (p:Tendsto f L' (𝓝 z))(h:Tendsto d L' (𝓝 0))(u:∀ᶠ i in L',dist (g i) (f i) < d i): Tendsto g L' (𝓝 z):=
 p.congr_dist <| squeeze_zero' (Eventually.of_forall fun _=>dist_nonneg) (u.mono fun i y=>(dist_comm (f i) (g i)).trans_le y.le) h
lemma Duet.clings {I:Type*} [PseudoMetricSpace I]{f g:ℕ→ℕ→ℕ→ I}{m₀:ℕ→ℕ→I}{i₀:I}(q:Duet f m₀ i₀)(h:Tendsto e atTop (𝓝 0))
 (u:∀ᶠi:ℕ×ℕ in atTop,∀t≥max i.1 i.2,dist (g i.1 i.2 t) (f i.1 i.2 t)<e t):Duet g m₀ i₀:=by
 intro k r y z
 rw [←prod_atTop_atTop_eq] at u
 let l':=(y.prodMk z).eventually u
 let w:=q k r y z;let j' i:=max (k i) (r i)
 refine ⟨?_,w.next,?_⟩
 · filter_upwards [l',w.starts] with i u' a'
   exact seen_dist a' h ((eventually_ge_atTop _).mono (u' · ·))
 refine seen_dist w.together (h.comp (Escrow.snd j')) ?_
 exact (((Escrow.fst j').eventually l').and (Escrow.pays j')).mono fun i r=>r.1 i.2 r.2

namespace Assay
variable (p:P.Assay R x s n D N o F G A B l m T U)
local notation "Q" i₀:max j₀:max => P.called F G (stacked A i₀) (stacked B j₀)
local notation "M" t:max=>P.Patina 3 t x Φ
local notation "H" i₀:max j₀:max t:max => P.Bale x D N F G (stacked A i₀) (stacked B j₀) (stacked l i₀) (stacked m j₀) t
include p
omit p in
private lemma fini {α:Type*} (I:Finset α) {Ask:α→ℝ→Prop}(h:∀i∈I,∃r>0,∀u≤r,Ask i u):∃r:ℝ,r>0∧∀u≤r,∀i∈I,Ask i u:=by
 induction I using Finset.induction with
 | empty=>exact ⟨_,one_pos,fun _ _ i w=> (Finset.notMem_empty _ w).elim⟩
 | @insert i I q t=>
    obtain ⟨r,p,y⟩:=h _ (mem_insert_self i I)
    obtain ⟨v,l,x⟩:=t (fun j u=>h j (mem_insert_of_mem u))
    refine ⟨_,lt_min p l,?_⟩
    intro f g j v
    rcases mem_insert.mp v with rfl|u
    · exact y f (le_of_le_min_left g)
    exact x f (le_of_le_min_right g) j u
lemma tolls (t:ℕ)(v:s ≤ t) (r:ℝ)(h:0<r):∃d>0,∀u≤d,
   ∀X':P.Test→ℂ, (M t) u X' → dist (G₀ t X') (G₀ t (ν t))<r∧
   ∀i j, max i j ≤ t → (H i j t) → dist ((Q i j) t X') ((Q i j) t (ν t))<r:=by
 let I:Finset (ℕ×ℕ):=(Finset.Iic (t,t)).filter fun w=>H w.1 w.2 t
 let Ask (i:ℕ×ℕ) d:=∀X':P.Test→ℂ,(M t) d X'→ (Q i.1 i.2) t X' ∈ Metric.ball ((Q i.1 i.2) t (ν t)) r
 have hr:∀i∈I,∃d>0,∀u≤d,Ask i u:=by
   intro i vi; have g:(H i.1 i.2 t):= (Finset.mem_filter.mp vi).2
   obtain ⟨_,a₁,z⟩:=g.gets (Metric.ball_mem_nhds _ h)
   exact ⟨_,a₁,fun _ t=> (z _ t).embark⟩
 obtain ⟨_,y,z⟩:=(p.old.stock_bale t v).gets (Metric.ball_mem_nhds _ h)
 obtain ⟨_,q,u⟩:=fini I hr
 exact ⟨_,lt_min y q,fun _ w V' j=>⟨(z _ (le_of_le_min_left w)).embark _ j,fun i j' h g=>u _ (le_of_le_min_right w) (i,j') (mem_filter.mpr ⟨mem_Iic.mpr (max_le_iff.mp h),g⟩) V' j⟩⟩
-- For each toll a service at the specified rating exists by other theorems.
lemma covers (t:ℕ)(v:s ≤ t) : P.FrameFloor t Φ∧ ∃i w,P.FrameFace 3 t Φ a c i w :=
 (p.old.taps.bills _ v).1.light (p.old.taps.bills _ v).2 p.old.taps.sep
lemma swell : ∃d:ℕ→ℝ,(∀t,0<d t) ∧ ∀X':ℕ→P.Test→ℂ,(∀t≥s,(M t) (d t) (X' t)) →
 Tendsto (fun t=>G₀ t (X' t)) atTop (𝓝 γ)∧ Duet (fun i j t=> (Q i j) t (X' t)) W V:=by
 let e (t:ℕ):ℝ:=1/(t+1:ℝ)
 have he:Tendsto e atTop (𝓝 0):=tendsto_one_div_add_atTop_nhds_zero_nat
 choose r pr h using fun t v=>p.tolls t v _ (show 0<e t by unfold e; positivity)
 let d t:=if y:s≤t then r t y else 1
 have hd(t:ℕ):0<d t:=by unfold d; split<;> simp [*]
 refine ⟨d,hd,?_⟩
 intro V' x₀
 have r' t v:=h t v (d t) (by simp [d,v]) _ (x₀ t v)
 refine ⟨seen_dist p.old.stock_remit he ((eventually_ge_atTop s).mono fun i u=>(r' i u).1), p.docket.clings he ?_⟩
 filter_upwards [p.earnest univ_mem] with i y t v
 exact (r' t ((le_of_le_min_left y.claims).trans (le_of_max_le_left v))).2 i.1 i.2 v (y.booked t v)
end Assay
#print axioms Assay.swell
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
