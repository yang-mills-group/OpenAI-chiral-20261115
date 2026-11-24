import SatinFixedContrastNovember4
import YM.SU5.Assay.Kiln
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
/-!
 Reindex and read BothWays along every **pair** of divergent
 schedules. Thus simultaneous includes taking t=max(k,l) forever
 (`k,l` independent engraving heights, `t` pose grid). Not taking
 width→0 first at t bounded. Also guard neighborhoods uniformly in
 both widths & refinements -- even before the first grid limit.
-/
section
open Set
variable {f g h:ℕ→ℕ}
variable {P:Spine}{j:Axis}{x:P.Spectrum0 j}{D:ℕ→P.Apron}{T:P.LagOp j x}
lemma Kiln.visit (p:P.Kiln j x D T)(v:Tendsto f atTop atTop):P.Kiln j x (D ∘ f) T:=by
 refine ⟨p.gridded,⟨fun i=>(p.normal.fades i).comp v,fun _ a _ b=>(p.normal.showAt _ a _ b).visit v⟩,?_⟩
 have hf:Tendsto (fun i:ℕ×ℕ=>(f i.1,i.2)) atTop atTop:=by rw [←prod_atTop_atTop_eq];exact (v.comp tendsto_fst).prodMk tendsto_snd
 exact fun _ _ _ a=>(p.pressed _ _ _ a).visit hf
end

lemma BothWays.pi {Z X:Type*}[Finite Z][TopologicalSpace X]{u:ℕ→ℕ}{a:ℕ→ℕ→ Z → X}{b:ℕ→ Z → X}{c:Z→X}
 (p:∀z,BothWays u (fun i j=>a i j z) (fun i=>b i z) (c z)): BothWays u a b c:=by
 have t:=eventually_all.mpr fun z=>(p z).starts
 exact ⟨t.mono fun _ h=>tendsto_pi_nhds.mpr h,tendsto_pi_nhds.mpr (fun z=>(p z).next),tendsto_pi_nhds.mpr (fun z=>(p z).together)⟩
def Duet {X:Type*}[TopologicalSpace X](a:ℕ→ℕ→ℕ→X)(b:ℕ→ℕ→ X)(v:X) : Prop:=
 ∀ f g:ℕ→ℕ,Tendsto f atTop atTop→Tendsto g atTop atTop→ BothWays (fun s=>max (f s) (g s)) (fun s=>a (f s) (g s)) (fun s=>b (f s) (g s)) v
lemma Duet.pi {Z X:Type*}[Finite Z][TopologicalSpace X]{a:ℕ→ℕ→ℕ→ Z → X}{b:ℕ→ℕ→ Z → X}{c:Z→X}
 (p:∀z, Duet (fun i j k=>a i j k z) (fun i j=>b i j z) (c z)): Duet a b c:= fun f g y r=> BothWays.pi (fun z=>p z f g y r)
namespace Duet
variable {X Y:Type*}[TopologicalSpace X][TopologicalSpace Y]{a a':ℕ→ℕ→ℕ→X}{b b':ℕ→ℕ→X}{v:X}(p:Duet a b v)
include p
lemma same: BothWays id (fun s=>a s s) (fun s=>b s s) v:=
  (p _ _ tendsto_id tendsto_id).raise (Eventually.of_forall fun _=>max_le le_rfl le_rfl)
lemma congr' (q:∀ᶠi:ℕ×ℕ in atTop,b i.1 i.2=b' i.1 i.2∧∀t≥max i.1 i.2,a i.1 i.2 t=a' i.1 i.2 t): Duet a' b' v:=fun f g r u=>by
 rw [←prod_atTop_atTop_eq] at q; exact (p _ _ r u).congr' ((r.prodMk u).eventually q)
lemma pack {c:ℕ→ℕ→ℕ→Y}{d:ℕ→ℕ→Y}{w:Y}(h:Duet c d w):Duet (fun i j t=>(a i j t,c i j t)) (fun i j=>(b i j,d i j)) (v,w):= fun _ _ r u=>(p _ _ r u).pack (h _ _ r u)
lemma map {μ:X→Y}(h:Continuous μ):Duet (fun i j k=>μ (a i j k)) (fun i j=> μ (b i j)) (μ v):=fun _ _ r u=> (p _ _ r u).map h
lemma earnest {s:Set X}(y:s∈𝓝 v):∀ᶠ i:ℕ×ℕ in atTop,
 Tendsto (a i.1 i.2) atTop (𝓝 (b i.1 i.2)) ∧ b i.1 i.2 ∈ s ∧ ∀t≥max i.1 i.2,a i.1 i.2 t ∈s:=by
 contrapose p with e
 -- for each i choose bad pair j,k and (if pose defect) t badly valued
 let H(i:ℕ):= ∃j≥i,∃k≥i,∃t≥max j k, ¬(Tendsto (a j k) atTop (𝓝 (b j k))∧ b j k ∈s∧ a j k t∈s)
 have el:∀i,H i:=by
    intro i; by_contra n; unfold H at n;push Not at n
    apply e; filter_upwards [eventually_ge_atTop ((i,i):ℕ×ℕ)] with q w
    have hn:= n q.1 w.1 q.2 w.2;have h:=hn _ le_rfl
    exact ⟨h.1,h.2.1,fun t r=>(hn t r).2.2⟩
 simp only [H] at el
 choose f m g n t k h using el
 intro p
 have a₁:Tendsto f atTop atTop:= tendsto_atTop_mono m tendsto_id
 have a₂:Tendsto g atTop atTop:= tendsto_atTop_mono n tendsto_id
 have a₃:Tendsto t atTop atTop:= tendsto_atTop_mono (fun i=>le_of_max_le_left (k i)) a₁
 have z:=p f g a₁ a₂
 have u:=Escrow.travels (u:=fun s=>max (f s) (g s)) tendsto_id a₃ (Eventually.of_forall k)
 obtain ⟨i,x⟩:=(z.starts.and ((z.next.eventually y).and ((z.together.comp u).eventually y))).exists
 exact h i x
lemma priced {s:Set X}(y:s∈𝓝 v):∃N:ℕ,∀i≥N,∀j≥N,Tendsto (a i j) atTop (𝓝 (b i j)) ∧ b i j ∈s ∧ ∀t≥max i j,a i j t∈s:=by
 obtain ⟨⟨i,j⟩,g⟩:=eventually_atTop.mp (p.earnest y)
 exact ⟨max i j,fun k s l h=> g (k,l) ⟨le_of_max_le_left s,le_of_max_le_right h⟩⟩
lemma next: Tendsto (fun i:ℕ×ℕ=>b i.1 i.2) atTop (𝓝 v):= fun _ y=> (p.earnest y).mono fun _ z=>z.2.1
end Duet
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
