import YM.Push.GRID_APPROXIMATION.KernelLocal
import YM.Cells.Interior
/-!
# Readouts on coarse box (lattice units)

Price-space of gauge-invariant measurable local tests. This stage ignores
operators/logarithms and works for any Gauge.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Push.GridApprox
open RG Lattice Wilson Filter MeasureTheory Function Finset
open scoped Topology BigOperators Classical
namespace BoxGauge
abbrev Keys (r:ℕ) : Finset (Edge Cover) := ((box r) ×ˢ univ).filter fun i=> i.1+step i.2∈box r
abbrev Tab (r:ℕ) := (Keys r : Type)
-- use coordinates in cover for quote and representation
abbrev Space (G:Gauge)(r:ℕ) := Tab r→G.El
variable {G:Gauge}(r:ℕ) {v t c f:Side}

def base (t:Side)(s:Tab r) : Edge (Site t) := (wrap _ s.val.1,s.val.2)
lemma in_range (s:Tab r) : s.val.1∈box r ∧ s.val.1+step s.val.2∈box r:= let p:=mem_filter.mp s.property; ⟨(mem_product.mp p.1).1,p.2⟩
lemma centered (h:2*r < t.val) : Set.InjOn (wrap t) (↑(box r)) := by
 apply (wrap_injOn t).mono; intro i e j; obtain ⟨p,u⟩:=box_test.mp (show _ from e); have := p j; have := u j; omega
lemma embed_base (h:2*r < t.val) : Injective (base r t) := by
 rintro ⟨⟨s,i⟩,hs⟩ ⟨⟨u,j⟩,hu⟩ v; let p:=Tab r; have hk:i=j:=congrArg Prod.snd v; have ht: s=u := centered r h (in_range r ⟨(s,i),hs⟩).1 (in_range r ⟨(u,j),hu⟩).1 (congrArg Prod.fst v); subst u; subst i; rfl

def tabulate (t:Side)(x:Config G t) : Space G r:= x ∘ base r t
lemma tab_cont (t:Side) : Continuous (tabulate (G:=G) r t):=continuous_pi fun _=> continuous_apply _
def coversSpace (g: Cover→G.El)(U: Space G r) : Space G r:= fun i=>g i.val.1 * U i * (g (i.val.1+step i.val.2))⁻¹
-- projection respects true vertex symmetries (even ones using periodic points not in support sector)
lemma under (g:Site t→G.El)(U:Config G t):tabulate r t (gauge g U)=coversSpace r (g ∘ wrap t) (tabulate r t U):=by
 funext i; change _ * _ * (g (((wrap t) _) + step _))⁻¹ = _ * _ * (g (wrap _ _))⁻¹; rw [map_add,wrap_step]; rfl
open Cells

def paper (G:Gauge) (r:ℕ) : Subalgebra ℂ (Space G r→ℂ) where
 carrier := {F| Envelope F ∧ ∀ g:Cover→ G.El,∀ u,F (coversSpace r g u)= F u}
 add_mem':= fun (h : _ ∧ _) (k : _ ∧ _) => ⟨h.1.addC k.1,fun i j=>congrArg₂ (·+·) (h.2 i j) (k.2 i j)⟩
 mul_mem':= fun (h : _ ∧ _) (k : _ ∧ _) => ⟨h.1.mulC k.1,fun i j=>congrArg₂ (·*·) (h.2 i j) (k.2 i j)⟩
 algebraMap_mem' _c := ⟨Envelope.compactC continuous_const,fun _ _=> rfl⟩
variable (A:paper G r)
lemma paid : Envelope A.val ∧ ∀ g:Cover→ G.El,∀ u,A.val (coversSpace r g u)= A.val u:= A.property

def paint (t:Side)(A:paper G r) : Config G t→ℂ:= A.val ∘ tabulate r t
lemma within : Interior (window (0:Site t) r) (paint r t A):= by
 have he:=paid r A; let F:= he.1.comp_env (tab_cont r t).measurable
 refine ⟨fun g U=> ?_, F.meas, fun x y h=> ?_, F.cost⟩
 · change A.val _= A.val _; rw [under r g U]; exact he.2 _ _
 apply congrArg A.val; funext i; apply h (base r t i); exact ⟨i.val.1,(in_range r i).1, add_zero _⟩; exact ⟨i.val.1+step i.val.2,(in_range r i).2,by simp [base]⟩

lemma inject_pi {α β ν:Type*}[Fintype α][Fintype β][MeasurableSpace ν] (μ:Measure ν)[IsProbabilityMeasure μ](i : α→β)(he:Injective i) : MeasurePreserving (fun x:β→ν=> x ∘ i) (Measure.pi fun _=>μ) (Measure.pi fun _=>μ) := by
 classical
 let s:=Set.range i; let e: α ≃ s:= Equiv.ofInjective i he
 let π:=MeasurableEquiv.piEquivPiSubtypeProd (fun _ : β=>ν) (·∈s)
 let τ:=MeasurableEquiv.piCongrLeft (fun _ : α=>ν) e.symm
 let S:Measure (s→ν):= Measure.pi fun _=>μ; let T:Measure ({i // i∉s}→ν) := Measure.pi fun _=>μ
 have hx: (fun x:β→ν=> x ∘ i)= (τ ∘ Prod.fst) ∘ π:= by
    ext x j; change x (i j)=(τ ((π x).1)) j; nth_rw 2 [←e.symm_apply_apply j]; unfold τ; rw [MeasurableEquiv.piCongrLeft_apply_apply]; rfl
 rw [hx]; refine ((measurePreserving_piCongrLeft (fun _ : α=>μ) e.symm).comp (measurePreserving_fst (μ:=S) (ν:=T))).comp ?_; unfold π S T; convert! measurePreserving_piEquivPiSubtypeProd (fun _ : β=> μ) (·∈s) using 2 ; congr; exact Subsingleton.elim _ _

abbrev credits (G:Gauge)(r:ℕ) := (Measure.pi fun _ : Tab r=>G.probHaar)
lemma projection (t:Side)(h:2*r < t.val) : MeasurePreserving (tabulate r t) (prior G t) (credits G r) := inject_pi G.probHaar _ (embed_base r h)
def weight (A:paper G r) : ℝ:= ∫ x, ‖A.val x‖ ∂credits G r
lemma weight_pos : 0≤ weight r A:=integral_nonneg (fun _i=>norm_nonneg _)
lemma torus_charge (t:Side)(h:2*r < t.val):weight r A=∫ x, ‖paint r t A x‖ ∂prior G t:=by
 let Q(x):= ‖A.val x‖; have hp := projection (G:=G) r t h; have hp0:=integral_map (μ:=prior G t) (f:=Q) hp.aemeasurable; rw [hp.map_eq] at hp0; exact hp0 ((paid r A).1.meas.norm.aestronglyMeasurable)
lemma weight_scale (t:ℂ) : weight r (t • A)= ‖t‖*weight r A:=by unfold weight; simp only [Subalgebra.coe_smul, Pi.smul_apply,norm_smul]; exact integral_const_mul ..
end BoxGauge
end YM.Push.GridApprox
