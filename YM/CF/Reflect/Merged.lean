import YM.CF.Reflect.Paste

/-! Exact splice in the compact product measure. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.RP
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Topology
open Function Fock Filter NormedSpace SU Lat Lattice Branch Cube Tenant Phase Mir Mir.Trip MeasureTheory Sample Finset
attribute [local instance] opCStarAlgebra
section batch
variable {I X Y : Type*} [Fintype I] [DecidableEq I] [MeasurableSpace X] [MeasurableSpace Y]
variable (μ : Measure X) (ν : Measure Y) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
lemma patch_mp (s : Finset I) : MeasurePreserving (fun v : (I→X)×(I→X)=>patchF s v.1 v.2) ((fares I μ).prod (fares I μ)) (fares I μ) := by
  let e := MeasurableEquiv.piEquivPiSubtypeProd (fun _:I=>X) (·∈s)
  let p := measurePreserving_piEquivPiSubtypeProd (fun _:I=>μ) (·∈s)
  let m := fun (l:Fintype {i:I//i∈s})=> @Measure.pi {i:I//i∈s} (fun _=>X) l _ (fun _=>μ)
  let n := fun (l:Fintype {i:I//¬i∈s})=> @Measure.pi {i:I//¬i∈s} (fun _=>X) l _ (fun _=>μ)
  let M := m (Subtype.fintype fun i:I=> i∈s); let N := n (Subtype.fintype fun i:I=>¬i∈s)
  have hM : IsProbabilityMeasure M := by unfold M m; infer_instance
  have hN : IsProbabilityMeasure N := by unfold N n; infer_instance
  have hp : MeasurePreserving (⇑e) (fares I μ) (M.prod N) := p
  let p := hp.prod hp
  have H := (hp.symm _).comp (((measurePreserving_fst (μ:=M) (ν:=N)).prod (measurePreserving_snd (μ:=M) (ν:=N))).comp p)
  convert! H using 1
lemma prod_mix : MeasurePreserving (fun v:(X×Y)× X×Y=> ((v.1.1,v.2.1),(v.1.2,v.2.2))) ((μ.prod ν).prod (μ.prod ν)) ((μ.prod μ).prod (ν.prod ν)) := by
  let f := MeasurableEquiv.prodAssoc (α:=X) (β:=Y) (γ:=X×Y) -- tune names
  have A := measurePreserving_prodAssoc μ ν (μ.prod ν)
  have B := measurePreserving_prodAssoc ν μ ν
  have H := (Measure.measurePreserving_swap (μ:=ν) (ν:=μ)).prod (MeasurePreserving.id ν)
  have Z := (measurePreserving_prodAssoc μ ν ν).comp (H.comp (B.symm MeasurableEquiv.prodAssoc))
  have W := ((MeasurePreserving.id μ).prod Z).comp A
  exact ((measurePreserving_prodAssoc μ μ (ν.prod ν)).symm MeasurableEquiv.prodAssoc).comp W
end batch
abbrev ux := SU.group.probHaar
def barrow (m B : Side) : Measure (Skin m B) := fares _ ux
instance (m B): IsProbabilityMeasure (barrow m B) := by unfold barrow; infer_instance
lemma edge_mp (m B : Side) (i : Axis) : MeasurePreserving (rayUK m B i) (barrow m B) (barrow m B) := by
  let g (a : RZ m B) (x:E) := if a.2=i then x⁻¹ else x
  have he (a:RZ m B) : MeasurePreserving (g a) ux ux := by unfold g; split; exact Measure.measurePreserving_inv _; exact MeasurePreserving.id ux
  let R := rx m B i
  have hp := measurePreserving_piCongrLeft (α:=fun _:RZ m B=>E) (fun _=>ux) R
  have hQ := (measurePreserving_pi _ _ he).comp hp
  have hx : (Pi.map g ∘ ⇑(MeasurableEquiv.piCongrLeft (fun _:RZ m B=>E) R))=rayUK m B i := by
    funext x y; obtain ⟨j,rfl⟩ := R.surjective y
    rw [reflect_E]; unfold Function.comp Pi.map; rw [MeasurableEquiv.piCongrLeft_apply_apply,show rayE m B i (R j)=j from ray_back j i]
  exact hx ▸ (show MeasurePreserving (Pi.map g ∘ ⇑(MeasurableEquiv.piCongrLeft (fun _:RZ m B=>E) R)) _ _ from hQ)

def wheel (m B : Side) : Measure (Pack m B) := (barrow m B).prod (rains m)
instance (m B) : IsProbabilityMeasure (wheel m B) := by unfold wheel; infer_instance
lemma orbit_w (m B : Side) (i : Axis) : MeasurePreserving (Pbar m B i) (wheel m B) (wheel m B) := (edge_mp m B i).prod ((slideM m i).rains_p)
lemma binary_w (m B : Side) (S T) : MeasurePreserving (fun p:Pack m B×Pack m B=>stitch m B S T p.1 p.2) ((wheel m B).prod (wheel m B)) (wheel m B) := ((patch_mp ux S).prod (patch_mp cloud T)).comp (prod_mix (barrow m B) (rains m))
def quill (m B : Side) (i : Axis) (x:Pack m B×Pack m B×Pack m B) := tiedK m B i x.1 x.2.1 x.2.2
lemma spun (m B : Side) (i) : let w := wheel m B; MeasurePreserving (quill m B i) (w.prod (w.prod w)) w := by
  intro w
  exact (binary_w m B _ _).comp ((MeasurePreserving.id w).prod ((binary_w m B _ _).comp ((MeasurePreserving.id w).prod (orbit_w m B i)))) -- tune
lemma heard {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] (m B : Side) (i) (f:Pack m B → X) (h : Integrable f (wheel m B)) :
    (∫ x,f x ∂wheel m B) = ∫ w, (∫ v, f (quill m B i (w,v)) ∂(wheel m B).prod (wheel m B)) ∂wheel m B := by
  let μ := wheel m B; let ν:= μ.prod (μ.prod μ); let F := quill m B i; have he := spun m B i; change MeasurePreserving F ν μ at he
  have hh (F : Pack m B × Pack m B × Pack m B → Pack m B) (g : MeasurePreserving F ν μ) : ∫ x,f x ∂μ=∫ x,f (F x) ∂ν := by
    rw [←g.map_eq]; exact integral_map g.measurable.aemeasurable (g.map_eq.symm ▸ h.aestronglyMeasurable)
  change ∫ x,f x ∂μ=_; rw [hh F he]; exact integral_prod _ ((he.integrable_comp h.aestronglyMeasurable).mpr h) -- tune
end YM.CF.RP
