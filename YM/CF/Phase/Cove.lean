import YM.CF.Phase.PairLaw
import YM.CF.Sample.Mist

/-! Unified expectation of path weights (end then path). -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.Phase
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Topology
open Function Fock Filter NormedSpace SU Lat Lattice Branch Cube Tenant MeasureTheory Sample
open Finset
attribute [local instance] opCStarAlgebra
variable {m B : Side}

def loft (m B : Side) (U : Skin m B) (x y : Cue m) : Plan (Index m) cloud where
  orderF := degree m
  indexF := faces m
  run a := bidW m B U x y a
  polite a := by
    let T := fun t : ((Skin m B × Cue m) × Cue m)× Cue m => bidW m B t.1.1.1 t.1.1.2 t.1.2 a t.2
    change Continuous (T ∘ fun z=>(((U,x),y),z)); exact (show Continuous T from bid_js m B a).comp (continuous_const.prodMk continuous_id)
  normalize a v := price_integral _ _ _ _ _ _ _ a v (by simp)
  readF a v w h := bid_limit a (fun _ _ _=>rfl) (fun _ _=>rfl) (fun _ _=>rfl) h
  rightF a z := price_pos _ _ _ _ _ _ _ a z (by simp)
  before i j p l := fits_degree (mem_filter.mp p).2 l.symm
abbrev Pack (m B : Side) := Skin m B × Cue m
abbrev DriftY (m B : Side) := Pack m B × Cue m
abbrev Tide (m B : Side) := DriftY m B × Cue m
abbrev roster (m B : Side) (e : ℝ) := {t:DriftY m B| t.1∈payer m B e ∧ ZeroF m B t.1.1 t.2}
abbrev checked (m B : Side) (e : ℝ) := {t:Tide m B| t.1 ∈ roster m B e ∧ Arch m B t.1.1.1 t.1.1.2 t.1.2 t.2}
lemma roster_l (m B e) : LocallyCompactSpace (roster m B e) := by
  let f := fun t:DriftY m B=>(t.1.1,t.2)
  have hf : Continuous f := (continuous_fst.comp continuous_fst).prodMk continuous_snd
  exact (IsLocallyClosed.inter ((IsLocallyClosed.inter (IsClosed.isLocallyClosed ((cover_closed _ _).preimage (continuous_fst (Y:= Cue m)))) ((open0 m B).isLocallyClosed)).preimage continuous_fst) (((open0 m B).preimage hf).isLocallyClosed)).locallyCompactSpace
lemma gale_open (m B) : IsOpen {t : Tide m B | Arch m B t.1.1.1 t.1.1.2 t.1.2 t.2} := by
  let F := fun t:Tide m B=> (t.1.1.1,t.1.1.2,t.2); let H := fun t:Tide m B=>(t.1.1.1,t.1.2,t.2)
  exact ((openB m B).preimage (show Continuous F by unfold F; fun_prop)).inter ((openB m B).preimage (show Continuous H by unfold H; fun_prop))
lemma backed {X T : Type*} {K : Type*} [TopologicalSpace X] [TopologicalSpace T] [TopologicalSpace K] {A B : Set X} (f : X→T) (h : ContinuousOn f (A∩B)) (p : IsOpen B) (g : K→X) (hg : Continuous g) (q : ∀ k,g k∈A) {k} (e : g k∈B) : ContinuousAt (f ∘ g) k := by
  change Tendsto (f ∘ g) _ (𝓝 (f (g k)))
  exact Tendsto.comp (h _ ⟨q _,e⟩) (tendsto_nhdsWithin_iff.mpr ⟨hg.continuousAt, Eventually.and (Eventually.of_forall q) (hg.continuousAt (p.mem_nhds e))⟩)

abbrev lifted (m B : Side) (t : Tide m B) := bid m B t.1.1.1 t.1.1.2 t.1.2 t.2
abbrev cot (m B : Side) (p : DriftY m B) := law m B p.1.1 p.2
@[fun_prop] lemma lift_cont (m B) : Continuous (lifted m B) := bid_conn m B
lemma cot_cont (m B) : Continuous (cot m B) := by
  let f := fun t:DriftY m B=>(t.1.1,t.2)
  let L := fun t:Pack m B=>law m B t.1 t.2
  change Continuous (L ∘ f)
  exact (show Continuous L from law_cont m B).comp (show Continuous f by unfold f; fun_prop)
variable {E₁ : Type*} [NormedAddCommGroup E₁] [NormedSpace ℝ E₁]
def shade (m B : Side) (f : Tide m B→E₁) (u : DriftY m B) (v : Cue m) := lifted m B (u,v) • f (u,v)
def trip (m B : Side) (f : Tide m B→E₁) (t : DriftY m B) := ∫ x:Cue m, shade m B f t x ∂rains m
def flower (m B : Side) (f : Tide m B→E₁) (t : DriftY m B) := cot m B t • trip m B f t
def coastal (m B : Side) (f : Tide m B→E₁) (t : Pack m B) := ∫ x:Cue m, flower m B f (t,x) ∂rains m

structure Cargo (f : Tide m B→E₁) (e K : ℝ) : Prop where
  normC i (g : i∈checked m B e) : ‖f i‖≤K
  cont : ContinuousOn f (checked m B e)

variable {f : Tide m B→E₁} {e n : ℝ}
lemma Cargo.paid (h : Cargo f e n) : Gift (fun t:(roster m B e) × Cue m=>lifted m B (t.1.val,t.2)) (fun t => f (t.1.val,t.2)) n := by
  let v := lifted m B; let g := fun t:(roster m B e)×Cue m=>(t.1.val,t.2)
  change Gift (v ∘ g) (f ∘ g) n
  have hg : Continuous g := (continuous_subtype_val.comp continuous_fst).prodMk continuous_snd
  have he (t) (he:v (g t)≠0) : Arch m B t.1.val.1.1 t.1.val.1.2 t.1.val.2 t.2 := by
    let u := t.1.val; exact bid_ready u.1.1 _ _ t.1.property.1.2 t.1.property.2 he
  refine soft (fun i=> bid_live ..) (fun t q=>h.normC (g t) ⟨t.1.property, he _ q⟩) ((lift_cont m B).comp hg) ?_; intro x q
  exact backed f (show ContinuousOn f ((Prod.fst ⁻¹' roster m B e) ∩ _) from h.cont) (gale_open m B) g hg (fun i=>i.1.property) (he _ q)
lemma Cargo.tripC (h : Cargo f e n) : ContinuousOn (trip m B f) (roster m B e) := by
  letI := roster_l m B e
  rw [continuousOn_iff_continuous_restrict]; exact h.paid.settled
lemma Cargo.shadeC (h : Cargo f e n) (t : DriftY m B) (g:t∈roster m B e) : Continuous (shade m B f t) := by
  let A : roster m B e := ⟨t,g⟩
  let L := fun t : roster m B e × Cue m=>lifted m B (t.1.val,t.2) • f (t.1.val,t.2)
  change Continuous (L ∘ fun x=>(A,x))
  exact (show Continuous L from h.paid.weighted).comp (show Continuous (fun x:Cue m=>(A,x)) from continuous_const.prodMk continuous_id)
variable [CompleteSpace E₁]
lemma Cargo.trip_p (h : Cargo f e n) (t : DriftY m B) (g:t∈roster m B e) : ‖trip m B f t‖ ≤ n := by
  let F := fun x:Cue m=> ((⟨t,g⟩:roster m B e),x); let G := h.paid.pullGift F (continuous_const.prodMk continuous_id)
  let w := fun x:Cue m=> lifted m B (t,x)
  have hx : Continuous w := by change Continuous (lifted m B ∘ (fun x:Cue m=>(t,x))); exact (lift_cont m B).comp (continuous_const.prodMk continuous_id)
  have hew : ∫ x:Cue m,w x ∂rains m=1 := bid_norm t.1.1 t.1.2 t.2
  exact cap_mean (E:=E₁) (μ:=rains m) w (fun x=> f (t,x)) G.bounded G.pos hx G.weighted hew -- tune syntax
lemma Cargo.packed (h : Cargo f e n) : Gift (fun t:(payer m B e) × Cue m=> cot m B (t.1.val,t.2)) (fun t=> trip m B f (t.1.val,t.2)) n := by
  let v := cot m B; let g := fun t:(payer m B e) ×Cue m=> (t.1.val,t.2)
  change Gift (v ∘ g) (trip m B f ∘ g) _
  have hg : Continuous g := (continuous_subtype_val.comp continuous_fst).prodMk continuous_snd
  let Y := fun t:DriftY m B=> (t.1.1,t.2)
  let A : Set (DriftY m B) := Prod.fst ⁻¹' payer m B e
  let Z := Y ⁻¹' {t:Pack m B | ZeroF m B t.1 t.2}
  have hx (u) (x:v (g u) ≠ 0) : g u∈Z := law_rich m B _ _ x
  refine soft (fun _=> law_positive ..) (fun t he=> h.trip_p (g t) ⟨t.1.property,hx t he⟩) ((cot_cont m B).comp hg) (fun x e=> ?_)
  exact backed (trip m B f) (A:=A) h.tripC ((open0 m B).preimage (show Continuous Y by unfold Y; fun_prop)) g hg (fun i=>i.1.property) (hx x e)
lemma Cargo.coastalC (h : Cargo f e n) : ContinuousOn (coastal m B f) (payer m B e) := by letI := payer_space m B e; rw [continuousOn_iff_continuous_restrict]; exact h.packed.settled
lemma Cargo.flowerC (h : Cargo f e n) (t : Pack m B) (g:t∈payer m B e) : Continuous (fun x:Cue m=> flower m B f (t,x)) := by
  let L := fun t:(payer m B e) × Cue m=> cot m B (t.1.val,t.2) • trip m B f (t.1.val,t.2)
  change Continuous (L ∘ fun x=> ((⟨t,g⟩:payer m B e),x))
  exact (show Continuous L from h.packed.weighted).comp (show Continuous (fun x:Cue m=> ((⟨t,g⟩:payer m B e),x)) from continuous_const.prodMk continuous_id)
lemma Cargo.portC (h : Cargo f e n) (t : Pack m B) (g:t∈payer m B e) : ‖coastal m B f t‖ ≤ n := by
  let F := fun x:Cue m=> ((⟨t,g⟩:payer m B e),x); let G := h.packed.pullGift F (continuous_const.prodMk continuous_id)
  let w := fun x:Cue m=>cot m B (t,x)
  have hw : Continuous w := by change Continuous (cot m B ∘ (fun x:Cue m=>(t,x))); exact (cot_cont m B).comp (continuous_const.prodMk continuous_id)
  have hr : ∫ x:Cue m,w x ∂rains m=1 := rain_law m B t.1
  exact cap_mean (μ:=rains m) w (fun x=>trip m B f (t,x)) G.bounded G.pos hw G.weighted hr
end YM.CF.Phase
