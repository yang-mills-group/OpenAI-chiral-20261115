import YM.CF.Reflect.Edges

/-! Redundant halves splice exactly. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.RP
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Topology
open Function Fock Filter NormedSpace SU Lat Lattice Branch Cube Tenant Phase Mir Mir.Trip MeasureTheory Sample Finset
attribute [local instance] opCStarAlgebra
variable {m B : Side}

def stitch (m B : Side) (L : Finset (RZ m B)) (K : Finset (Index m)) (u v : Pack m B) := (patchF L u.1 v.1,patchF K u.2 v.2)
abbrev starR (m B : Side) (i : Axis) : Finset (RZ m B) := E₁ m B i∩E₂ m B i -- binder tune
abbrev starK (m : Side) (i : Axis) : Finset (Index m) := seaM m i∩seaP m i
def tiedK (m B : Side) (i : Axis) (x y z : Pack m B) : Pack m B := stitch m B (starR m B i) (starK m i) x (stitch m B (E₁ m B i) (seaM m i) y (Pbar m B i z))
structure NorthOf (m B : Side) (i : Axis) (u v : Pack m B) : Prop where
  gaugeS : Agrees (upField m B i) u.1 v.1
  labels : AgreeF (seaM m i) u.2 v.2
lemma NorthOf.rev {i u v} (h : NorthOf m B i u v) : NorthOf m B i v u := ⟨fun x l v=>(h.gaugeS x l v).symm,h.labels.flip⟩
variable (i : Axis) (x y z : Pack m B)
lemma upU (a) (h : a∈E₁ m B i) : (tiedK m B i x y z).1 a = if a∈E₂ m B i then x.1 a else y.1 a := by simp [tiedK,stitch,h,starR,patchF]
lemma downU (a) (h : a∈E₂ m B i) : (tiedK m B i x y z).1 a = if a∈E₁ m B i then x.1 a else (rayUK m B i z.1) a := by
  by_cases g:a∈E₁ m B i; simp [upU i x y z a g,h,g]; simp [tiedK,stitch,starR, Pbar,onPack,g,patchF,rayUK]
lemma upA (a) (h:a∈seaM m i) : (tiedK m B i x y z).2 a = if a∈seaP m i then x.2 a else y.2 a := by simp [tiedK,stitch,starK,patchF,h]
lemma downA (a) (h:a∈seaP m i) : (tiedK m B i x y z).2 a = if a∈seaM m i then x.2 a else z.2 (revI m i a) := by
  by_cases g:a∈seaM m i; simp [upA i x y z a g,h,g]; simp [tiedK,stitch,starK,Pbar,onPack,g,patchF,oncue,revI]
lemma strum (v : Pack m B) : NorthOf m B i (tiedK m B i x y z) (tiedK m B i x y v) := by
  refine ⟨fun a ha hb=> ?_, fun a ha=>?_⟩
  · have ht : a∈ E₁ m B i := mem_filter.mpr ⟨mem_univ _,ha,hb⟩; rw [upU i x y z a ht,upU i x y v a ht]
  rw [upA i x y z a ha,upA i x y v a ha]
lemma sew : Pbar m B i (tiedK m B i x y z)=tiedK m B i x z y := by
  apply Prod.ext
  · funext a; let t := rayE m B i a
    change rayUK m B i ((tiedK m B i x y z).1) a=_; rw [reflect_E]
    have ht : rayE m B i t=a := ray_back ..; have hv : t.2=a.2 := rfl
    by_cases l:a∈ E₁ m B i
    · rw [upU i x z y a l]; have hQ := (flipQ ..).mpr l; by_cases k:a∈E₂ m B i
      · rw [if_pos k,if_neg (sharedE a i l k).1,(sharedE a i l k).2,upU i x y z a l, if_pos k]
      have he : rayE m B i a∉E₁ m B i := fun p=> k ((flipsP ..).mp p)
      rw [downU i x y z (rayE m B i a) hQ,if_neg he, if_neg k,reflect_E,ray_back]; rw [show (rayE m B i a).2=a.2 from rfl]; split <;> simp
    have hA := (all_vars i a).resolve_left l; have hk := (flipsP a i).mpr hA; have hm : rayE m B i a∉E₂ m B i := fun g=> l ((flipQ ..).mp g)
    rw [downU i x z y a hA,if_neg l,reflect_E,upU i x y z _ hk, if_neg hm]
  funext a; let k := revI m i a; change (tiedK m B i x y z).2 k=_
  have hp : a∈ seaM m i ↔ k∈seaP m i := by have h := plane_turn (revI m i a) i; rw [map_back] at h; exact h
  rcases plane_all a i with h|h
  · rw [upA i x z y a h,downA i x y z k (hp.mp h),map_back]; by_cases l:a∈seaP m i
    · rw [if_pos ((plane_turn ..).mpr l),if_pos l, show k=a from plane_both a i h l]
    rw [if_neg (fun g=> l ((plane_turn ..).mp g)), if_neg l]
  rw [downA i x z y a h, upA i x y z k ((plane_turn ..).mpr h)]; by_cases l:a∈seaM m i
  · rw [if_pos l, if_pos (hp.mp l),show k=a from plane_both a i l h]
  rw [if_neg l, if_neg (fun g=> l (hp.mpr g))]
lemma barter (v : Pack m B) : Agrees (downField m B i) (tiedK m B i x y z).1 (tiedK m B i x v z).1 := by intro a ha hb; have ht : a∈ E₂ m B i := mem_filter.mpr ⟨mem_univ _,ha,hb⟩; rw [downU i x y z a ht,downU i x v z a ht]
lemma cap_pair {e} : Guard (tiedK m B i x y z).1 e ↔ Guard (tiedK m B i x y y).1 e ∧ Guard (tiedK m B i x z z).1 e := by
  let T := tiedK m B i x
  have he a b (h : Guard (T a b).1 e) : Guard (T b a).1 e := by
    have hg:=h; rw [show T b a=Pbar m B i (T a b) from (sew ..).symm]; exact through_guard _ h
  have hg a b c d e' (p:Guard (T a b).1 e) (q:Guard (T c d).1 e) (k:Agrees (upField m B i) e' (T a b).1) (v:Agrees (downField m B i) e' (T c d).1) : Guard e' e := by
    have ht (x:Site (Domain m B)) {j k' : Axis} (h:j≠k') : travel e' x (square j k')=travel (T a b).1 x (square j k') ∨ travel e' x (square j k')=travel (T c d).1 x (square j k') := by
      let W := square j k'; let D := visits x W; rcases stays x h i with hx|hx
      · exact Or.inl (travel_local x W _ _ (fun i g l=>k i (hx _ g) (hx _ l))) -- tune
      exact Or.inr (travel_local x W _ _ (fun i g l=>v i (hx _ g) (hx _ l)))
    constructor
    · intro i j k h; rcases ht i h with e|e; rw [e]; exact p.1 i j k h; rw [e]; exact q.1 i j k h
    intro i j k h; rcases ht i h with e|e; rw [e]; exact p.2 i j k h; rw [e]; exact q.2 i j k h
  constructor
  · intro h; exact ⟨hg y z z y _ h (he _ _ h) (strum i x y y z).gaugeS (barter i x y y z),hg z y y z _ (he _ _ h) h (strum i x z z y).gaugeS (barter i x z z y)⟩
  intro h; exact hg y y z z _ h.1 h.2 (strum i x y z y).gaugeS (barter i x y z z)
lemma stitch_cont (S T) : Continuous (fun p : Pack m B × Pack m B=>stitch m B S T p.1 p.2) := by
  unfold stitch; apply Continuous.prodMk
  · exact (patch_cont S).comp ((continuous_fst.comp continuous_fst).prodMk (continuous_fst.comp continuous_snd))
  exact (patch_cont T).comp ((continuous_snd.comp continuous_fst).prodMk (continuous_snd.comp continuous_snd))
lemma tiedC : Continuous (fun w:Pack m B× Pack m B× Pack m B => tiedK m B i w.1 w.2.1 w.2.2) := by
  let v := fun w:Pack m B × Pack m B=>stitch m B (E₁ m B i) (seaM m i) w.1 (Pbar m B i w.2)
  have he : Continuous v := by
    let f := fun q:Pack m B × Pack m B=> (q.1,Pbar m B i q.2)
    change Continuous ((fun p:Pack m B × Pack m B=>stitch m B _ _ p.1 p.2) ∘ f)
    exact (stitch_cont ..).comp (show Continuous f from continuous_fst.prodMk (((slideM m i).convey B).comp continuous_snd))
  let f := fun w:Pack m B× Pack m B × Pack m B=> (w.1,v w.2)
  change Continuous ((fun p:Pack m B × Pack m B=>stitch m B _ _ p.1 p.2) ∘ f); exact (stitch_cont ..).comp (show Continuous f from continuous_fst.prodMk (he.comp continuous_snd))
end YM.CF.RP
