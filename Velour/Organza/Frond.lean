import Velour.Organza.Residue
/-! Polynomial support nets on the common muslin, word cores. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option maxRecDepth 1100
noncomputable section
namespace YM.OS.Semigroup
open Function Set Filter Complex Analysis MeasureTheory
open scoped NNReal ENNReal Topology BigOperators ContDiff InnerProductSpace ComplexOrder
variable {H : Hilbert} {a : Axis} (S:Semigroup H a)


open Boundary Probe
local notation "R" => S.gauze
local notation "D" => S.muslin
local notation "B" => S.weight

local notation "E" => S.E
local notation "G" => S.heatL

local notation "U" => S.unit.translation
local notation "M" => S.liftL


def Firm (X:Module.End ℂ D):Prop:=
 ∃m,∀n,∃K,S.Refines X m n K

variable {S}
variable {X Y V Z:Module.End ℂ S.muslin}
lemma Refines.spare {J:H.Op}{m n:ℕ}(h:S.Refines X m n J) (l:ℕ):
 S.Refines X (m+l) n (J*R^l):= by
 intro x
 rw [h,mul_apply_eq_comp, add_right_comm, ← S.weight_div l, weight_cancel]

lemma Firm.mul (h:S.Firm X)(j:S.Firm Y):S.Firm (X*Y):=by
 obtain ⟨m,p⟩:=h; obtain ⟨l,q⟩:=j
 exact ⟨l+m,fun n=>⟨_, ((p n).choose_spec).mul (q (m+n)).choose_spec⟩⟩

lemma Firm.add (h:S.Firm X)(j:S.Firm Y):S.Firm (X+Y):=by
 obtain ⟨m,p⟩:=h; obtain ⟨l,q⟩:=j
 refine ⟨m+l,fun n=>?_⟩
 obtain ⟨K,k⟩:=p n
 obtain ⟨J,v⟩:=q n
 refine ⟨K*R^l + J*R^m,fun x=>?_⟩
 change (B n (X x+Y x)).val=_
 rw [map_add,Submodule.coe_add,k.spare l,v.spare m, add_comm l m]
 rfl




lemma Faces.unique (h:S.Faces X Y)(q:S.Faces X V):Y=V:=by
 ext1 y; apply Subtype.ext
 have d₀ : DenseRange (fun x:D=>x.val):= S.muslin_dense.mono (fun x p=>⟨⟨x,p⟩,rfl⟩)
 apply ext_inner_left ℂ
 exact congrFun (d₀.equalizer
     (continuous_id.inner continuous_const) (continuous_id.inner continuous_const)
     (funext fun x=>(h x y).symm.trans (q x y)))

lemma Faces.add (h:S.Faces X Y)(q:S.Faces V Z):
 S.Faces (X+V) (Y+Z):=by
 intro v w
 change inner ℂ ((X v).val+(V v).val) w.val=inner ℂ v.val ((Y w).val+(Z w).val)
 rw [inner_add_left,inner_add_right,h,q]
lemma Faces.symm (h:S.Faces X Y): S.Faces Y X:=by
 intro v w
 rw [← inner_conj_symm (Y v).val,← h,inner_conj_symm]


variable (S)
variable {κ:Type}
def Fray (J:κ→ℝ≥0→H.Op) (T:κ→S.Detector): Prop:=
 (∀i, S.Instates (J i) (T i)) ∧
   (∀i, ∃j, (fun t=> star (J i t)) =ᶠ[𝓝[>] (0:ℝ≥0)] J j)

def palette (T:κ→S.Detector) (P:Set Test4): Set (Module.End ℂ D):=
 {X|∃i,∃f∈P, T i f = X}
def grove (T:κ→S.Detector)(P:Set Test4): Subalgebra ℂ (Module.End ℂ D):=
 Algebra.adjoin _ (S.palette T P)

variable {S}
variable {T:κ→S.Detector} {P Q:Set Test4}{J:κ→ℝ≥0→H.Op}
lemma grove_mono (t:P⊆Q): S.grove T P≤S.grove T Q:=
 Algebra.adjoin_mono (by rintro _ ⟨i,f,p,rfl⟩; exact ⟨_,_,t p,rfl⟩)

lemma grove_seed (i:κ){f:Test4}(p:f∈P): T i f∈S.grove T P:=
 Algebra.subset_adjoin ⟨_,_,p,rfl⟩


lemma Touchable.gives {Y:S.Detector}(h:S.Touchable Y)(f:Test4): S.Firm (Y f):=by
 obtain ⟨m,p⟩:=h
 exact ⟨m,fun n=>⟨_,(p n).choose_spec f⟩⟩

lemma Fray.bound (h:S.Fray J T)(p:X∈S.grove T P): S.Firm X:=by
 refine Algebra.adjoin_induction (p:=fun x _=>S.Firm x) ?_ ?_
    (fun _ _ _ _ hx hy=>hx.add hy) (fun _ _ _ _ hx hy=>hx.mul hy) p
 · rintro _ ⟨i,f,g,rfl⟩
   exact (h.1 i).touch.gives f
 intro c
 refine ⟨0,fun n=>⟨c • 1,fun v=>?_⟩⟩
 rw [zero_add,Module.algebraMap_end_apply,map_smul];rfl

lemma Fray.faces (h:S.Fray J T)(p:MapsTo (⇑bar) P P)
 (w:X∈S.grove T P): ∃Y ∈ S.grove T P, S.Faces X Y:=by
 refine Algebra.adjoin_induction ?_ ?_ ?_ ?_ w
 · rintro _ ⟨i,f,t,rfl⟩
   obtain ⟨j,e⟩:=h.2 i
   exact ⟨_,grove_seed j (p t), (h.1 i).mirror (h.1 j) e f⟩
 · intro c
   refine ⟨_,(S.grove T P).algebraMap_mem (star c),fun x y=> ?_⟩
   rw [Module.algebraMap_end_apply, Module.algebraMap_end_apply]
   change inner ℂ (c • x.val) y.val=inner ℂ x.val (star c • y.val)
   rw [inner_smul_left,inner_smul_right];rfl


 · rintro _ _ _ _ ⟨_,u,v⟩ ⟨_,r,s⟩; exact ⟨_,add_mem u r,v.add s⟩
 rintro _ _ _ _ ⟨_,u,v⟩ ⟨_,r,s⟩
 exact ⟨_,mul_mem r u,v.mul s⟩

lemma Fray.covary (h:S.Fray J T)(u:E4)(p:MapsTo (⇑(ahead u)) P Q)(e:X∈S.grove T P):
 M u * X * M (-u)∈ S.grove T Q:=by
 revert e
 intro e
 refine Algebra.adjoin_induction (p:=fun x _=> M u*x*M (-u)∈ S.grove T Q) ?_ ?_ ?_ ?_ e
 · rintro _ ⟨i,f,t,rfl⟩
   rw [←(h.1 i).move]; exact grove_seed _ (p t)
 · intro c
   rw [←Algebra.commutes, mul_assoc,← liftL_add,add_neg_cancel, liftL_zero, mul_one]
   exact (S.grove T Q).algebraMap_mem _
 · intro x y _ _ hx hy; rw [mul_add, add_mul];exact add_mem hx hy
 intro x y _ _ hx hy
 have j:= (S.grove T Q).mul_mem hx hy
 rw [mul_assoc _ _ (M u*y*M (-u)),←mul_assoc _ _ (M (-u)),←mul_assoc (M (-u)),
    ←liftL_add, neg_add_cancel,liftL_zero,one_mul] at j
 simpa only [mul_assoc] using j


/-- Support grading. Bounded regions give compact supports if using closed bounded.
Keep all Test4 here including optional nonlocal test choice in unbounded region. -/
def placement (O:Set E4):Set Test4:= {f| tsupport f ⊆ O}

def pocket (T:κ→S.Detector)(O:Set E4): Subalgebra ℂ (Module.End ℂ D):=
 S.grove T (placement O)
lemma pocket_iso {O Q:Set E4}(p:O⊆Q): pocket T O≤ pocket T Q:=
 grove_mono (fun _ k=>Subset.trans k p)

private lemma barsupport (f:Test4) : tsupport (bar f)= tsupport f:=by
  unfold tsupport; congr 1; ext v; simp

lemma pocket_over {O:Set E4} : MapsTo (⇑bar) (placement O) (placement O):=by
  intro f t; change tsupport (bar f) ⊆ O; rwa [barsupport]







lemma LocalTest.ahead {f:Test4}(p:LocalTest f)(u:E4): LocalTest (Probe.ahead u f):=
 p.comp_homeomorph (Homeomorph.subRight u)

lemma placement_ahead (u:E4)(O:Set E4) :
   MapsTo (⇑(ahead u)) (placement O) (placement ((· - u) ⁻¹' O)):=by
   intro f p b e
   exact p ((tsupport_comp_subset_preimage f (f:=(· - u)) (by fun_prop)) e)

lemma pocket_covary (h:S.Fray J T)(u:E4)(O:Set E4)(e:X∈pocket T O):
 M u * X * M (-u)∈pocket T ((· - u) ⁻¹' O):= h.covary u (placement_ahead ..) e

lemma pocket_faces (h:S.Fray J T)(O:Set E4)(e:X∈pocket T O):
 S.Firm X ∧ ∃Y∈pocket T O,S.Faces X Y:=
 ⟨h.bound e,h.faces pocket_over e⟩
#print axioms pocket_faces
#print axioms pocket_covary

