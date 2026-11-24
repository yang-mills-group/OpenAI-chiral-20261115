import YM.SU5.Selected.Lantern.Winter
import YM.SU5.Selected.Lantern.Blend
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 450000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Pannier.Chancel.Lantern
open Function Filter NormedSpace Metric Lattice Wilson Laurent Finset Cube SU Fock Lat Spire Scroll MeasureTheory ProbabilityTheory Peaks Drapes Rush Tulip Dial Pastry
open Buffered Branch Tenant Skye RG
open Crest.Airy
open Reed (Fine)
open scoped Topology BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Matrix.Norms.L2Operator ComplexOrder
attribute [local instance] opCStarAlgebra
local notation "I"=>Complex.I
-- Loom of b-oriented packets. Pointwise expressions. No restriction on how choose term globally except uniform Blend fee.
variable {n:Side}{q:Type}[Fintype q][DecidableEq q]{v:ℕ}
structure Cab (n:Side) where
 broad: Finset (Seat n)
 core: Finset (Seat n) -- Frame columns fully supported here. may equal broad after halo^0.
 rev:Bool
 frame:Buffered.Mark n
-- abbrev home {n:Side}(S:Finset (Seat n))(q:Type):= Unit -- later
structure QModel (F: Fields n)(M:Tulip.Male)(j:ℕ)(R η ξ:ℝ) (b:Bool)(S:Finset (Seat n)) (X V:WRect (Single n) q) : Prop where
 hang: Contained (modesIn n S) X
 vine: Contained (modesIn n S) V
 pitch: hand (!b) (cutM (Tset n))*X=X
 ace: ‖X‖≤1
 stem: ‖V‖≤R
 need: ‖Xᴴ*V-1‖≤η
 lies: ‖((1-sp b j M F.2: Op (Single n)))* V‖≤ ξ
variable (M : Tulip.Male)(j w t : ℕ) (S:Finset (Seat n)) (τ η ξ J R δ:ℝ) (q:Type)[Fintype q][DecidableEq q] (r:ℕ)
abbrev Cab.feels(A:Cab n)(U: Fields n)(t:ℕ)(τ:ℝ): Prop := Disjoint (Lattice.halo t A.broad) (flags τ U.1)
private lemma fringe (t:ℕ)(i:Axis)(s₀:ℤ){S Q:Finset (Seat n)}(p:Distant t (Sᶜ) Q) : Distant t (hyphen i s₀ S)ᶜ (hyphen i s₀ Q):=by
 let f:= (plane i s₀).anon n; have hf: Involutive f:=fun x=> fling_there ..
 intro x hx y hy; obtain ⟨y,u,rfl⟩:= mem_image.mp hy; let z:= f x
 nth_rw 1 [← hf x]; exact (p z (mem_compl.mpr (fun h=> mem_compl.mp hx ((coal i s₀ S x).1 h))) y u).trans_eq (Next.Rank.Thirst.s_sep _ _ z y).symm -- tune

def Marquee (F: Fields n)(M: Tulip.Male)(j:ℕ)(R η ξ:ℝ)(b:Bool)(S:Finset (Seat n))(q:Type)[Fintype q][DecidableEq q](r:ℕ)(A:FC (Single n)): Prop:= ∃ (X Z: WRect (Single n) q) (L:List q), QModel F M j R η ξ b S X Z ∧ r≤ L.length ∧ L.Nodup ∧ A=fo (fun i=> handy b (Tset n) (col X i) (col Z i)) L

structure Lounge (A: Cab n) : Prop where
 shape: A.broad.Nonempty
 env: AtSupport false A.broad A.frame
 enroll: A.core⊆ A.broad
 fence: Distant w (A.broadᶜ) A.core
 expense(x: Fields n):‖A.frame x‖ ≤ J^r
 pressed(x:Fields n)(h:A.feels x t τ)(e: Agrees A.broad x.1 x.2)(p:Guard x.2 δ) : Blend (Marquee x M j R η ξ A.rev A.core q r) (J^r) (A.frame x)

#print Lounge.mk
abbrev safeReflect (M:Tulip.Male)(j:ℕ)(δ:ℝ)(n:Side):=∀ (x:Pane n), Guard x δ → ∀ (i:Axis)(s:ℤ)(b:Bool), twist (carR i s n) (sp b j M x) = sp (!b) j M (fling i s n x)
lemma safe_reflect (h:1≤j): ∃ δ> (0:ℝ),∃ k:ℕ,∀ n:Side,k≤n.val →∀ M:Tulip.Male, safeReflect M j δ n:=by
 obtain ⟨δ,hδ,k,z⟩:= Scroll.radiance j h; refine ⟨δ,hδ,k,fun n p M x u i s b=>?_⟩
 unfold sp; rw [handAgainst]; let V:=fling i s n x; have hp: twist (carR i s n) (spar j M x)=1-spar j M V:= funde_f (plane i s) inert (Window.pinLift i) (mirrorX i) x j h M δ (z n p) u
 rw [hp]; cases b; rfl; change 1-(1-spar j M V)=spar j M V; abel
lemma safe_reflect_smaller {M:Tulip.Male}{j:ℕ}{δ γ:ℝ}{n:Side}(p:safeReflect M j δ n)(h:γ≤δ): safeReflect M j γ n:=fun x e=>p _ (e.shrink h)
private lemma tonePreparation {q:Type}[Fintype q][DecidableEq q]{n:Type*}[Fintype n][LinearOrder n]{X:WRect n q} (T:UNI n)(P Q:Op n)(e:twist T P=Q): T.val*(P*X)=Q*(T.val*X):=by rw [←e,twist_formula]; simp only [Matrix.mul_assoc]; rw [← Matrix.mul_assoc (star _),show star T.val*T.val=1 from T.property.1, Matrix.one_mul]
lemma remodel {X V: WRect (Single n) q}{M:Tulip.Male}{j:ℕ}{F:Fields n}{η ξ R:ℝ}{S:Finset (Seat n)}{b:Bool}(p:QModel F M j R η ξ b S X V)(i:Axis)(s:ℤ)
    (h:twist (carR i s n) (sp b j M F.2) = sp (!b) j M (fling i s n F.2)) : let T:= (carR i s n).val; QModel (reflFields i s F) M j R η ξ (!b) (hyphen i s S) (T*X) (T*V) := by
 intro T; have ht:=p.hang; have hg:=p.vine; have hP(Y: WRect (Single n) q)(p:Contained (modesIn n S) Y):Contained (modesIn n (hyphen i s S)) (T*Y):=by
    exact (tonePreparation (X:=Y) _ _ _ (refl_modes i s S)).symm.trans (congrArg (fun Z:WRect (Single n) q=> T*Z) p)
 refine ⟨hP _ ht, hP _ hg,(tonePreparation _ _ _ (handTogether (flatTset i s) (!b))).symm.trans (by rw [p.pitch]),(rent_v ..).trans_le p.ace, (rent_v ..).trans_le p.stem, ?_, ?_⟩
 · rw [Matrix.conjTranspose_mul,Matrix.mul_assoc,← Matrix.mul_assoc Tᴴ, show Tᴴ*T=1 from (carR i s n).property.1, Matrix.one_mul]; exact p.need
 change ‖(1-sp (!b) j M _ : Op _)*(T*V)‖ ≤ ξ; rw [show (reflFields i s F).2=fling i s _ F.2 from rfl, ←tonePreparation (carR i s n) (1-sp b j M F.2) _ (by rw [map_sub,map_one,h]) ]; exact (rent_v ..).trans_le p.lies -- tone signature

lemma Marquee.flick {q:Type}[Fintype q][DecidableEq q]{n:Side}{x:Fields n}{M:Tulip.Male}{j r:ℕ}{R η ξ:ℝ}{b:Bool}{S:Finset (Seat n)}{A:FC (Single n)}(i:Axis)(s:ℤ)
    (h:twist (carR i s n) (sp b j M x.2)=sp (!b) j M (fling i s n x.2))(p:Marquee x M j R η ξ b S q r A): Marquee (reflFields i s x) M j R η ξ (!b) (hyphen i s S) q r (theta (carR i s n) A):=by
 let C:= carR i s n; obtain ⟨X,Z,W,l,g,t,rfl⟩:=p; refine ⟨C.val*X,C.val*Z,W,remodel _ l i s h,g,t,?_⟩ -- maybe q omitted? variable explicit
 let f(k:q):= handy b (Tset n) (col X k) (col Z k); let φ:FC (Single n)→* FC (Single n):= ⟨⟨theta C,theta_one _⟩,theta_mul _⟩
 change φ ((W.map f).prod)=_; rw [map_list_prod]; unfold fo; rw [List.map_map]; apply congrArg List.prod; congr 1; ext1 i'; dsimp only [Function.comp]; unfold f; simp_rw [line_a]; exact fields_r (flatTset i s) _ _
def Cab.shadow (A:Cab n)(i:Axis)(s:ℤ): Cab n:= ⟨hyphen i s A.broad, hyphen i s A.core,!A.rev,reflMark i s A.frame⟩
namespace Lounge
variable {M j w t τ η ξ J R δ q r}{A:Cab n} (p: Lounge M j w t τ η ξ J R δ q r A) (i:Axis)(s:ℤ)
-- Cabinet closure budget across reflections repeatedly. p.across even uses Aggregate exposures at aligned rails.
local notation "ρ" => fling i s n
local notation "σ" => hyphen i s
local notation "T" => theta (carR i s n)
include p
lemma shadow (v:safeReflect M j δ n): Lounge M j w t τ η ξ J R δ q r (A.shadow i s):=by
 refine ⟨p.shape.image _, p.env.refl .., image_subset_image p.enroll, fringe w i s p.fence, fun x=> ?_, fun x h l hw=>?_⟩
 · change ‖T _‖≤_; rw [theta, twist_norm,Scroll.norm_cc]; exact p.expense _
 let x':= reflFields i s x; let f:= (plane i s).anon n
 have hx : Guard x'.2 δ:=keepC inert (plane i s) x.2 δ hw
 have hv: A.feels x' t τ:=by
    unfold Cab.feels
    apply (Finset.disjoint_image (show Injective f from (show Involutive _ from fun a=>fling_there ..).injective)).1
    change Disjoint (σ (Lattice.halo t A.broad)) (σ (flags τ (ρ x.1))); rw [coal_flags,coal_halo]; exact h
 refine Blend.charge (S:=fun d a=> Blend (Marquee x M j R η ξ (!A.rev) (σ A.core) q r) d (T a)) (p.pressed x' hv (fling_local i s _ l) hx) (fun y z=>Blend.item (T y) ?_) ?_ ?_ ?_ ?_
 · have hg:= z.flick i s (v _ hx i s _); rwa [show reflFields i s x'=x from reflFields_inv i s x] at hg
 · rw [theta_zero]; exact .zero
 · intro a b x y hx hy; rw [theta_add]; exact hx.join hy
 · intro a x hx b; rw [theta_smul,show ‖b‖*a=‖star b‖*a by rw [norm_star]]; exact hx.smul _
 · intro a b y z v; exact z.extendsTo v
end Lounge
end YM.CF.Pannier.Chancel.Lantern
open YM.CF.Pannier.Chancel.Lantern
#print axioms Lounge.shadow
#print axioms safe_reflect
