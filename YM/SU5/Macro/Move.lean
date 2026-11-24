import YM.SU5.Selected.Time.Prom
import YM.Mink.Geometry
/-!
# Macroscopic test movements

Use standard `Mink.spacelike` in the model, `E4` in this file: taking ℓ² (not the height's max metric).
Rotation tests later will be on Euclidean supports with that API's own distances.
Careful: `act` here is real time!
-/
set_option autoImplicit false
noncomputable section
namespace YM.SatinMacro
open Function Set Filter Metric NormedSpace OS.Semigroup Bornology
open scoped Topology BigOperators InnerProductSpace NNReal

section spacetime
variable {j : Axis}

/-- Spatial/time decomposition of real spacetime in the j frame (3 for Mink supports). -/
def joinST (e : OS.Cross j) (t : ℝ) : E4 := e.val + t • basis j
@[simp] lemma joinST_clock (e : OS.Cross j) (t : ℝ) : joinST e t j=t := by
  change e.val j + t * basis j j = t
  simp [show e.val j=0 from e.property]
@[simp] lemma sep_joinST (e : OS.Cross j) (t : ℝ) : SEP j (joinST e t)=e := Subtype.ext (by
  change joinST e t - joinST e t j • _ = _; rw [joinST_clock]; exact add_sub_cancel_right ..)
lemma neg_joinST (e : OS.Cross j) (t : ℝ) : -joinST e t = joinST (-e) (-t) := by
  unfold joinST; rw [neg_smul,neg_add]; rfl
lemma joinST_self (x : E4) : joinST (SEP j x) (x j)=x := sub_add_cancel ..

/-- Relative to this base point. -/
def there (p : E4) (X : Set E4) := (fun x => x+p) '' X
lemma isOpen_there (p : E4) {X : Set E4} (h : IsOpen X) : IsOpen (there p X) := by
  exact (Homeomorph.addRight p).isOpenMap X h
lemma isCompact_there (p : E4) {X : Set E4} (h : IsCompact X) : IsCompact (there p X) :=
  h.image (continuous_add_const _)
lemma isBounded_there (p : E4) {X : Set E4} (h : IsBounded X) : IsBounded (there p X) :=
  ((h.isCompact_closure.image (continuous_add_const p)).isBounded).subset (Set.image_mono subset_closure)
lemma there_add (p q : E4) (X : Set E4) : there (p+q) X=there p (there q X) := by
  unfold there; rw [image_image]
  simp_rw [add_assoc,add_comm q]

/-- Spacelike pair of regions according to the ambient Mink geometry with time last. -/
def Apart (X Y : Set E4) := ∀ x∈X,∀ y∈Y, y-x∈Mink.spacelike
section ray
open Mink

private lemma len_spatial (e : OS.Cross timeAxis) : ‖spatial (e:E4)‖ = ‖(e:E4)‖ := by
  have hx := Mink.squares (e:E4)
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1
  simpa only [show (_root_.YM.time (e:E4))=0 from e.property, ne_eq, OfNat.ofNat_ne_zero,
    not_false_eq_true, zero_pow, add_zero] using hx.symm
lemma drift_clock (x y : E4) (e : OS.Cross timeAxis) (t : ℝ) : YM.time (y+joinST e t-x)=YM.time y + t-YM.time x := by
  change clockL (_-_)=_
  rw [map_sub,clockL_at,clockL_at,clock_add]
  exact congrArg (fun t=> YM.time y+t-YM.time x) (joinST_clock e t)
lemma drift_rest (x y : E4) (e : OS.Cross timeAxis) (t : ℝ) : spatial (y+joinST e t-x)=spatial e.val - (spatial x-spatial y):=by
  rw [←restL_at,map_sub]; simp_rw [restL_at,rest_add]; rw [joinST, rest_add, rest_mul, roll_space]; rw [smul_zero]; abel

/-- Even keep an entire bounded window of times *independent of displacement*.
One direction suffices (stronger: with the norm test no preferred spatial ray). -/
lemma uniformApart {X Y : Set E4} (x : IsBounded X) (y : IsBounded Y) (D : ℝ) :
    ∃ d : ℝ, ∀ (e : OS.Cross timeAxis), d < ‖(e:E4)‖ → ∀ t:ℝ, |t|≤D → Apart X (there (joinST e t) Y) := by
  have hu(T:Set E4)(h:IsBounded T) (F : E4 → ℝ) (p:Continuous F) : ∃ b : ℝ,∀ x∈T, F x ≤ b := by
    obtain ⟨b,t⟩:= (h.isCompact_closure.image p).bddAbove
    exact ⟨b,fun x w=>t (mem_image_of_mem _ (subset_closure w))⟩
  let qty (p:E4):=|YM.time p| + ‖spatial p‖
  have he : Continuous qty:= (clock_cont.abs).add rest_cont.norm
  obtain ⟨w,x'⟩:= hu X x qty he; obtain ⟨v,y'⟩:= hu Y y qty he
  refine ⟨w+v+D,fun e h t v x a b M=> ?_⟩
  obtain ⟨y,b,rfl⟩:=M
  rw [lateral,drift_clock,drift_rest]
  specialize x' x a; specialize y' y b; unfold qty at *
  have hy:= norm_sub_norm_le (spatial (e:E4)) (spatial x-spatial y); rw [len_spatial] at hy
  linarith [abs_sub (YM.time y+t) (YM.time x), abs_add_le (YM.time y) t,norm_sub_le (spatial x) (spatial y)]
lemma eventuallyApart {X Y : Set E4} (x : IsBounded X) (y : IsBounded Y)
    (e : OS.Cross timeAxis) (he : 0 < ‖(e:E4)‖) (D : ℝ) :
    ∀ᶠ u:ℝ in atTop, ∀ t:ℝ, |t|≤D → Apart X (there (joinST (u • e) t) Y):= by
  obtain ⟨b,v⟩:= uniformApart x y D
  filter_upwards [eventually_gt_atTop (b / ‖(e:E4)‖),eventually_gt_atTop (0:ℝ)] with u h q
  apply v
  change b < ‖u • (e:E4)‖
  rw [norm_smul, Real.norm_of_nonneg q.le]; exact (div_lt_iff₀ he).1 h
end ray
end spacetime

section ad
variable {H : Hilbert} (V : Spectral.Orbit H E4)
local notation "U" p:max => V.translation p
variable (p q : E4)
lemma move_join : (U p)*(U q)=V.translation (p+q) := V.sends ..
@[simp] lemma move_one : V.translation 0=1 := V.origin
lemma move_adjoint : star (U p)=V.translation (-p) := by
  have he : star (U p)*(U p)=1 := (ContinuousLinearMap.norm_map_iff_adjoint_comp_self (U p)).1 (V.unitary p)
  calc
   _ = (star (U p)*(U p))* V.translation (-p) := by rw [mul_assoc,move_join,add_neg_cancel,move_one,mul_one]
   _ = _ := by rw [he,one_mul]

def spindle : unitary H.Op:= ⟨V.translation p,⟨by rw [move_adjoint,move_join,neg_add_cancel,move_one],by rw [move_adjoint,move_join,add_neg_cancel,move_one]⟩⟩
/-- Act on the proposed local material. **Real translations**. -/
def act : H.Op≃⋆ₐ[ℂ] H.Op := Unitary.conjStarAlgAut ℂ H.Op (spindle V p)
lemma act_apply (A : H.Op) : act V p A= V.translation p * A * V.translation (-p) := by
  unfold act; rw [Unitary.conjStarAlgAut_apply]; change (U p) * A * star (U p) = _; rw [move_adjoint]
lemma act_add (A : H.Op) : act V p (act V q A)=act V (p+q) A:=by
  unfold act; rw [← Unitary.conjStarAlgAut_mul_apply]
  exact congrArg (fun B:unitary H.Op=> Unitary.conjStarAlgAut ℂ H.Op B A) (Subtype.ext (move_join ..))
@[simp] lemma act_zero (A:H.Op) : act V 0 A=A:= by rw [act_apply,neg_zero,move_one,one_mul,mul_one]

/-- The weak locality comparison on candidate field and adjoint vacuum vectors.
`X=A Ω`, `Y=B Ω`; `X'=A* Ω`, `Y'=B* Ω`. For [A*,act B]; no assumption of
working on the positive-energy projection w/o its adjoints. -/
def swap (X X' Y Y' : H) : Prop := inner ℂ X ((U p) Y)=inner ℂ Y' (V.translation (-p) X')

-- distinguish vacuum equality of the two operator orders
variable (w:H) (h:∀ p:E4, V.translation p w=w)
include h
lemma forward_price (A B:H.Op) : inner ℂ (A w) ((U p) (B w)) = inner ℂ w ((star A * act V p B) w):= by
  rw [act_apply]; change _= inner ℂ w (A.adjoint (_))
  rw [ContinuousLinearMap.adjoint_inner_right]
  change _ = inner ℂ (A w) ((U p) (B (V.translation (-p) w)))
  rw [h]
lemma reverse_price (A B:H.Op) : inner ℂ ((star B) w) (V.translation (-p) ((star A) w))=inner ℂ w ((act V p B*star A) w):=by
  change inner ℂ (B.adjoint w) _=_
  rw [ContinuousLinearMap.adjoint_inner_left,act_apply]
  let x:= B (V.translation (-p) (A.adjoint w)); change inner ℂ w x=inner ℂ w ((U p) x)
  rw [← ContinuousLinearMap.adjoint_inner_left (U p)]
  rw [show (U p).adjoint = V.translation (-p) from move_adjoint V p, h]
lemma swap_iff (A B:H.Op) : swap V p (A w) ((star A) w) (B w) ((star B) w) ↔
    inner ℂ w ((star A*act V p B) w)=inner ℂ w ((act V p B * star A) w):= by
  rw [swap,forward_price _ _ w h, reverse_price _ _ w h]
lemma swap_of_commute (A B:H.Op) (a:Commute (star A) (act V p B)) : swap V p (A w) ((star A) w) (B w) ((star B) w) :=
  (swap_iff V p w h A B).mpr (by rw [a.eq])
end ad

section heat
variable {H : Hilbert} {j : Axis} (S : OS.Semigroup H j)
lemma motion_apply (p : OS.Cross j) (t : ℝ) : S.unit.translation (joinST p t) = S.U p * S.edge t := by
  change S.edge _ * S.U _ = _
  rw [joinST_clock,sep_joinST]; exact S.both t p
lemma static (x : H) (h : x ∈ S.ground) (p : ∀ u, S.U u x=x) (v:E4) : S.unit.translation v x=x:=by
  rw [←joinST_self (j:=j) v,motion_apply]; change S.U _ (S.edge _ x)=x
  rw [Spectral.Alps.mink_invar S x _ h,p]
end heat
end YM.SatinMacro

#print axioms YM.SatinMacro.eventuallyApart
#print axioms YM.SatinMacro.swap_of_commute
#print axioms YM.SatinMacro.motion_apply
