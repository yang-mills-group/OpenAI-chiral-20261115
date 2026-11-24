import YM.CF.Scree.Locus
import YM.CF.Fixed.OneParticle

/-!
Exact symmetry of the `GramM.board` with the actual chosen branch/polynomial
budgets, used in Hermiticity, NOT yet a positivity or transfer argument. Includes
the force part outside the small-field region; strict `pingS` and the `flags`
support both transform (different tests), and tags on noncoincident priorities.
-/

set_option autoImplicit false
set_option maxHeartbeats 500000
set_option synthInstance.maxSize 24000
noncomputable section
namespace YM.CF.Fixed
open Function NormedSpace Filter Metric Finset Lattice Wilson Cube MeasureTheory Spire
open SU Lat Fock Scroll Tulip Skye Scree RG
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Kronecker
attribute [local instance] opCStarAlgebra

variable {N : Side} (i : Axis)

abbrev reflectSweep (N:Side) (i:Axis) : Sweep N:=⟨Signed.mirror i,0,false⟩
local notation "s_" => reflectSweep N i

lemma castX_reflect : castX s_=reflShape i:=by
  have he:Lattice.lift (0:Site N)=0:=funext fun i=> ZMod.valMinAbs_zero ..
  change Shape.mk (Signed.mirror i) _= _
  rw [he]
lemma inv_reflectSweep : (s_)⁻¹=s_:=by
  change Sweep.mk ((Signed.mirror i)⁻¹) _ _=Sweep.mk _ _ _
  rw [Signed.mirror_inv, Signed.act_zero,neg_zero]

lemma flash_reflect (U : Pane N) : flashA s_ U=reflConfig N i U := by
  rw [revoke]; change _=((Lattice.pull _ 0) U);
  rw [show (assembly N).embed (s_).b=0 from map_zero (assembly N).root]; rfl

lemma box_reflect (x : Seat N) : boxA s_ x=(Signed.mirror i).act x:=by
  rw [sitA, show (assembly N).embed (s_).b=0 from map_zero (assembly N).root]
  exact add_zero _

def swapSupport (X:Support (More N)) := X.map (boxA s_).symm.toEmbedding
lemma swapSupport_eq (X:Support (More N)) : swapSupport i X = reflRegion N i X:=by
  ext x
  rw [mem_reflRegion]; simp [swapSupport,box_reflect]
lemma hubSquare (x:Scree.Hub N) : moveHub s_ (moveHub s_ x)=x:=by
  have he:(boxA s_).symm=boxA s_ := (sitU s_).symm.trans (congrArg _ (inv_reflectSweep i))
  apply Subtype.ext
  change ((boxA s_).symm ((boxA s_).symm x.val.1), swapSupport i (swapSupport i x.val.2))=x.val
  refine Prod.ext ?_ ?_
  · change (boxA s_).symm ((boxA s_).symm x.val.1)= x.val.1
    nth_rw 1 [he]; exact Equiv.apply_symm_apply ..
  change swapSupport i (swapSupport i x.val.2)=_
  unfold swapSupport; ext y; simp [box_reflect, ← Signed.act_mul, square_mirror]

abbrev hubMirror : Equiv.Perm (Scree.Hub N):=⟨moveHub (reflectSweep N i),_,hubSquare i,hubSquare i⟩

lemma forceSquare (x : Force N) : moveForce s_ (moveForce s_ x)=x:=by
  apply Subtype.ext
  change (moveHub s_ (moveHub s_ x.val.1), swapSupport i (swapSupport i x.val.2))=x.val
  refine Prod.ext (hubSquare i _) ?_
  change swapSupport i (swapSupport i x.val.2)=_
  unfold swapSupport; ext y; simp [box_reflect, ← Signed.act_mul, square_mirror]

abbrev forceMirror : Equiv.Perm (Force N):=⟨moveForce (reflectSweep N i),_,forceSquare i,forceSquare i⟩
abbrev mirrorBoard (N:Side) (i:Axis) := paintR false true (reflectP N i)

-- Blackboard symmetry inputs available from IncX, Dark. No analytic continuation through flags.
lemma ping_reflect {t:ℝ} (X : Support (More N)) (U : Pane N) :
    pingS t (swapSupport i X) (flashA s_ U) ↔ pingS t X U:= by
  classical
  rw [flash_reflect]; let s:=Signed.mirror i; let z:Site (More N):=0
  have hp (k:Face (Per (More N))) : touched k=swapSupport i (touched (Face.send s z k)) := by
    have e: affine s z=(boxA s_) := funext fun x=>by
      rw [box_reflect]; exact add_zero _
    rw [Work.H03.touched_send]; ext x; simp only [swapSupport,mem_image,Finset.mem_map, Equiv.toEmbedding_apply]
    constructor
    · intro h; refine ⟨_,⟨x,h,rfl⟩,?_⟩
      rw [congrFun e x, Equiv.symm_apply_apply]
    rintro ⟨y,⟨y,g,rfl⟩,hx⟩
    rw [←hx, congrFun e y, Equiv.symm_apply_apply]; exact g
  have hχ (x:Face (Per (More N))) : SU.group.chord (faceValue (reflConfig N i U) x)=
      SU.group.chord (faceValue U (Face.send s z x)) := Face.send_price _ _ _ _ _ SU.group.chord_inv (fun u v=>SU.group.chord_conj _ _)
  constructor
  · intro h x g; obtain ⟨y,rfl⟩:=Finite.injective_iff_surjective.mp (Face.injective_send s z) x
    rw [←hχ]; apply h; rw [hp y]; exact fun p=>g ((Finset.disjoint_map _).mp p)
  intro h x g
  rw [hχ]; apply h; rw [hp] at g; exact fun p=>g ((Finset.disjoint_map _).mpr p)

-- labels use the actual `detX` convention. Pin is usable in the universal
-- quantifiers in `IncX.face` and `Dark.face`.
variable {Q:Sweep N→Prop} {p:BudgetPoint} {h d:ℝ}

lemma exponent_reflect {F:RegBudget N} (H: IncX Q F p h d) (he: Q s_) (U : Pane N) :
    exponentL p F (flashA s_ U)=mirrorBoard N i (exponentL p F U):=by
  have hP (u:Scree.Hub N) : F (moveHub s_ u) (flashA s_ U)=mirrorBoard N i (F u U):=by
    have ht := H.face s_ he (pinSpin i) (by rw [show (s_).s=Signed.mirror i from rfl, Spire.det_t]; exact mirrorX i) u U
    rw [show (s_).s=Signed.mirror i from rfl, Spire.det_t, castX_reflect] at ht; exact ht
  unfold exponentL; rw [map_sum];
  rw [← Equiv.sum_comp (hubMirror (N:=N) i) (fun v=>numbE p.threshold v.val.2 (F v) (flashA s_ U))]; apply Finset.sum_congr rfl
  intro j _; unfold numbE; by_cases hx:pingS p.threshold j.val.2 U
  · rw [Set.indicator_of_mem (show (flashA s_ U)∈ _ from (ping_reflect i j.val.2 U).2 hx), Set.indicator_of_mem (show U∈_ from hx)]
    exact hP j
  rw [Set.indicator_of_notMem (show (flashA s_ U)∉ _ from mt (ping_reflect i j.val.2 U).1 hx), Set.indicator_of_notMem (show U∉ _ from hx),map_zero]

abbrev reflectOrbit (V : Orbit N) : Orbit N:= (flashA s_ V.1, bun s_ V.2)

private theorem forceMask (p : BudgetPoint) (u:Finset (Force N)) (V:Orbit N) :
    let H:= u.map (forceMirror (N:=N) i).toEmbedding
    (coverF p H (flashA s_ V.1) ∧ Set.PairwiseDisjoint (H:Set (Force N)) (fun x=> x.val.1.val.2)) ↔
      coverF p u V.1 ∧ Set.PairwiseDisjoint (u:Set (Force N)) (fun x=> x.val.1.val.2) := by
  classical
  intro H
  let t:=forceMirror (N:=N) i
  have hu:(H.biUnion fun j=>j.val.2)=swapSupport i (u.biUnion fun j=>j.val.2):=by
    ext x; simp only [swapSupport,H, Finset.mem_map,mem_biUnion]
    constructor
    · rintro ⟨_,⟨j,hj,rfl⟩,hx⟩
      obtain ⟨y,hy,eq⟩:= Finset.mem_map.mp hx
      exact ⟨y,⟨j,hj,hy⟩,eq⟩
    rintro ⟨y,⟨j,hj,hy⟩,eq⟩
    exact ⟨t j,⟨j,hj,rfl⟩, eq ▸ Finset.mem_map_of_mem _ hy⟩
  apply and_congr
  · unfold coverF; rw [hu, flagsA]; exact (_root_.Finset.map_injective _).eq_iff
  have hp (j k:Force N) : Disjoint (t j).val.1.val.2 (t k).val.1.val.2 ↔ Disjoint j.val.1.val.2 k.val.1.val.2 := Finset.disjoint_map _
  constructor
  · intro p a g b k u; exact (hp a b).1 (p (Finset.mem_map_of_mem _ g) (Finset.mem_map_of_mem _ k) (t.injective.ne u))
  intro p a g b k u
  obtain ⟨j,hj,rfl⟩:= Finset.mem_map.mp g; obtain ⟨l,hl,rfl⟩ := Finset.mem_map.mp k
  exact (hp ..).2 (p hj hl (fun r=>u (congrArg t r)))

lemma fueled_reflect {F: ForceBudget N} (H:Dark Q F p h d) (he: Q s_) (V:Orbit N)
    (hp:Injective (priorP V.2)) : fueled p F (reflectOrbit i V)= mirrorBoard N i (fueled p F V):=by
  classical
  have hf (x:Force N) : F (moveForce s_ x) (reflectOrbit i V)= mirrorBoard N i (F x V):=by
    have ht := H.face s_ he (pinSpin i) (by rw [show (s_).s=Signed.mirror i from rfl, Spire.det_t]; exact mirrorX i) x V.1 V.2 hp
    rw [show (s_).s=Signed.mirror i from rfl, Spire.det_t, castX_reflect] at ht; exact ht
  let t:=forceMirror (N:=N) i; let K:=Equiv.finsetCongr t; let A(x:Orbit N)(U:Finset (Force N)) : Prop:= coverF p U x.1 ∧ Set.PairwiseDisjoint (U:Set (Force N)) (fun x=> x.val.1.val.2)
  let f(x:Orbit N) (U:Finset (Force N)) := if A x U then ∏ j∈U, Scree.clamp p j (F j) x else 0

  have heq(x:Orbit N) : fueled p F x=∑ i:Finset (Force N), f x i :=by unfold fueled; congr!
  rw [heq,heq,map_sum,←Equiv.sum_comp K (f (reflectOrbit i V))]
  apply Finset.sum_congr rfl; intro x _; unfold f; change _=
    mirrorBoard N i (if A V x then (_:Cipher N) else 0)
  have e : A (reflectOrbit i V) (K x) ↔ A V x:= forceMask i p x V
  by_cases g: A V x; swap
  · rw [if_neg g, if_neg (mt e.mp g), map_zero]
  rw [if_pos g,if_pos (e.mpr g)]
  rw [show K x=x.map t.toEmbedding from rfl, Finset.prod_map,map_prod]
  apply Finset.prod_congr rfl; intro y _
  have hv : boundF (t.toEmbedding y) p (reflectOrbit i V).1 ↔ boundF y p V.1 := by
    unfold boundF
    change pingS p.threshold (swapSupport i y.val.1.val.2 \ swapSupport i y.val.2) (flashA s_ V.1) ↔ _
    unfold swapSupport; rw [←Finset.map_sdiff]; exact ping_reflect ..
  by_cases b:boundF y p V.1
  · unfold Scree.clamp
    rw [if_pos (hv.mpr b), if_pos b]; exact hf y
  unfold Scree.clamp; rw [if_neg b, if_neg (mt hv.mp b),map_zero]

lemma board_reflect {R:GramM N} {w w' d' : ℝ}
    (A:IncX Q R.F R.p h w) (B:IncX Q R.slip R.p h w') (C:Dark Q R.K R.p h d')
    (he : Q s_) (x:Orbit N) (hp:Injective (priorP x.2)) :
    R.board (reflectOrbit i x)= mirrorBoard N i (R.board x) := by
  letI : NormedAlgebra ℚ (Cipher N) := NormedAlgebra.restrictScalars ℚ ℝ (Cipher N)
  unfold GramM.board
  change exp (exponentL _ _ (flashA s_ x.1)+exponentL _ _ (flashA s_ x.1))*_= _
  rw [exponent_reflect i A he, exponent_reflect i B he, fueled_reflect i C he x hp,
    map_mul, map_exp (mirrorBoard N i) (mirrorBoard N i).toLinearMap.continuous_of_finiteDimensional, map_add]

end YM.CF.Fixed
