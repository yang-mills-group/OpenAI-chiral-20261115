import YM.CF.Cubes.Pavilion
import YM.CF.Lattice.Own
import YM.CF.Phase.BaseState

/-! Inputs to the matrix comparison. Replica's reads remain planar in the even directions. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.Phase
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Topology
open Finset Function Fock Filter NormedSpace SU Lat Lattice Branch Cube Tenant
attribute [local instance] opCStarAlgebra
variable {m B N : Side}
abbrev duo (q s : Sq) : Bool→Sq := fun j=> if j then s else q
def touch (m B : Side) (q s : Sq) (U : Skin m B) (A : ArrayF m) : Tenant.Input (CSide m B) :=
  (U, fun j=> grain m B U A (duo q s j))
def twinR (m B : Side) (k : Index m) (q s : Sq) (U : Skin m B) (A : ArrayF m) : Tenant.Input (CSide m B) :=
  (replica m B k U,fun j=> paintV m B U A (duo q s j) ∘ snap m B k ∘ node)
lemma either_duo {q t r} (h : q∈zone r) (g : t∈zone r) (i) : duo q t i∈zone r := by cases i <;> simp [duo,h,g]
variable {q t : Sq} {r : Zone} {U : Skin m B} {A : ArrayF m} {e : ℝ} (b : Room B e) (h : Guard U e) (g : Verified m B margin U A r) (u : q∈zone r) (v : t∈zone r)
include b h g u v
lemma painted_gap (z : Site (Domain m B)) (H : ‖t-q‖ ≤ 2/(way B:ℝ)) : ‖localPair (paintV m B U A q z)-localPair (paintV m B U A t z)‖≤1/4 := by
  let Y := paintV m B U A
  have hp (i) (d:i∈zone r) : Y i z∈Sphere := by
    simp [Sphere,show ‖Y i z‖=1 from paint_unit (U:=U) d.1 b.1 h g d.2 b.2.2 _]
  apply cross_scale.choose_spec.2 (⟨Y q z,hp q u⟩:Ballot) (⟨Y t z,hp t v⟩:Ballot)
  rw [norm_sub_rev]
  exact (variations_le A t q v.1 u.1 b.1 h g v.2 u.2 b.2.2 _).trans_lt ((mul_le_mul_of_nonneg_left H (variation_pos B).le).trans_lt (way_room B))
lemma enter_pair (H : ‖t-q‖≤2/(way B:ℝ)) : TenantK (touch m B q t U A) := by
  refine ⟨plaq_lens b h, fun j=>grain_unit b h g (either_duo u v j),fun j=>(grain_j b h g (either_duo u v j)).2.2,?_⟩
  unfold Cfield; rw [←jump_sub]; exact jump_bound _ _ (by norm_num) fun i=>painted_gap b h g u v (node i) H
lemma replica_pair (a : Index m) (H : ‖t-q‖≤2/(way B:ℝ)) : TenantK (twinR m B a q t U A) := by
  refine ⟨plaq_lens b (tile_guard a h b.1), ?_, ?_, ?_⟩
  · intro j x; have hx := either_duo u v j; exact paint_unit (U:=U) hx.1 b.1 h g hx.2 b.2.2 _
  · intro j; have hx := either_duo u v j; have he := Guard.descend (tile_slow a _ (paint_slow hx.1 b.1 h g hx.2 b.2.2) (half_pos goal_pos))
    rw [show 2*(goal/2)=goal by ring] at he; exact he
  unfold Cfield; rw [←jump_sub]; exact jump_bound _ _ (by norm_num) fun i=>painted_gap b h g u v (snap m B a (node i)) H
-- gauge of data pulled to slab, no statement on marks
omit b h g u v in
lemma touch_g (f : Site (Domain m B)→E) : touch m B q t (gauge f U) (onF f A)=flipR f (touch m B q t U A) := by
  unfold touch flipR; dsimp only; congr; funext i x; rw [grain,paint_g]; rfl -- tune
omit b h g u v in
lemma twinR_g (a : Index m) (f : Site (Domain m B)→E) : twinR m B a q t (gauge f U) (onF f A)=flipR (f ∘ snap m B a) (twinR m B a q t U A) := by
  unfold twinR flipR; rw [replica_g]; dsimp only; congr; funext i x; rw [paint_g]; rfl
lemma compare_ink (S : Seal (Site (Domain m B))) (a : Index m) (L : ∀ x∈S, slab m B a x) (c d : ℝ)
    (J : ∀ x y:Vect, ‖x‖=1 → ‖y‖=1 → ‖x-y‖ ≤ d → ‖localPair x - localPair y‖≤c) (H : 4/low * pot B e≤d) :
    vacancy S (touch m B q t U A) (flipR (aligner a U) (twinR m B a q t U A)) ≤ (leaks S).card*pot B e+ (2:ℝ)*((news S).card*c) := by
  unfold vacancy; apply add_le_add
  · let x := touch m B q t U A; let y := twinR m B a q t U A; let k := aligner a U
    apply (sum_le_sum (g:=fun _=>pot B e) _).trans (le_of_eq (by simp))
    rintro ⟨z,i⟩ l
    change ‖color matter (U (z,i))-color matter ((flipR k y).1 (z,i))‖≤_
    apply (color_comm_cost ..).trans
    let X := U (z,i); let V := (flipR k y).1 (z,i)
    change ‖(matter (X * V⁻¹)).val-1‖ ≤ _
    have he : cmp matter X V≤pot B e := compare_align a (L z (mem_filter.mp l).2.1) i (L _ (mem_filter.mp l).2.2) b.1 matter h.2
    rw [cmp_g,Cube.cmp,map_one] at he; exact he
  apply (sum_le_sum (g:=fun _=> (news S).card*c) _).trans (le_of_eq (by simp)) -- tune
  intro j _
  apply (sum_le_sum (g:=fun _=>c) _).trans (le_of_eq (by simp))
  intro i l; have hx := L (node i) (mem_filter.mp l).2
  have he := either_duo u v j
  let F := paintV m B U A (duo q t j)
  have hf x : ‖F x‖=1 := paint_unit he.1 b.1 h g he.2 b.2.2 x
  apply J _ _ (hf _)
  · change ‖turn _ (F _)‖=1; rw [turn_norm]; exact hf _
  exact (painting_near a hx h b.1 he.1 g he.2 b.2.2.1).trans H
omit b h g u v
lemma axes_leak (S : Seal (Site N)) : (leaks S).card ≤ S.card*4 := by
  have ht : leaks S⊆ S ×ˢ (univ:Finset Axis) := fun x hx=> mem_product.mpr ⟨(mem_filter.mp hx).2.1,mem_univ _⟩
  exact (card_le_card ht).trans (by simp [Axis])
lemma place_news (S : Seal (Site (More N))) : (news S).card ≤ S.card := by
  rw [←card_image_of_injective (news S) needle]; apply card_le_card; intro x h; obtain ⟨i,k,rfl⟩ := mem_image.mp h; exact (mem_filter.mp k).2
lemma evenly (c:ℝ) (p:0<c) : ∃ d:ℝ, 0<d ∧ ∀ x y:Vect, ‖x‖=1 → ‖y‖=1 → ‖x-y‖ ≤ d → ‖localPair x - localPair y‖ ≤ c := by
  let f : Ballot→Op (SpinIdx×Slot) := fun v=>localPair v.val
  obtain ⟨d,h,e⟩ := Metric.uniformContinuous_iff.mp (CompactSpace.uniformContinuous_of_continuous (show Continuous f from localPair_cont.comp continuous_subtype_val)) c p
  refine ⟨d/2,half_pos h,?_⟩; intro x y px py g
  have he := (e (a:=⟨x,by simp [Sphere,px]⟩) (b:=⟨y,by simp [Sphere,py]⟩) (by rw [Subtype.dist_eq,dist_eq_norm]; exact g.trans_lt (half_lt_self h)))
  rw [dist_eq_norm] at he; exact he.le
-- limit the modified short supports uniformly on the chosen cap
lemma reserved (B : Side) (c:ℝ) (p:0<c) : ∃ d:ℝ, 0<d ∧ ∀ (e:ℝ), e≤d → Room B e → ∀ (m:Side) (U:Skin m B), Guard U e → ∀ (A:ArrayF m) (r : Zone) (x y : Sq), Verified m B margin U A r→x∈zone r→y∈zone r→∀ S:Seal (Site (Domain m B)), S.card≤B.val → ∀ a, (∀ x∈S,slab m B a x) → vacancy S (touch m B x y U A) (flipR (aligner a U) (twinR m B a x y U A))≤c := by
  let C := c/(8*(B.val:ℝ)); have hb : 0<(B.val:ℝ) := by exact_mod_cast B.property
  have he : 0<C := by unfold C; positivity
  obtain ⟨w,h,H⟩ := evenly C he
  have hp : ∃ d:ℝ,d∈Set.Ioi 0 ∧ 4/low*pot B d < w ∧ pot B d<C := by
    have heq : pot B 0=0 := by unfold pot; ring
    have hc : Continuous (pot B) := by unfold pot; fun_prop
    have hU : ∀ᶠ d in nhdsWithin (0:ℝ) (Set.Ioi 0), 4/low*pot B d<w := ((continuous_const (y:=4/low)).mul hc).continuousAt.continuousWithinAt (gt_mem_nhds (show 4/low*pot B 0<w by rw [heq,mul_zero]; exact h))
    have hV : ∀ᶠ d in nhdsWithin (0:ℝ) (Set.Ioi 0), pot B d<C := hc.continuousAt.continuousWithinAt (gt_mem_nhds (show pot B 0<C by rw [heq]; exact he))
    exact (Eventually.and (show ∀ᶠ d in nhdsWithin (0:ℝ) (Set.Ioi 0),d∈Set.Ioi 0 from self_mem_nhdsWithin) (hU.and hV)).exists
  obtain ⟨d,hf,g,q⟩ := hp
  refine ⟨d,hf,?_⟩; intro v t b m U e A r x y E X Y S hr a Hq
  have hx : pot B v≤ pot B d := by unfold pot; exact mul_le_mul_of_nonneg_left t (by positivity)
  apply (compare_ink b e E X Y S a Hq C w H ((mul_le_mul_of_nonneg_left hx (div_nonneg (by norm_num) low_p.le)).trans g.le)).trans
  have hi : ((leaks S).card:ℝ) ≤ B.val*4 := by exact_mod_cast (le_trans (axes_leak S) (Nat.mul_le_mul_right 4 hr))
  have hj : ((news S).card:ℝ) ≤ B.val := by exact_mod_cast ((place_news S).trans hr)
  have hP := add_le_add (mul_le_mul hi (hx.trans q.le) (by unfold pot; have he := b.1; positivity) (by positivity)) (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hj he.le) (show 0 ≤ (2:ℝ) by norm_num))
  apply hP.trans; unfold C; field_simp; nlinarith
end YM.CF.Phase
