import YM.CF.BProof.Grid.Skeleton
import YM.CF.BProof.Extension.SU
import YM.CF.BProof.Face

/-! Three-dimensional frame uniform purchase. Use `pay 3` independent of the final b.
-/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BProof.Grid
open Function Cube Entity SU Lattice Filter TopologicalSpace Set MeasureTheory Finset
open scoped Topology Matrix.Norms.Frobenius Classical BigOperators
local notation "M" => group.mat
local notation "G" => SU.group

lemma matrix_into (A : group.Mat) (h: Extension.inSU (N:=4) A) : ∃ u : E, M u=A := ⟨⟨⟨A,h.1⟩,h.2⟩,rfl⟩
def spinFiber : Fiber 3 G E where
 cost := cd G
 symm := cd_symm G
 self := cd_self G
 triangle := cd_triangle G
 C := 2
 C_one:=by norm_num
 diameter x y := group.chord_le_two _
 move u x := x*u⁻¹
 unit x:=by simp
 mul u v x:=by group
 isom u x y:= cd_mul_right ..
 pace u v x:=by rw [cd_mul_left,cd_inv]; linarith [cd_nonneg G u v]
 cont_d:= continuous_cd G
 cont_a:=continuous_snd.mul continuous_fst.inv
 extend K hk:=by
    let A:= group.colorScale; have hp:=group.colorScale_pos
    obtain ⟨L,hL,H⟩:= Extension.frame_extend (X:=Fin 3→ℝ) 4 1 (K*group.colorScale) one_pos (mul_pos hk hp) (by simp)
    refine ⟨L/group.colorScale,div_pos hL hp,fun S T f t v h hg=>?_⟩
    obtain ⟨V,H,q,Hf⟩:=H S T (M ∘ f) t v h (fun i _=>⟨(f i).val.property,fund_det _⟩) (fun x hx y hy=>by
       have hh: ‖M (f x)-M (f y)‖ ≤ K * Dist.dist x y*A := (norm_le_scale ..).mp (hg x hx y hy); exact hh.trans_eq (mul_right_comm ..))
    choose g hh using fun x:Fin 3→ℝ=> show ∃ v : E,x∈ S → M v= V x from by
       by_cases h:x∈ S; obtain ⟨g,hg⟩:=matrix_into _ (q x h); exact ⟨g,fun _=>hg⟩; exact ⟨1,fun p=>(h p).elim⟩
    refine ⟨g,fun x hx=> group.mat_injective ((show M (f x)=V x from Hf hx).trans (hh _ (v hx)).symm),fun x hx y hy=>?_⟩
    rw [norm_le_scale,hh x hx,hh y hy]; exact (show ‖V x-V y‖≤_ from H x hx y hy).trans_eq (by field_simp)
variable {s c : Side}(g:Ratio c s)

def go (q:Cubic 3 c→ E)(U:Wire G 3 s) := spinFiber.enter g {p|p.dim=0} (U, q ∘ elder g) 3
lemma go_m : Measurable (Function.uncurry (go g)) := by
 let f (p:(Cubic 3 c→ E) × Wire G 3 s): Fiber.Preg := (p.2,p.1 ∘ elder g) -- tune
 exact (spinFiber.enter_c ..).comp (f:=fun _ => _) (show Measurable f from measurable_snd.prodMk (measurable_pi_lambda _ fun i=> (measurable_pi_apply _).comp measurable_fst))
-- uses frame convention q U. 
variable {n : ℕ}
def SeatBound (Y : Gauge) {s:Side} (V : Floor Y.El n s)(U: Wire Y n s)(m:ℝ) := ∀ x i, cd Y (V x*U (x,i)) (V (slide x i)) ≤ m -- n

lemma go_est (q:Cubic 3 c→ E) (U:Wire G 3 s)(hc:4≤ c.val) {m:ℝ} (hm:spinFiber.cap g.count m)(h:Wire.Flat G U Set.univ m):
    SeatBound G (go g q U) U (spinFiber.pay 3/g.count.val)∧ ∀ x,go g q U (grow g x)=q x:=by
 have ht := spinFiber.stroll g (V:={p | p.dim=0}) (U,q ∘ elder g) Set.univ hc (show Settle _ from fun p hp q h=> Nat.eq_zero_of_le_zero (h.rank.trans (le_of_eq hp))) (fun _ _ _ _ => trivial) (fun p h=> spinFiber.zeroD g _ U p hc h _) hm (fun p _ x i j _ _ _ _=>h x i j trivial trivial trivial trivial) 3
 constructor
 · intro x i; obtain ⟨v,u,w⟩:= entire g hc x i; let p := Entity.mk v univ
   rw [← cd_mul_right G (U (x,i))⁻¹ (go g q U x*_ ) _, mul_inv_cancel_right]
   exact ht p trivial (by simp [Entity.dim,p]) _ _ u w
 intro x
 have hx := vtx (n:=3) g x |>.mpr (Eq.refl _)
 unfold go; rw [spinFiber.fix_old g]; simp only [Function.comp_apply, elder_grow]; exact Nat.eq_zero_of_le_zero ((Entity.chief_sub g _ hc _ hx).rank.trans (by simp [Entity.dim])) -- tune
lemma go_eq (q q':Cubic 3 c→ E)(U U':Wire G 3 s)(hc:4≤c.val)(p:Entity 3 c)(ht: Wire.Agrees G {x|p.Mem g x} U U') (h: EqOn (q ∘ elder g) (q' ∘ elder g) {x|p.Mem g x}): EqOn (go g q U) (go g q' U') {x|p.Mem g x}:=spinFiber.enter_eq g _ p hc (fun _ _=>Iff.rfl) ht h _ -- tune
lemma go_pin(q:Cubic 3 c→ E)(U:Wire G 3 s)(hc:4≤c.val)(x:Cubic 3 c): go g q U (grow g x)=q x:=by
 have hx := vtx (n:=3) g x |>.mpr (Eq.refl _)
 unfold go; rw [spinFiber.fix_old g]; simp only [Function.comp_apply, elder_grow]; exact Nat.eq_zero_of_le_zero ((Entity.chief_sub g _ hc _ hx).rank.trans (by simp [Entity.dim]))
end YM.CF.BProof.Grid
