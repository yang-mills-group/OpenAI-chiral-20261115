import YM.CF.BProof.Single.Tile
/-! Paths of stamps in Stage. Keep continuous evaluation. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BProof.Spin
open Function Filter NormedSpace Fock Finset Branch Tenant Cube SU Tulip Lat Lattice Dial Stint SU.Pair
open scoped Topology BigOperators Matrix MatrixOrder InnerProductSpace Kronecker Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
variable {s N:Side}
def motion (g:E)(B:Stamp):= congrC (matter g) B
lemma motion_seq (g h:E)(B:Stamp): motion (g*h) B=motion g (motion h B):=by unfold motion congrC; rw [map_mul]; change ((matter g).val*_*_)*(_*_)ᵀ=_; rw [Matrix.transpose_mul]; simp only [mul_assoc]
@[simp] lemma motion_one : motion 1=id:= by ext b i j; change motion 1 b i j=_; unfold motion congrC; simp only [map_one]; simp
lemma motion_sub (g:E)(A B: Stamp) : motion g (A-B)=motion g A-motion g B:=by unfold motion congrC; rw [mul_sub,sub_mul]
lemma motion_frame (g:E)(A B:Stamp) : ‖motion g A-motion g B‖=‖A-B‖:=by rw [←motion_sub]; exact congr_norm ..
theorem seal_move (g:E){B:Stamp}(h:SealH B):SealH (motion g B):= ⟨val_con _ ⟨_,h.norm⟩,by unfold motion congrC; rw [Matrix.transpose_mul,Matrix.transpose_mul,h.symm, Matrix.transpose_transpose,mul_assoc],by unfold motion congrC; rw [Matrix.det_mul,Matrix.det_mul,h.det,Matrix.det_transpose,matter_matrix,triple_det]; simp⟩
def stitch (g: Geometry N)(A: Quilt N): Quilt N:=fun z=> motion (g z) (A z)
lemma pair_spin (u: Geometry N)(A:Quilt N) : pair (stitch u A)=congrC (tradew N u) (pair A):=by
 unfold pair congrC; rw [show (tradew N u).val=joint (fun z=>(matter (u z)).val) from rfl]; rw [←mul_assoc (joint _), ←(tile_joint _).eq,mul_assoc,mul_assoc,joint_tr,joint_mul,joint_mul]; congr 2; funext z; unfold stitch motion congrC; rw [mul_assoc]
lemma pair_bound {A:Quilt N}{r:ℝ}(hr:0≤r)(h:∀ z, ‖A z‖≤r): ‖pair A‖≤r:=(norm_mul_le ..).trans (by rw [CStarRing.norm_of_mem_unitary (tile_unit N),one_mul]; exact jump_bound _ _ hr fun i=> h (node i.1))
lemma pair_difference (A B: Quilt N) : pair A - pair B = pair (A-B):=by unfold pair; rw [←mul_sub,joint_sub]
@[fun_prop] lemma pair_cont : Continuous (pair (N:=N)):=by
 apply continuous_matrix; rintro i j; simp_rw [pair_local]; split; fun_prop; exact continuous_const
lemma pair_cell (A : Quilt N)(i j:Single N): ‖pair A i j‖≤ ‖A (badgeOf i)‖:=by
 rw [pair_local]; split; rw [norm_mul]; exact (mul_le_of_le_one_left (norm_nonneg _) ((norm_entry ..).trans_eq (CStarRing.norm_of_mem_unitary spinJ_unitary))).trans (norm_entry ..); rw [norm_zero]; exact norm_nonneg _
variable {D:Type}[TopologicalSpace D](b:Feet N D)
lemma earnsTile (r:ℝ)(hr:1≤r) : ∃ t:Pay, ∀ {D:Type} [TopologicalSpace D] {N:Side} (b:Feet N D)(F:D→ Quilt N), Continuous F → (∀ g x, F (b.st.drive g x)= stitch g (F x))→ (∀ x i, ‖F x i‖≤r)→(∀ (x y:D)(i:Single N), ‖F x (badgeOf i)- F y (badgeOf i)‖≤ r*b.st.eval {badgeOf i} x y)→ Earn t b.mark b.mark.reverseV (fun x=> pair (F x)):=by -- binders v lift
 let q:=quota*((↑(0:ℕ):ℝ)+1)^4 *Real.exp (1*(quota*((↑(0:ℕ):ℝ)+1)^4))*r; have hx:=quota_p; refine ⟨⟨1,q,one_pos,(by unfold q; positivity)⟩,?_⟩; intro D _ N b F p g h v; refine row_earn (m:=0) b.cap quota_p.le zero_le_one ?_ (pair_cont.comp p) (zero_le_one.trans hr) ?_ ?_ ?_ -- m duplicated
 · intro i x; simp only [Function.comp_apply]; rw [g,pair_spin]; exact congr_product ..
 · intro x i j t; rw [b.town,b.index] at t; simp only [Function.comp_apply]; rw [pair_local,if_neg (fun m=>?_)]
   change 0<separation _ _ at t; have hz: badgeOf i=badgeOf j:=congrArg node m; rw [hz,separation_self] at t; exact lt_irrefl _ t
 · intro i j x; exact (pair_cell ..).trans (h ..)
 intro i j x y; apply le_trans (b:=‖(F x - F y) (badgeOf i)‖); · change ‖(pair (F x)-pair (F y)) i j‖≤_; rw [pair_difference]; apply pair_cell
 exact (v ..).trans (mul_le_mul_of_nonneg_left (b.st.includeV (singleton_subset_iff.mpr (by rw [b.index]; exact (bay_mem _).mpr (by rw [b.st.F.reflex]))) x y) (zero_le_one.trans hr))
end YM.CF.BProof.Spin
