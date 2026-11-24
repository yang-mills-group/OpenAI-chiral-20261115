import YM.CF.Appel.Patch
set_option autoImplicit false
noncomputable section
namespace YM.CF.Appel
open Char Summit Neige
open Function Filter Set Matrix Lattice Wilson RG Precision Pressure Tree Exterior MeasureTheory Metric Newt Jet
 AnalyticBridge.MarginalMultiplier3b1d AnalyticBridge.LocalGaussianLaws AnalyticBridge.SectorAffine
 AnalyticBridge.NonflatCovarianceLocality.Matching
open Push.SectorMeasure Next.Fluctuations Next.SectorChange Next.SectorChange.Wisps Next.SectorChange.Schur PhysicalNext.JointLoad PatchReads
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius InnerProductSpace ENNReal NNReal
variable {P:RG.Patch}{G:Gauge}{c f:Side}{S:StepData c f}{T:Tube G S}{A A':Stores S}{F F':Forest S.ratio}{k k':S.Choices} {V W:Config G c}{x C:ℝ}{r l:ℕ}
 {Y: LinkArray G (Frozen A x F)}{Y':LinkArray G (Frozen A' x F')}{o:Site c}
variable {α E:Type} [Fintype α][DecidableEq α] [NormedAddCommGroup E][NormedSpace ℝ E] {p:α→Site c} {K v d s t:ℝ} {n:ℕ}
open Gaussian ProbabilityTheory AnalyticBridge.Annulus1AD
open Set Topology
lemma tintF (x:Prices G α): ‖tape x‖≤ Push.Uniform.shade G*‖x‖:= by change ‖Push.Uniform.tint G α x‖≤_; exact Push.Uniform.tint_le x
lemma loomP (i:LogArray G α) : ‖tape.symm i‖≤ ‖i‖:=by apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr; rintro ⟨j,t⟩; exact (PiLp.norm_apply_le (i j) t).trans (norm_le_pi_norm i j)
def wireP(G:Gauge)(s d M B:ℝ):ℝ:= Push.Uniform.shade G*(B*(s⁻¹*(2*d + M)))
lemma spins (J:MA α G)(hJ:IsUnit J.det)(s:ℝ)(m:Prices G α)(p:‖m‖≤C)(hp:‖paintO J⁻¹‖ ≤ K)(z:LogArray G α)(q:Chi)(hs:0<s)(hd:0<d)(h:doors q d (spun J s m z)≠0): z∈surface G α (wireP G s d C K):=by
 let x:=tape.symm z; let y:= spinC J s m z; let t:=tape y
 have he: x =paintO J⁻¹ (s⁻¹ • (y-m)):=by change x =J⁻¹ *ᵥ _; unfold y spinC; rw [add_sub_cancel_left,smul_smul, inv_mul_cancel₀ hs.ne', one_smul,Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hJ,Matrix.one_mulVec]
 have hα : ‖t‖ ≤ 2*d := (pi_norm_le_iff_of_nonneg (by positivity)).mpr fun i => (broad_span q hd _ (every_door q h i)).le
 have hx: ‖x‖ ≤ K*(s⁻¹*(2*d+C)):=calc
    ‖x‖=‖paintO J⁻¹ (s⁻¹ • (y-m))‖:= congr_arg norm he
    _ ≤ K*‖s⁻¹ • (y-m)‖:= ((paintO J⁻¹).le_opNorm _).trans (mul_le_mul_of_nonneg_right hp (norm_nonneg _))
    _ ≤ _ := by rw [norm_smul,Real.norm_of_nonneg (inv_nonneg.mpr hs.le)]; apply mul_le_mul_of_nonneg_left _ ((norm_nonneg _).trans hp); apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr hs.le); apply (norm_sub_le ..).trans; apply add_le_add _ p; nth_rw 1 [← tape.symm_apply_apply y]; exact (loomP t).trans hα
 have ht: ‖z‖ ≤ wireP G s d C K:= by rw [← tape.apply_symm_apply z]; exact (tintF x).trans (mul_le_mul_of_nonneg_left hx (Push.Uniform.shade_pos G).le)
 exact fun i _=> mem_closedBall.mpr (by rw [dist_zero_right]; exact (norm_le_pi_norm z _).trans ht)
-- independent of Y: supports far enough.
variable {q:Chi}{D w H:ℝ}{i j:Rows.In x A F (G:=G)}
private lemma shush (Y Z:LinkArray G (Frozen A x F))(h:green x S A i.1.val.val)(hp:120≤radiusB x): Scan S x (front A F i) (25*radiusB x) A A F F k k V V Y Z:=by
 have hi:= groundF i h; unfold grounded at hi
 refine ⟨fun _ _=>Iff.rfl,fun _ _=> rfl,fun _ _=>rfl,fun _ _=> Iff.rfl,fun _ _=> rfl,?_⟩; intro j j' hj _
 let b:=j.val.val
 have hv:= Work.E03.parent_step S b.1 b.2
 obtain h|h :=j.property
 · obtain ⟨t,ht,he⟩:=halo_spec.mp h; exact (hi (halo_spec.mpr ⟨_,ht,(separation_triangle t (S.ratio.parent b.1) _).trans (by unfold b; rw [separation_comm (S.ratio.parent j.val.val.1)]; omega)⟩)).elim
 obtain ⟨t,ht,he⟩:=halo_spec.mp h; refine (hi (halo_spec.mpr ⟨_,ht,(separation_triangle t (S.ratio.parent (b.1+ Lattice.step b.2)) _).trans (by apply (Nat.add_le_add he ((separation_triangle _ (S.ratio.parent b.1) _).trans (Nat.add_le_add ((separation_comm ..).trans_le hv) ((separation_comm ..).trans_le hj)))).trans; omega)⟩)).elim
lemma stance (Z:LinkArray G (Frozen A x F))(hp:Ready T x)(hl:l≤18)(he:green x S A i.1.val.val): liftN T x V k A F q D Y l i=liftN T x V k A F q D Z l i:=by
 unfold liftN; rw [if_pos he, if_pos he]; apply orbitX (i:=i) hp _ _ _ ((shush Y Z he hp.length).lower (Nat.mul_le_mul_right _ (by omega))) rfl
lemma looser (Z:LinkArray G (Frozen A x F))(hp:Ready T x)(hl:l ≤ 18): hessN T x V k A F q D Y l=hessN T x V k A F q D Z l:=by
 ext i j; simp only [hessN,Matrix.of_apply]; split; rename_i H
 · have hm(r s:Rows.In x A F (G:=G))(he:green x S A r.1.val.val): headed T x V k A F (orbitP T x V k A F q D Y l) r s=headed T x V k A F (orbitP T x V k A F q D Z l) r s:=by
      have hx:= shush (k:=k) (V:=V) (i:=r) Y Z he hp.length
      apply head_read hp (hx.lower (by omega)) _ rfl rfl
      intro i j h h'; apply orbitX hp _ _ _ (hx.shrink ?_) h'; have hh: (l+1)*radiusB x≤ 19*radiusB x:=Nat.mul_le_mul_right _ (by omega); omega
   unfold AnalyticBridge.GaussianFieldAlignment.Relative.symPart; simp only [Matrix.smul_apply, Matrix.transpose_apply,Matrix.add_apply]; rw [hm i j H.1,hm j i H.2]
 rfl
lemma mastV (K:Teller G)(p:K.Funds S T)(h:Ready T x)(ht:l ≤18)(hd:0<D)(hr:2*D<firstRadius G)(hp:Offset.Shift n x d v D C T F A V k q): Continuous (fun Y=> liftN T x V k A F q D Y l):=by
 apply continuous_pi; intro i; by_cases hi:green x S A i.1.val.val
 · simp_rw [stance (i:=i) (1:LinkArray G (Frozen A x F)) h ht hi] -- loops
   exact continuous_const
 simp_rw [liftN,if_neg hi, fun Y=>(Offset.reads_actual _ _ _ _ _ _ _ Y _ (congr_fun hp.okay Y)).2.1]; exact (continuous_apply i).comp (meanLog_cont _ _ _ _ _ _ _ _ p hd hr) -- tune
end YM.CF.Appel
