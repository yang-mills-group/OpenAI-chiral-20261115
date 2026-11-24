import YM.CF.Char.Piste
import YM.CF.Char.Rue
set_option autoImplicit false
noncomputable section
namespace YM.CF.Char
open Function Filter Set Matrix Lattice Wilson RG Precision Pressure Tree Exterior MeasureTheory Metric Newt Jet
 AnalyticBridge.MarginalMultiplier3b1d AnalyticBridge.LocalGaussianLaws AnalyticBridge.SectorAffine
 AnalyticBridge.NonflatCovarianceLocality.Matching
open Push.SectorMeasure Next.Fluctuations Next.SectorChange Next.SectorChange.Wisps Next.SectorChange.Schur PhysicalNext.JointLoad PatchReads
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius InnerProductSpace
variable {P:RG.Patch}{G:Gauge}{c f:Side}{S:StepData c f}{T:Tube G S}{A A':Stores S}{F F':Forest S.ratio}{k k':S.Choices} {V W:Config G c}{x C:ℝ}{r l:ℕ}
 {Y: LinkArray G (Frozen A x F)}{Y':LinkArray G (Frozen A' x F')}{o:Site c}
open AnalyticBridge.GaussianFieldAlignment Orthogonal Tensor PhysicalNext.OrderedAffine2B.SymRows Gauges
variable {i j: Rows.In x A F (G:=G)}{s M d v D A₀ E:ℝ}{n:ℕ}{q:Chi}{z:Site c→G.El}{R:Directions G c→ Mast G c}
lemma poursF(hr:S.patch.Branches S.kernel G)(ht:T.up.Bounds T.high v D E): Flow (PhysicalNext.OrderedAffine2B.SymRows.room x A F) (rotating (constantGauge z⁻¹ S.ratio)) (outRotation z⁻¹) k k T (Lattice.gauge z V) V q d (gaugeY z x A F Y) Y:=by
 have hg: gauge z⁻¹ (gauge z V)=V:=by ext1 i; simp only [Lattice.gauge,Pi.inv_apply]; group
 have hf:= gaugeH T A F x (Lattice.gauge z V) k q d (gaugeY z x A F Y) z⁻¹ ht hr; rw [hg] at hf; rw [show gaugeY z⁻¹ x A F (gaugeY z x A F Y)=Y from ?_] at hf; exact hf
 ext1 i; simp only [gaugeY,Pi.inv_apply]; group
lemma readZ{E:Type}[NormedAddCommGroup E][NormedSpace ℝ E]{ι:Type}[Fintype ι]{f:E→ Fish ι}{x:E}(p:Allows n f x D) (i:ι) : Allows n (fun y=>f y i) x D:=((p.linear _ (show ‖ContinuousLinearMap.proj (R:=ℝ) (φ:=fun _ : ι=>ℝ) i‖ ≤ 1 from ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x=> (norm_le_pi_norm x i).trans_eq (one_mul _).symm)).mono (one_mul _).le)
lemma costZ{E:Type}[NormedAddCommGroup E][NormedSpace ℝ E]{α: Type}[Fintype α][DecidableEq α]{f:E→ Prices G α}{x:E}{i:α}(p:∀ j, Allows n (fun y=> f y (i,j)) x D)(hp:0≤D) (O:ColorOrtho G α) (j:G.ColorIndex): Allows n (fun y=> Orthogonal.move O (Equiv.refl _) (f y) (i,j)) x (Push.Uniform.shade G*D):=by
 let P(y:E):G.Color:=tape (Orthogonal.move O (Equiv.refl _) (f y)) i
 have hu:Allows n (fun y k=> f y (i,k)) x D:=allows_pi hp p
 let L:= (WithLp.linearEquiv 2 ℝ (Fish G.ColorIndex)).symm.toContinuousLinearEquiv
 let Q : Fish G.ColorIndex →L[ℝ] G.Color:= (O i).toContinuousLinearMap.comp L.toContinuousLinearMap
 have he : ‖Q‖≤Push.Uniform.shade G:=by
    apply ContinuousLinearMap.opNorm_le_bound _ (Push.Uniform.shade_pos _).le; intro w; change ‖O i (L w)‖≤_; rw [LinearIsometry.norm_map]
    let b: Fish (Unit × G.ColorIndex):= w ∘ Prod.snd; have hx:L w=Push.Uniform.tint G _ b ():=rfl
    have hp: ‖b‖≤‖w‖:=(pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr fun i=> norm_le_pi_norm w _
    rw [hx]; exact ((norm_le_pi_norm ..).trans (Push.Uniform.tint_le b)).trans (mul_le_mul_of_nonneg_left hp (Push.Uniform.shade_pos _).le)
 have ht: Allows n P x (Push.Uniform.shade G * D):=(hu.linear _ he).germ (Eventually.of_forall fun y=>(move_tape O (Equiv.refl _) (f y) i).symm)
 let V:= (ContinuousLinearMap.proj (R:=ℝ) (φ:=fun _ : G.ColorIndex=>ℝ) j).comp L.symm.toContinuousLinearMap
 have hv: ‖V‖≤1:=ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun i=> by rw [one_mul]; exact PiLp.norm_apply_le i j
 exact (ht.linear V hv).mono (one_mul _).le
lemma groundF (i:Rows.In x A F (G:=G))(hp:green x S A i.1.val.val): grounded (front A F i) A x:= hp _ (by change S.ratio.parent _∈_; simp [Next.SectorChange.points])
def cot(T:Tube G S)(x:ℝ)(V:Config G c)(k:S.Choices)(A:Stores S)(F:Forest S.ratio)(q:Chi)(d:ℝ)(Y:LinkArray G (Frozen A x F))(l:ℕ):= liftN T x V k A F q d Y l-Offset.mean T x k A F q d Y V
lemma cot_p(l:ℕ)(h:Flow (PhysicalNext.OrderedAffine2B.SymRows.room x A F) (rotating (constantGauge z⁻¹ S.ratio)) (outRotation z⁻¹) k k T (Lattice.gauge z V) V q d (gaugeY z x A F Y) Y)(hp:S.patch.Branches S.kernel G)(hT:T.up.Bounds T.high v D E) :
 cot T x V k A F q d Y l= Orthogonal.move (onBond (rotating (constantGauge z⁻¹ S.ratio))) (Equiv.refl _) (cot T x (Lattice.gauge z V) k A F q d (gaugeY z x A F Y) l):=by
 unfold cot; rw [boxL h (fun i=>Iff.rfl) hp hT,h.meanP hT hp]; symm; exact Matrix.mulVec_sub ..
lemma cept(hr:Ready T x)(ht:T.up.Bounds T.high v D E)(l:ℕ)(hL:l ≤18) {i:Active A x F}(hg:green x S A i.val.val)(hh:Fleet S x V F A Y z k R (S.ratio.parent i.val.val.1) s)(hR:Allows n R 0 (1/2)) (hc: Allows n (fun y=>orbitP T x (facadeX G (s•y)) k (bareStores S) F q d 1 l-Offset.mean T x k (bareStores S) F q d 1 (facadeX G (s•y))) (R 0) M) (j:G.ColorIndex): Allows n (fun y=> cot T x (Vmove x V y) k A F q d Y l (i,j)) 0 (Push.Uniform.shade G * Jet.composeCost n M (1/2)):=by
 let Q(y:Directions G c):= gauge z (Vmove x V y); let W(y:Directions G c):=cot T x (Q y) k A F q d (gaugeY z x A F Y) l; let N:= composeCost n M (1/2); have hK:=hc.comp hR
 have hP (j:G.ColorIndex): Allows n (fun y=> W y (i,j)) 0 N:=by
    let u:Active (bareStores S) x F:=⟨i.val,notChilled S F x _⟩
    let b:Rows.In x (bareStores S) F (G:=G):=(u,j); have he:PatchReads.lift (A:=A) (i,j)= PatchReads.lift b:=rfl
    apply (readZ hK b).germ; filter_upwards [hh] with y hy
    unfold W cot; dsimp only [Pi.sub_apply,liftN]; rw [if_pos hg, orbitX hr q d l (i:=(i,j)) (hy.lower (by exact Nat.mul_le_mul_right _ (by omega))) he, meetX hr (i:=(i,j)) (hy.lower (by omega)) he]
 have hp : 0≤N:= hK.nonneg
 apply (costZ hP hp (onBond (rotating (constantGauge z⁻¹ S.ratio))) j).germ
 exact Eventually.of_forall fun y=> (congr_fun (cot_p (z:=z) (V:=Vmove x V y) l (poursF hr.rules ht) hr.rules ht) (i,j)).symm
end YM.CF.Char
