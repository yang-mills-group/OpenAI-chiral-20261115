import YM.CF.Char.Calls
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
open Push Push.Uniform
abbrev clipped(T:Tube G S)(x:ℝ)(F:Forest S.ratio)(k:S.Choices):=costP F k T.high (grainA T.up (Stores.till x))
abbrev facadeX (G:Gauge)(u:Mast G c):= increment 1 (hull G c u)
local notation "L"=> bareStores S
local notation "P"=> pageX (G:=G) F x
abbrev trays(S:StepData c f)(x:ℝ)(F: Forest S.ratio)(a:Fish (Key F G)):= Rows.fresh x (shots S x) (bareStores S) F (tape (leaveX F x a))
lemma tray_x (F:Forest S.ratio)(x:ℝ)(u:Mast G c)(a:Fish (Key F G)):
 increment (replica S.ratio (facadeX G u)) (trays S x F a)= fine G F (meetVar u a):=by
 let z:= paint F G (meetVar u a); let V:= facadeX G u
 have he:z=(tint G _ u,tint G _ a):=by unfold z paint; dsimp only [ContinuousLinearEquiv.trans_apply]; rw [meetVar,ContinuousLinearEquiv.apply_symm_apply]; rfl
 change _=Precision.lifting F (represent z.1) z.2; rw [he]; change increment (replica S.ratio V) _= Precision.lifting F V (tint G _ a)
 let b:= trays S x F a
 ext1 i
 by_cases hi:i∈F.trunks
 · have hg : replica S.ratio V i=1:= if_pos (F.trunk_internal (by exact hi)); rw [increment,hg,trays,Rows.fresh,dif_neg (not_not.mpr hi),G.mat_lieExp_zero,mul_one,lifting,F.on_tree _ ⟨i,hi⟩]
 let j:F.Free:= ⟨i,hi⟩; let p:Active L x F:= ⟨j,notChilled S F x j⟩; rw [increment,show trays S x F a i=tape (leaveX F x a) p from Gap.freshly_read L F _ _ p, lifting, F.off_tree _ ⟨i,hi⟩]
 have hu:tape (leaveX F x a) p=(tint G _ a) j:=by
    ext k; change a ((pageX (G:=G) F x).symm (p,k))=a (j,k); exact congr_arg a ((pageX (G:=G) F x).symm_apply_apply (j,k))
 rw [hu]
lemma clip_actual(u:Mast G c)(a: Fish (Key F G)): rack T x (facadeX G u) k (trays S x F a)=clipped T x F k (meetVar u a):=by
 rw [rack_actual, tray_x F]; rfl
lemma trays_add(a b: Fish (Key F G)): trays S x F (a+b)= trays S x F a+trays S x F b:=by unfold trays; rw [map_add]; change Rows.fresh _ _ _ _ (colors _) =_; rw [map_add, Rows.fresh_add]; rfl
lemma trays_smul (w:ℝ)(a: Fish (Key F G)):trays S x F (w • a)=w • trays S x F a:=by unfold trays; rw [map_smul]; change Rows.fresh _ _ _ _ (colors _) =_; rw [map_smul,Rows.fresh_smul]; rfl
def agentX(i:Key F G):G.Color →L[ℝ] Fish (Key F G) := (tint G F.Free).symm.toContinuousLinearMap.comp (ContinuousLinearMap.single ℝ (fun _=>G.Color) i.1)
lemma trays_A(i:Key F G)(u:G.Color): trays S x F (agentX i u)=Pi.single i.1.val u:=by
 let A: Active L x F:= ⟨i.1,notChilled S F x i.1⟩; ext1 j
 unfold trays Rows.fresh; by_cases h:j=i.1.val
 · subst j; rw [dif_pos i.1.property,dif_pos A.property,Pi.single_eq_same]; ext k
   have he:P (i.1,k)=(A,k):=rfl
   change agentX i u ((P).symm _) = _; rw [← show _=_ from he,(P).symm_apply_apply]; change (Pi.single (M:=fun _=>G.Color) i.1 u i.1) k=_; rw [Pi.single_eq_same]
 rw [Pi.single_eq_of_ne h]; split
 next hs=>
    split
    next ha=>
        let p:Active L x F:= ⟨⟨j,hs⟩,ha⟩; ext k; have he:P (p.val,k)=(p,k):=rfl
        change agentX i u ((P).symm (p,k)) = (0:G.Color) k; rw [← he,(P).symm_apply_apply]; change (Pi.single (M:=fun _=>G.Color) i.1 u p.val) k=_; rw [Pi.single_eq_of_ne (show p.val ≠ i.1 from fun hh=> h (congr_arg Subtype.val hh))]
    rfl
 rfl
lemma agent_b (i:Key F G): agentX i (epsI G i.2)=bolt i:=by
 change (tint G F.Free).symm (Pi.single i.1 ((EuclideanSpace.basisFun _ ℝ) i.2))= _
 apply (tint G F.Free).injective; rw [ContinuousLinearEquiv.apply_symm_apply]
 ext j a; change (Pi.single (M:=fun _=>G.Color) i.1 ((EuclideanSpace.basisFun _ ℝ) i.2) j) a=(bolt i (j,a)); by_cases h:j=i.1
 · subst j; by_cases h:a=i.2 <;> simp [bolt,h,Pi.single_apply]
   exact fun hh=>h (congr_arg Prod.snd hh)
 simp [bolt,Pi.single_apply,show ¬(j,a)=i from fun hp=>h (congr_arg Prod.fst hp),h]
lemma cumu {ι τ : Type} [Fintype ι] [Fintype τ](i:Fish ι)(j k:Fish τ): meetVar i (j+k)= meetVar i j+lowerCol k:=by change meetVar _ _ = _+meetVar (0:Fish ι) k; unfold meetVar; rw [← map_add]; congr; simp
variable {u: Mast G c}{a:Fish (Key F G)}
-- pointwise uniform comparison
lemma driveB(i:Key F G)(h:ContDiffAt ℝ ω (clipped T x F k) (meetVar u a)):
 pushed T x (facadeX G u) k L F (leaveX F x a) (P i)= Slope (clipped T x F k) (meetVar u a) i:=by
 let T':=clipped T x F k; let p:=meetVar u a; let U: G.Color→L[ℝ] Fish (Joint F G):= lowerCol.comp (agentX i)
 change fderiv ℝ (drive T x (facadeX G u) k (trays S x F a) i.1.val) 0 _= _
 have he : drive T x (facadeX G u) k (trays S x F a) i.1.val=(fun v=> T' (p+U v)-T' p):=by ext1 v; unfold drive; rw [← trays_A,← trays_add,clip_actual,clip_actual,cumu]; rfl
 let B:G.Color→ Fish (Joint F G):= fun i=>p+U i; have hb:B 0=p:= by simp [B]
 have ht:HasFDerivAt B U 0:= U.hasFDerivAt.const_add _
 have hh:HasFDerivAt (fun v=> T' (p+U v)-T' p) ((fderiv ℝ T' p).comp U) 0:=(((hb.symm ▸ (show HasFDerivAt T' (fderiv ℝ T' p) p from (h.differentiableAt (by simp)).hasFDerivAt) : HasFDerivAt T' (fderiv ℝ T' p) (B 0)).comp 0 ht).sub_const _)
 rw [he,hh.fderiv]; unfold Slope Uniform.entry; rw [iteratedFDeriv_one_apply]; change fderiv ℝ T' p (lowerCol (agentX i (epsI G i.2)))=fderiv ℝ T' p (bolt (Sum.inr i)); rw [agent_b,lower_bolt]
end YM.CF.Char
