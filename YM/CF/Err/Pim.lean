import YM.CF.Err.Moire
set_option autoImplicit false
set_option maxHeartbeats 700000
noncomputable section
namespace YM.CF.Err
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open CF.Appel CF.Newt CF.Char CF.Neige CF.Summit Next Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Wisps Next.SectorChange.Schur MultiNext.SignedSource Lyre Banjo Analysis Pressure AnalyticBridge.MarginalMultiplier3b1d PatchReads SectorNext.Remainder SectorNext.Remainder.Scales Planned.AtomRegular Extra.Iteration Extra.Iteration.Scales
open Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix MatrixOrder Kronecker Classical Matrix.Norms.Frobenius
open AnalyticBridge.Annulus1AD Ac Esti
variable {G:Gauge}{c f:Side}{S:StepData c f}{r v l:ℕ}{w x β d:ℝ}{q:Chi}{T:Tube G S}
open CF.Forge
open AnalyticBridge.SectorAffine AnalyticBridge.SectorAffine.Offset Matrix
variable{A:Stores S}{F:Forest S.ratio}{V:Config G c}{k:S.Choices}{L:Teller G}
def indeX : LogArray G (Frozen A x F)→ₗ[ℝ] Directions G f where
 toFun:=Rows.input x A F
 map_add':=by intro a b; funext i; unfold Rows.input; split_ifs <;> simp_all
 map_smul':=by intro a b; funext i; unfold Rows.input; split_ifs <;> simp_all
abbrev lacG(x:ℝ)(q:Chi)(d:ℝ)(V:Config G c)(u:LinkArray G (Frozen A x F)):= tape.symm (autoShell q d V u)
lemma deltaF(h:L.Funds S T)(p:Config G c):∃ X: Prices G (Frozen A x F)→ₗ[ℝ] Prices G (Active A x F), ∀ U V, Offset.mean T x k A F q d U p- Offset.mean T x k A F q d V p=X (lacG x q d p U - lacG x q d p V):=by
 let M:= -(Schur.per (panels A F) (Rows.gram T x p k (shots S x) A F)).transpose; let B:= (Rows.move T x p k (shots S x) A F)ᵀ; let C:= allData T x A F k p
 let X₀:= M.mulVecLin ∘ₗ B.mulVecLin ∘ₗ C.mulVecLin; let X:= X₀ ∘ₗ colors.symm.toLinearMap ∘ₗ indeX (G:=G) (x:=x) (F:=F) (A:=A) ∘ₗ colors.toLinearMap
 -- needs all U simultaneously
 refine ⟨X,fun U V=>?_ ⟩; rw [map_sub]; unfold Offset.mean Offset.b; rw [f0_split _ _ _ _ _ _ h, f0_split _ _ _ _ _ _ h]; simp_rw [mulVec_add]; rw [add_sub_add_left_eq_sub]; rfl -- tune tape
lemma linQ(h:L.Funds S T) (v:l≤18)(hg:Ready T x) (V:Config G c):∃ Q: Prices G (Frozen A x F)→ₗ[ℝ] Prices G (Active A x F),∀ U W,liftN T x V k A F q d U l-liftN T x V k A F q d W l= Q (lacG x q d V U-lacG x q d V W):=by
 obtain ⟨Z,hZ⟩:=deltaF (q:=q) (d:=d) (k:=k) (A:=A)  (F:=F) (x:=x) h V
 let Q: Prices G (Active A x F)→ₗ[ℝ] Prices G (Active A x F):=LinearMap.pi fun i=>if green x S A i.1.val.val then 0 else LinearMap.proj i
 refine ⟨Q.comp Z,fun U W=>?_⟩; rw [LinearMap.comp_apply,←hZ U W]; ext1 i; unfold Q; rw [LinearMap.pi_apply,Pi.sub_apply]; split; next he=> rw [stance (Z:=W) hg v he,sub_self,LinearMap.zero_apply]
 next p=> simp only [liftN,if_neg p]; rfl
lemma atlasX(p:Config G c)(u:LogArray G (Frozen A x F))(hd:0<d)(hr:d<firstRadius G)(hl:‖u‖≤d)(q:Chi): ∃ Y:LinkArray G (Frozen A x F), lacG x q d p Y= tape.symm u:=by
 let z(x:Frozen A x F):= replica S.ratio p x.val.val; refine ⟨fun i=> G.lieExp (u i)*z i,?_⟩; unfold lacG; congr 1; funext i; unfold autoShell z; rw [mul_inv_cancel_right,patched_agrees _ hd hr ((norm_le_pi_norm u i).trans hl)]
lemma ownsY(p: Config G c)(hd:0<d)(hr:d<firstRadius G) (q:Chi):∃ o_:LinkArray G (Frozen A x F),∃ a: (Frozen A x F ×G.ColorIndex) → LinkArray G (Frozen A x F), IsUnit (Matrix.of (fun i j=> lacG x q d p (a j) i-lacG x q d p o_ i)):=by
 let I:=Frozen A x F ×G.ColorIndex; let L(y):=lacG x q d p y (A:=A) (F:=F)
 obtain ⟨o,h⟩:= atlasX (A:=A)  (F:=F) (x:=x) p 0 hd hr (by simp [hd.le]) q
 have he(i:I):∃ w:ℝ,∃ j:LinkArray G (Frozen A x F),0 < w∧ L j=w • Pi.single i 1:=by
    let V: Prices G (Frozen A x F):= Pi.single i 1; let t:=‖colors V‖; let w:=d/(t+1); have hp:0 ≤ t:= norm_nonneg _; have hw:0<w:=by unfold w; positivity
    have hv:‖colors (w • V)‖ ≤ d:=by rw [map_smul,norm_smul,Real.norm_of_nonneg hw.le]; apply le_trans (mul_le_mul_of_nonneg_left (show ‖colors V‖ ≤ t+1 from le_add_of_nonneg_right zero_le_one) hw.le); exact le_of_eq (div_mul_cancel₀ _ ((by linarith : 0 < t+1).ne'))
    obtain ⟨j,h⟩:=atlasX p _ hd hr hv q; exact ⟨w,j,hw,h.trans (tape.symm_apply_apply _)⟩
 choose w f hp hr using he; refine ⟨o,f,?_⟩; change IsUnit (Matrix.of (fun i j=> L (f j) i-L o i)); rw [show L o=0 from h.trans (show tape.symm _= _ from map_zero colors.symm)]; rw [show Matrix.of (fun i j=> L (f j) i-(0:Prices G (Frozen A x F)) i)= diagonal w from ?_]; apply Matrix.isUnit_iff_isUnit_det .. |>.2; rw [Matrix.det_diagonal]; exact (isUnit_iff_ne_zero.mpr (Finset.prod_pos (fun i _=>hp i)).ne') -- tune
 ext i j; by_cases q:i=j; subst j; simp [hr]; simp [hr,q, Ne.symm q, diagonal_apply]
end YM.CF.Err
