import YM.CF.Neige.Wit
import YM.AnalyticBridge.ANNULUS_GAUSSIAN_INTERFACE_1AD.Payment
import YM.SectorNext.GAUSSIAN_SECTOR_CHANGE.Stamped
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
-- prices on affine center shift & gradient remainder
lemma parcels (U: Config G c→α→ℝ)(h:Offset.Parcel 0 p d n (U ∘ Offset.pulse x V) C)(hC:0≤C)(hd:0<d) (hs:0<temp x): Allows n (U ∘ Vmove x V) 0 (activation G n 0 d*C):=by
 obtain ⟨hm,hv⟩:=Offset.stipulation (H:=U) (h:=0) h hd hs hC
 let L:= temp x • ContinuousLinearMap.id ℝ (Directions G c)
 have hp: (U ∘ Vmove x V)= (U ∘ increment V) ∘ L:=rfl
 rw [hp]; let t:= activation G n 0 d*C; have ht:0 ≤ t:=mul_nonneg (zero_le_one.trans (activation_one G n 0 hd)) hC
 let f:=U ∘ increment V; have hh:ContDiffAt ℝ n f (L 0):= (map_zero L).symm ▸ hm
 refine ⟨hh.comp _ L.contDiff.contDiffAt, fun i hi => Planned.AtomRegular.op_le_of_unit ht fun b hb=>?_⟩
 change ‖iteratedFDeriv ℝ i (f ∘ L) _ b‖ ≤ _
 rw [Push.Uniform.iter_lin_at (hh.of_le (by exact_mod_cast hi)),ContinuousMultilinearMap.compContinuousLinearMap_apply,map_zero]; apply (pi_norm_le_iff_of_nonneg ht).mpr; intro j
 let b'(i):= L (b i)
 have he:Afford (temp x) 0 0 (List.ofFn b'):=by
    rw [Afford,List.forall_mem_ofFn_iff]; intro u i; change ‖temp x • b u i‖  ≤ _; rw [norm_smul,Real.norm_of_nonneg hs.le]; simp [FreeResolvent.Mark.hill]; exact mul_le_of_le_one_right hs.le ((norm_le_pi_norm ..).trans (hb u))
 have hp' := hv 0 (List.ofFn b') (List.length_ofFn.trans_le hi) he j
 simp only [pow_zero,one_pow, inv_one,one_mul,FreeResolvent.Stars.list_result,id_comp] at hp'
 exact hp'
variable {q:Chi}{D D' D'' θ γ m δ a u:ℝ}
lemma stepsA (H:Offset.Shift n x d v a D T F A V k q)(Y:LinkArray G (Frozen A x F))(hp:0 ≤ D)(hx:0<temp x)(hd:0<d):
   let C:=activation G n 0 d*D
   let g:=fiery G x S.patch.L
   (Offset.b T x k A F q a Y V=Rows.blame T x V k (shots S x) A F q a Y ∧ Offset.mean T x k A F q a Y V=meanLog A F T x V k q a Y)∧
    Allows n (Offset.mean T x k A F q a Y ∘ Vmove x V) 0 (C*g) ∧
    Allows n (Offset.residual T x k A F q a Y ∘ Vmove x V) 0 (C*g*Real.exp (-v*radiusB x)):=by
 intro C g; obtain ⟨hm,hp',-⟩:=Offset.reads_actual T x k A F q a Y V (congr_fun H.okay Y); obtain ⟨_,ht,hH⟩:= H.steps Y; have hg:0≤g:= temp_nonneg _
 refine ⟨⟨hm,hp'⟩, (parcels _ ht (mul_nonneg hp hg) hd hx).mono (le_of_eq (by unfold g C; ring)), (parcels _ hH (mul_nonneg (mul_nonneg hp hg) (by positivity)) hd hx).mono (le_of_eq (by unfold g C;ring))⟩
-- actual Hess mismatch for cost. actual source ζ residual Ext. algebra orientation later
abbrev bankG(T:Tube G S)(A:Stores S)(F:Forest S.ratio)(k:S.Choices)(q:Chi)(d x:ℝ)(Y:LinkArray G (Frozen A x F))(l:ℕ)(V:Config G c):= Rows.gram T x V k (shots S x) A F *ᵥ liftN T x V k A F q d Y l+Offset.b T x k A F q d Y V
def credW(T:Tube G S)(A:Stores S)(F:Forest S.ratio)(k:S.Choices)(q:Chi)(d x:ℝ)(Y:LinkArray G (Frozen A x F))(l:ℕ)(V:Config G c):= layX T x A F k q d Y l V
abbrev Dira(T:Tube G S)(A:Stores S)(F:Forest S.ratio)(k:S.Choices)(q:Chi)(d x:ℝ)(Y:LinkArray G (Frozen A x F))(l:ℕ)(V:Config G c):= (credW T A F k q d x Y l V).transpose *ᵥ bankG T A F k q d x Y l V
abbrev fullV(T:Tube G S)(A:Stores S)(F:Forest S.ratio)(k:S.Choices)(q:Chi)(d x:ℝ)(Y:LinkArray G (Frozen A x F))(l:ℕ)(V:Config G c):= perturb (credW T A F k q d x Y l V) (baseX T x A F k V)
lemma cigar (H:Offset.Shift n x d v a D T F A V k q)(hp:0≤D)(hx:0<temp x)(hd:0<d)(K:Teller G)
 (hc:Cert P K S T x)(hf:A.flags=RG.flags (temp x) V)(hh:sizedP G P K S T F)(ht:shirt G K P x C u n l)(hs:ShardIncome n x θ δ m T A F V k)(hρ:Loom n x D' V T F A Y k q a l):
 let g:=fiery G x S.patch.L
 let N:=activation G n 0 d*D
 let E:=N*g*Real.exp (-v*radiusB x)+2^n*δ*(C*u^2)
 (Offset.b T x k A F q a Y V= Rows.blame T x V k (shots S x) A F q a Y ∧ Offset.mean T x k A F q a Y V=meanLog A F T x V k q a Y) ∧
 Allows n (fun y=>liftN T x (Vmove x V y) k A F q a Y l) 0 (N*g+C*u^2) ∧
 Allows n (bankG T A F k q a x Y l ∘ Vmove x V) 0 E ∧
 Allows n (Dira T A F k q a x Y l ∘ Vmove x V) 0 (2^n*D'*E) ∧
 Protected n (credW T A F k q a x Y l ∘ Vmove x V) 0 D' ∧ Protected n (fullV T A F k q a x Y l ∘ Vmove x V) 0 (D'*lamp x):=by
 intro g N E; obtain ⟨hm,hv,hX⟩:= stepsA H Y hp hx hd; obtain ⟨hl,hn,ht⟩:=ht.2.2.2 S T A F hc hh V hf k q a Y
 have hP: Allows n (bankG T A F k q a x Y l ∘ Vmove x V) 0 E := by
    apply (hX.add (appliance hs.kernel hn)).germ; refine Eventually.of_forall fun y=> ?_
    change Offset.residual T x k A F q a Y _+_*ᵥ cot _ _ _ _ _ _ _ _ _ _= _*ᵥ _+_; unfold Offset.residual cot; rw [Matrix.mulVec_sub]; dsimp only [Function.comp_apply,baseX]; abel
 refine ⟨hm,(hv.add hn).germ (Eventually.of_forall fun i=>?_), hP, appliance hρ.back hP,hρ.link,hρ.errorH⟩
 dsimp only [Function.comp_apply,cot]; abel -- comp etc
end YM.CF.Appel
