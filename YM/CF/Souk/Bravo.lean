import YM.CF.Souk.Mire
/-! Trace-delta norms for true thermal. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.Souk
open Function Filter Set Matrix Lattice Wilson RG Precision Pressure Tree Exterior MeasureTheory Metric
 AnalyticBridge.MarginalMultiplier3b1d AnalyticBridge.LocalGaussianLaws AnalyticBridge.SectorAffine Char Jet Newt Hors Neige
open Push.SectorMeasure AnalyticBridge.RelativeLogdet.Ink
open Push
open Push.Uniform (curve Slope meetVar Positions upperCol lowerCol block meet_derivative bolt address Primary tint Multiplicity countCost)
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius InnerProductSpace
variable {P:RG.Patch}{G:Gauge}{c f:Side}{S:StepData c f}{T:Tube G S}{K:Teller G}{F:Forest S.ratio}{X E B:Type}[NormedAddCommGroup E][NormedSpace ℝ E][NormedAddCommGroup B][NormedSpace ℝ B]{t x s D A C Q V r:ℝ}{i n l:ℕ}
variable {ι τ:Type} [Fintype ι][Fintype τ] [DecidableEq τ]
open Planned.JetPort
open Next.SectorChange PatchReads Next.SectorChange.Wisps PhysicalNext.JointLoad
variable {k: S.Choices}{q:Chi}
private lemma usesX (A: Stores S)(F:Forest S.ratio)(Y : LinkArray G (Frozen A x F))(hr:Ready T x)(hp:1000 ≤radiusB x)(k: S.Choices)(l:ℕ)(v u:Config G c): Sample k v Y ((l+52)*radiusB x) (Neige.fareX T x A F k q D Y l v) k u Y (Neige.fareX T x A F k q D Y l u):=by
 let H:=layX T x A F k q D Y l; let L:=radiusB x; let M(y):=majorX T x A F k q D Y l y; have ht(t):=supportH (l:=l) (A:=A) (F:=F) (V:=t) (Y:=Y) (k:=k) (q:=q) (D:=D) hr hp -- tune
 have hU:Sample k v Y ((l+48)*L) (H v) k u Y (H u):=layPt hr hp
 have hx:Sample k v Y ((l+49)*L) (H v).transpose k u Y (H u).transpose:=by
    intro i j m n S p s; rw [Matrix.transpose_apply,Matrix.transpose_apply]; by_cases he:separation (front A F i) (front A F m) ≤ L
    · exact hU _ _ _ _ (S.shrink (by simp_rw [Nat.add_mul]; omega)) s p
    rw [show H v _ _=0 from (ht v).rank m i (by rw [separation_comm]; exact lt_of_not_ge he),show H u _ _=0 from (ht u).rank n j (by rw [separation_comm,← faces p,←faces s]; exact lt_of_not_ge he)]
 have hg: Sample k v Y ((l+42)*L) (M v) k u Y (M u):=fun i i' j j' h hi hj=> Char.hessN_read hr h hi hj hp
 have hv(t):Names (M t) L:=⟨fun i j h=> hessN_off hr (fun hh=> by have h':separation (front A F i) (front A F j) ≤ L/20:=ball_member hh; omega) hp l⟩
 exact (tile_mul (tile_mul hx hg (ht v).turnt (ht u).turnt (b:=(l+49)*L) (by simp_rw [Nat.add_mul]; omega)) hU ((ht v).turnt.maps (hv v)) ((ht u).turnt.maps (hv u)) (by unfold L; simp_rw [Nat.add_mul]; omega)).less stone_s
lemma π_apply (u:Mast G c) : let H:=bareStores S
 let P:=lathe x s F (Neige.fareX T x H F k q D 1 l)
 let X:=μ₁ T F x k q D s l; let U:=ζ₁ T F x k q D s l
 P u=(X u).transpose * U u * X u - 1:=by
 intro Y P X U; let V:=facadeX G (s • u); let M:=layX T x Y F k q D 1 l V; let B:= pageX (G:=G) F x; let G':=majorX T x Y F k q D 1 l V
 change (M.transpose *G'*M -1).submatrix B B = (M.submatrix B B).transpose*(G'.submatrix B B)*(M.submatrix B B)-1 -- instance issues
 rw [Matrix.submatrix_sub,Pi.sub_apply, Pi.sub_apply,Matrix.submatrix_one_equiv]; change _=M.transpose.submatrix B B*(G'.submatrix B B)*(M.submatrix B B) - _; rw [Matrix.submatrix_mul_equiv,Matrix.submatrix_mul_equiv]
lemma reel_B (hr:Ready T x)(hp:1000≤ radiusB x)(h:Loom 2 x C (1:Config G c) T F (bareStores S) 1 k q D l):
 let Z:=μ₁ T F x k q D (temp x) l; let W:=ζ₁ T F x k q D (temp x) l
 let M:=fun i:Mast G c=> (Z i).transpose*W i* Z i- 1
 let t:=lamp x^3; let L:=composeCost 2 C (Uniform.shade G); let B:=raised G S.patch.L ((l+52)*radiusB x)
 Jewel Z 0 L (B*L) ∧ Jewel M 0 (L*t) (B*(L*t)):=by
 intro Z W M t L B
 let Y:=bareStores S; let H:= layX T x Y F k q D 1 l; have ht: Z= lathe x (temp x) F H:= rfl
 have hz:Protected 2 Z 0 L:=can_tags h.link; have hu: Protected 2 (fun x=> (Z x).transpose) 0 L:= can_tags (X:=fun y=>(H y).transpose) h.back
 let P:= Neige.fareX T x Y F k q D 1 l; let F':=lathe x (temp x) F P; have hf:M=F':= (funext (fun y:Mast G c=> π_apply (s:=temp x) (k:=k) (q:=q) (l:=l) (D:=D) (x:=x) y)).symm -- tune
 have hs:Protected 2 F' 0 (L*t):= (can_tags h.errorX).mono (Eq.le (by unfold L t Jet.composeCost; ring))
 refine ⟨⟨hz,hu,fun i hi j=> tileBill hr (X:=H) (s:=temp x) (fun y z=> (layPt hr hp (k:=k) (k':=k) (Y:= (1:LinkArray G (Frozen Y x F))) (Y':=(1:LinkArray G (Frozen Y x F)))).more (show (l+48)*radiusB x ≤ (l+52)*radiusB x from Nat.mul_le_mul_right _ (by omega))) (n:=i) (hz.order (by omega)) j⟩,hf ▸ ⟨hs,hs.germ ?_,fun i hi j=> tileBill hr (k:=k) (X:=P) (s:=temp x) (fun _ _=> usesX Y F 1 hr hp k l _ _) (hs.order (by omega)) j⟩⟩
 filter_upwards with y; rw [←hf]; apply congrArg paintO; unfold M; have hh:(W y).transpose=W y:=by unfold W ζ₁; rw [transpose_submatrix,(Char.sym_hessN l).eq]
 rw [Matrix.transpose_sub,Matrix.transpose_mul, Matrix.transpose_mul,transpose_transpose, Matrix.transpose_one, hh, Matrix.mul_assoc]
lemma gold_B {X Y: Fish ι→Neige.Shelf τ}{x:Fish ι}(hf: Jewel X x C Q)(hu:A≥C)(hp:V≥Q) (hv:X=ᶠ[𝓝 x] Y): Jewel Y x A V:=by
 refine ⟨((hf.upper.germ ?_).mono hu),((hf.turn.germ ?_).mono hu),fun i hi v=> ?_⟩
 · exact hv.mono fun y he=> congrArg paintO he
 · exact hv.mono fun y he=>by dsimp only; rw [he]
 unfold pS Uniform.entry; rw [← (hv.iteratedFDeriv ℝ (i+1)).eq_of_nhds]; exact (hf.cents _ hi v).trans hp
end YM.CF.Souk
