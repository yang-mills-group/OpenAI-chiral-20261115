import YM.CF.Cay.See
set_option autoImplicit false
set_option maxHeartbeats 700000
noncomputable section
namespace YM.CF.Cay
open Slate Forge Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open CF.Appel CF.Newt CF.Char CF.Neige CF.Summit Next Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Wisps Next.SectorChange.Schur MultiNext.SignedSource Lyre Banjo Analysis Pressure AnalyticBridge.MarginalMultiplier3b1d PatchReads SectorNext.Remainder SectorNext.Remainder.Scales Planned.AtomRegular Extra.Iteration Extra.Iteration.Scales
open Push.Uniform (curve Slope tint partSpace meetVar)
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix MatrixOrder Kronecker Classical Matrix.Norms.Frobenius
open AnalyticBridge.Annulus1AD AnalyticBridge.SectorAffine Oriented Esti Vol Bloch Exterior Jet
variable {G:Gauge}{c f:Side}{S:StepData c f}{r v l n:ℕ}{w x β d:ℝ}{q:Chi}{T:Tube G S}{F:Forest S.ratio}{E A:Type}[NormedAddCommGroup E][NormedSpace ℝ E][NormedAddCommGroup A][NormedSpace ℝ A]
local notation "G"=>SU.group
variable {K:Teller SU.group}{T:Tube SU.group S}
local notation "ζ"=>Monk G S
open Matrix
abbrev wrench(M:ζ)(x:ℝ): Directions G f→L[ℝ] Prices G (M.zoo x):= (tint G _).symm.toContinuousLinearMap.comp (ContinuousLinearMap.pi fun i: M.zoo x=>ContinuousLinearMap.proj (φ:=fun _=> SU.group.Color) i.val.val)
def strut (Y:E→ℝ)(p v:E):= fderiv ℝ Y 0 p+ hdot Y 0 v p/2
lemma strut_add (Y H:E→ℝ)(p v:E)(h:ContDiffAt ℝ (2:ℕ) Y 0)(hu:ContDiffAt ℝ (2:ℕ) H 0):strut (fun i=>Y i+ H i) p v=strut Y p v+ strut H p v:=by
 have he(f:E→ℝ):strut f p v= iteratedFDeriv ℝ 1 f 0 ![p]+ iteratedFDeriv ℝ 2 f 0 ![v,p]/2:=by unfold strut; rw [iteratedFDeriv_two_apply,iteratedFDeriv_one_apply]; rfl
 change strut (Y+H) p v=_; rw [he,he Y,he H,iteratedFDeriv_add_apply h hu,iteratedFDeriv_add_apply (h.of_le (by norm_num)) (hu.of_le (by norm_num))]; rw [_root_.add_apply, _root_.add_apply]; ring
lemma strut_const (Y:E→ℝ)(p v:E)(h:ContDiffAt ℝ (2:ℕ) Y 0)(r:ℝ):strut (fun i=>r*Y i) p v=r*strut Y p v:=by
 have he(f:E→ℝ):strut f p v= iteratedFDeriv ℝ 1 f 0 ![p]+ iteratedFDeriv ℝ 2 f 0 ![v,p]/2:=by unfold strut; rw [iteratedFDeriv_two_apply,iteratedFDeriv_one_apply]; rfl
 change strut (r • Y) _ _=_; rw [he,he Y,iteratedFDeriv_const_smul_apply h,iteratedFDeriv_const_smul_apply (h.of_le (by norm_num)),_root_.smul_apply,_root_.smul_apply,smul_eq_mul,smul_eq_mul]; ring
lemma strut_sum {ι:Type}(X:Finset ι)(Y:ι→E→ℝ)(p v:E)(h:∀ i∈X, ContDiffAt ℝ (2:ℕ) (Y i) 0): strut (fun x=>∑ i∈ X,Y i x) p v=∑ i∈X,strut (Y i) p v:=by
 induction X using Finset.induction with
 | empty=> simp only [sum_empty,strut,hdot]; simp
 | @insert i t e ih=>simp_rw [sum_insert e]; have hx:=fun a p=> h a (mem_insert_of_mem p); rw [strut_add (Y i) _ _ _ (h _ (mem_insert_self ..)) (ContDiffAt.sum hx), ih hx] -- tune
open Souk (μ₁)
section
variable(T:Tube G S)(x:ℝ)(q:Chi)(d:ℝ)(l:ℕ)(β:ℝ)
def adjust(M:ζ):=sepB T x M q d l β+sepQ T x M q d l
variable {T} in
abbrev tunic(T:Tube G S)(x:ℝ)(q:Chi)(d:ℝ)(l:ℕ)(β:ℝ)(M:ζ)(p:Bool) : Prices G (Slots S):= let μ:= liftN T x M.V M.k M.key M.park q d (M.bush x) l; axle M.key M.park T x M.k q d (M.bush x) (if p then M.fuel x T q d l β else μ) M.V
def subX(T:Tube G S)(x:ℝ)(q:Chi)(d:ℝ)(l:ℕ)(β:ℝ)(i: Slots S×SU.group.ColorIndex)(M:ζ):=-β*(tunic T x q d l β M true i)^2/2+β*(tunic T x q d l β M false i)^2/2
def flog(q:Chi)(M:ζ)(x:ℝ):= (wrench M x M.z ⬝ᵥ wrench M x M.z)/2
lemma basedP(h:0<β): adjust T x q d l β=(fun M=> flog q M x+∑ i,subX T x q d l β i M):=by
 funext M; have he:=trim T x M q d l β h; unfold subX adjust; dsimp only [tunic]; simp only [Bool.false_eq_true,↓reduceIte, if_true]; rw [sum_add_distrib, ← sum_div,← sum_div, ← mul_sum,← mul_sum]; unfold dotProduct at he; simp_rw [pow_two]; rw [show flog q M x=costU (M.bell x)/2 from rfl,← he]; ring
lemma subX_p(i:Receipt SU.group S)(M:ζ): ContDiff ℝ ω (subX T x q d l β i ∘ rough M):=by
 let R(v:Directions G f):= tunic T x q d l β (rough M v) true
 let K:= credW T M.key M.park M.k q d x (M.bush x) l M.V; let U:= (paintO K).comp (wrench M x); let P:=M.park; let z:= liftN T x M.V M.k M.key M.park q d (M.bush x) l; let y:= ranQ (Rows.move T x M.V M.k (shots S x) M.key P); let W(v:Directions G f):=z+coupling β • U v
 have hv:ContDiff ℝ ω W:=contDiff_const.add (U.contDiff.const_smul _); have he:ContDiff ℝ ω R:= (y.contDiff.comp hv).add (contDiff_const (c:=Offset.f0 T x M.key P M.k M.V q d (M.bush x))) -- tune
 let J:= ContinuousLinearMap.proj (R:=ℝ) (φ:=fun _:Receipt SU.group S=>ℝ) i; have htX:ContDiff ℝ ω (J ∘ R):=J.contDiff.comp he; -- use powers
 exact (((contDiff_const (c:=-β)).mul (htX.pow 2)).div_const 2 |>.add (contDiff_const (c:=β*(tunic T x q d l β M false i)^2/2)))
end
end YM.CF.Cay
