import GaugeFieldConstruction.HatchRT
/-!
 # Independence of contour. Establish for conservation + locality at SAME partial prices (CutCert). Borrow from analytic proofs Hesper.
-/
set_option autoImplicit false
set_option synthInstance.maxSize 15000
set_option maxHeartbeats 300000
set_option linter.unusedSimpArgs false
noncomputable section
namespace YM.NSF.Boundary
open YM.Boundary Mink Function Set Filter MeasureTheory Complex Finset Distribution Probe Surface
open scoped Topology BigOperators ContDiff InnerProductSpace NNReal ENNReal
variable {n:ℕ}(k:Fin n)
local notation "ιᵢ" => k.castSucc
local notation "ιⱼ" => k.succ
local notation "N_τ" => τNearRT k
local notation "K_μ" => κMoverRT k
lemma priceDiffRt (b:Test4)(f:Joint n)(i:Axis): DriftΛL (NSF.Points.direction ιᵢ i) (χTestRT k b f)= χTestRT k (DmoveRT i b) f :=by
 let K:=K_μ; let D:=NSF.Points.direction ιᵢ i; let H:=χTestRT k b
 ext1 x; obtain ⟨⟨v,w⟩,rfl⟩:=K.surjective x; rw[DriftΛKnownL]; change ((fderiv ℝ (H f) (K (v,w))) D =_)
 have hi: K (basis i,0)=D:=by
    rw [motionKnownRT]; ext1 a; cases a using Fin.succAboveCases ιᵢ <;> simp [addXRT,D,Points.direction,tDiffRT,k.castSucc.succAbove_ne]
 rw [← hi]; have hp:= ((H f).smooth 1).differentiable (by simp) (K (v,w))|>.hasFDerivAt
 let U(z:E4 × Points n):= b z.1*f z.2
 have he: ⇑(H f) ∘ K = U:= funext fun p=>priceIRT ..
 have hX:= hp.comp (v,w) (K.hasFDerivAt); rw [he] at hX
 have ha:= (b.smooth 1).differentiable (by simp) v|>.hasFDerivAt; have hg:= (f.smooth 1).differentiable (by simp) w|>.hasFDerivAt
 have hv:= (HasFDerivAt.comp (f:=Prod.fst) (v,w) ha hasFDerivAt_fst).mul (HasFDerivAt.comp (v,w) (f:=Prod.snd) hg hasFDerivAt_snd)
 have H':= hX.unique hv -- tune
 change (fderiv ℝ (H f) (K (v,w)) ∘L K.toContinuousLinearMap) (basis i,(0:Points n))= _; rw [H']
 simp only [add_apply, smul_apply, ContinuousLinearMap.comp_apply]; rw [priceIRT,DmoveRT,ΦsΛKnownL]; simp [mul_comm]
lemma switchNextRt : (N_τ).s ιᵢ=ιⱼ:=by simp[NearPair.s]
lemma switchNextRt' : (N_τ).s ιⱼ=ιᵢ:=by simp[NearPair.s]
lemma switchDirRT (i:Axis): (N_τ).switch (NSF.Points.direction ιᵢ i)= NSF.Points.direction ιⱼ i:=by
 ext1 w; rw [NearPair.switch_at]; by_cases p: w=ιⱼ
 · simp[p,switchNextRt',Points.direction]
 have h: (N_τ).s w≠ιᵢ:=fun s=> p ((N_τ).s.injective (s.trans (switchNextRt' k).symm)); simp [Points.direction,h,p,k.castSucc.succAbove_ne,PiLp.single_apply]
lemma ΔSwitchRT (i:Axis)(f:Joint (n+1)): along (N_τ).switch.toContinuousLinearEquiv (DriftΛL (NSF.Points.direction ιᵢ i) f)=DriftΛL (NSF.Points.direction ιⱼ i) (along (N_τ).switch.toContinuousLinearEquiv f):=by
 let A:=(N_τ).switch.toContinuousLinearEquiv; let u:=NSF.Points.direction ιᵢ i
 ext1 x; rw [along_at, DriftΛKnownL, DriftΛKnownL]; have H:=(((f.smooth 1).differentiable (by simp) (A x)).hasFDerivAt.comp x A.hasFDerivAt).fderiv
 change _=fderiv ℝ (f ∘ A) x _; rw [H, ContinuousLinearMap.comp_apply]; congr 1
 change u=A _; rw [← switchDirRT]; exact (show _=u from (N_τ).switch.symm_apply_apply u).symm
variable {G:Gauge}{L:Register G}{S:Table L}{Y:Surface S}{B:∀ i, Blanket i}{F:Waves S}{X:Y.Aurora B}
variable (T:Axis→Axis→ S.Union)(e:MintDΛ (X:=X) T) (p:X.FullBody F)(j:(B (n+1)).Modified)
variable (V:Fin n→ S.Union)(a:Axis)
local notation "Tx_" i => addXRT k V (T i a)
abbrev partialXRT {n:ℕ}(V:Fin n→ S.Union)(y:Points n):= (B n).partialD (Y.W n V) y
local notation "Ξy"=> partialXRT (Y:=Y) (B:=B)
include e p j
lemma reinsLaRt {y:Points (n+1)}(u:y∈shores (n+1))(w:(𝓝[fields (n+1)] y).NeBot)(V:Fin (n+1)→ S.Union)(k:Fin (n+1))(v:Joint (n+1))(q:HasCompactSupport ⇑v): (∑ i:Axis, (partialXRT (B:=B) (Y:=Y) (Function.update V k (T i a)) y (DriftΛL (NSF.Points.direction k i) v)))=0:= by
 let A(i:Axis):= Function.update V k (T i a); let H(z:Points (n+1)):=∑ i:Axis,(Ξy (A i) z (DriftΛL (NSF.Points.direction k i) v))
 change H y=0; have ht:Tendsto H (𝓝[fields (n+1)] y) (𝓝 (H y)):=by unfold H; exact tendsto_finsetSum _ fun i _=> ((B (n+1)).tends j _ _ y u).mono (warmer _)
 apply tendsto_nhds_unique ht; refine (Tendsto.congr' ?_ tendsto_const_nhds); filter_upwards [self_mem_nhdsWithin] with z hz
 let M(i:Axis):=X.emit (A i); let D(i:Axis):= NSF.Points.direction k i; let I (i:Axis)(x:Points (n+1)):= MintSpΛ (M i) (D i) (glow x z)*v x
 have hu(i:Axis): (Ξy (A i) z (DriftΛL (D i) v))= -(∫ x,I i x) :=by rw [show partialXRT (B:=B) (Y:=Y) _ z _=_ from p.builds _ (A i) z hz (DriftΛL _ v), show (∫ x,I i x)=_ from FeeΛSpL hz (M i) (p.hol _ _) v (D i) q, neg_neg] -- tune read
 unfold H; change 0=∑ i:Axis, Ξy (A i) z (DriftΛL (D i) v)
 simp_rw [hu]; rw[sum_neg_distrib,← integral_finsetSum _ fun i _ => MSteadyΛL hz (M i) (p.hol _ _) v _ q]; change 0= -(∫ x, ∑ i:Axis,I i x)
 have hp(x:Points (n+1)): (∑ i:Axis, I i x)=0:= by unfold I; rw [← sum_mul, show (∑ i:Axis,_)=_ from e _ V k a _ (roseΛ hz x), zero_mul]
 simp_rw [hp]; simp
#print axioms ΔSwitchRT
end YM.NSF.Boundary
end
