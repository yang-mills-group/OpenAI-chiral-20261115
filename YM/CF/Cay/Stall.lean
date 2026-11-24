import YM.CF.Cay.Coil
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
section
variable {X:Support c}
lemma subX_s (p:Ready T x)(ht:1000 ≤ radiusB x)(i:Receipt SU.group S)(h:Beat.shadows (o:=down S i) X (horn x l)): Virt S (subX T x q d l β i) X:=by
 intro M N u; unfold subX; suffices e :∀ t:Bool,tunic T x q d l β M t i=tunic T x q d l β N t i by simp_rw [e]
 intro a; cases a
 · refine rimP (q:=q) (d:=d) u p ht i (aroundBk X h (by unfold horn; simp_rw [Nat.add_mul,separation_self]; omega)) (fun j j' k a=> ?_); exact liftN_read (A:=M.key) (F:=M.park) (F':=N.park) (A':=N.key) p (u.scope (r:=(l+41)*radiusB x) (b:=(l+62)*radiusB x) (by simp_rw [Nat.add_mul]; omega) (aroundBk X h (by unfold horn; simp_rw [Nat.add_mul]; omega))) k
 · exact rimP (q:=q) (d:=d) u p ht i (aroundBk X h (by unfold horn; simp_rw [Nat.add_mul,separation_self]; omega)) (fun j j' k t=> u.reaction p ht k (aroundBk X h (by unfold horn; simp_rw [Nat.add_mul]; omega)))
lemma rivet(T:Tube G S)(x:ℝ)(q:Chi)(d:ℝ)(l:ℕ)(β:ℝ)(h:0<β)(M:ζ): ContDiff ℝ ω (adjust T x q d l β ∘ rough M):=by
 rw [basedP _ _ _ _ _ _ h]; exact (laySq (wrench M x) M.z 0).1.add (ContDiff.sum (s:=univ) (f:=fun i=> subX T x q d l β i∘ rough M) fun i _=>subX_p _ _ _ _ _ _ i M)
lemma settle (e:Bond f)(M:ζ)(x:ℝ)(q:Chi): let Q:=wrench M x; let P(i):=flog q i x; spring P e M= (Q (arrow e M.z) ⬝ᵥ Q M.z)/2:=by
 intro Q P; obtain ⟨h,hp,ht⟩:= laySq Q M.z (arrow e M.z); unfold spring; let V:=fun i=>(Q i ⬝ᵥ Q i)/2; change fderiv ℝ V 0 _+hdot V _ _ _/2=_; rw [show fderiv ℝ V 0=0 from hp,_root_.zero_apply,ht,zero_add]
lemma cog (e:Bond f)(p:Beat.shadows (o:=S.ratio.parent e.1) X (2*horn x l))(hr:Ready T x)(hv:1000 ≤ radiusB x)(ht:0<β): Virt S (spring (adjust T x q d l β) e) X:=by
 intro M N u; let g(Q:ζ):= adjust T x q d l β Q; let A(Q:ζ):= (wrench Q x (arrow e Q.z) ⬝ᵥ wrench Q x Q.z)/2
 have he(R:ζ): spring g e R=A R+∑ i,spring (subX T x q d l β i) e R:=by
    let P(t:ζ):= flog q t x; let B:=P ∘ rough R; let z:=arrow e R.z; unfold g; rw [basedP _ _ _ _ _ _ ht,show A R= spring P e R from (settle e R x q).symm]; change strut (fun x'=>B x'+∑ i,(subX T x q d l β i ∘ rough R) x') z R.z=strut B z R.z+_; have hp (i:Receipt SU.group S):ContDiffAt ℝ (2:ℕ) (subX T x q d l β i∘ rough R) 0:= (subX_p _ _ _ _ _ _ i R).contDiffAt.of_le le_top
    rw [strut_add B _ _ _ ((laySq (wrench R x) z R.z).1.contDiffAt.of_le le_top) (ContDiffAt.sum (fun i _=>hp i)),strut_sum (Y:=fun i=>subX T x q d l β i∘ rough R) _ _ _ (fun i _=> hp i)]; rfl
 change spring g e M=spring g e N; rw [he,he]; refine congrArg₂ (·+·) ?_ (sum_congr rfl fun i _=> ?_);
 · let o:=S.ratio.parent e.1; let r:=radiusB x
   let Y:= wrench M x (arrow e M.z); let W:= wrench N x (arrow e N.z); have hw:=u.scope (r:=0) (x:=x) (by unfold horn; simp_rw [Nat.add_mul,mul_add]; omega) p
   unfold A; congr 1; unfold dotProduct; refine PatchReads.sum_eq (o:=o) (A:=M.key) (F:=M.park) (A':=N.key) (F':=N.park) hw (fun i w=>?_) (fun i w=>?_ ) fun i j l' ht=> ?_
   · rw [show wrench M x _ i=0 from ?_,zero_mul]; change arrow e M.z i.1.val.val i.2=0; rw [arrow,Pi.single_eq_of_ne]; rfl; intro t; change 0 < separation o (S.ratio.parent i.1.val.val.1) at w; rw [t,separation_self] at w; omega
   · rw [show wrench N x _ i=0 from ?_,zero_mul]; change arrow e N.z i.1.val.val i.2=0; rw [arrow,Pi.single_eq_of_ne]; rfl; intro t; change 0 < separation o (S.ratio.parent i.1.val.val.1) at w; rw [t,separation_self] at w; omega
   have ht':i.1.val.val=j.1.val.val:= congrArg Prod.fst ht
   have hh:N.z e=M.z e:= (u.color _ (u.outC p (r:=0) (by unfold horn; simp_rw [Nat.add_mul,mul_add]; omega) (by simp))).symm
   change arrow e M.z i.1.val.val i.2*M.z i.1.val.val i.2= arrow e N.z j.1.val.val j.2*N.z j.1.val.val j.2
   unfold arrow; rw [hh,u.color _ (u.outC p (r:=0) (by unfold horn; simp_rw [Nat.add_mul,mul_add]; omega) l'),ht', show i.2=j.2 from congrArg Prod.snd ht]
 exact curt e (r:=horn x l) (subX_s hr hv i (show Beat.shadows (o:=down S i) _ (horn x l) from Subset.refl _)) p u
end
end YM.CF.Cay
