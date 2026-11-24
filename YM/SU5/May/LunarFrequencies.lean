import YM.SU5.May.FloeCoins
import YM.SU5.FiniteGaugeData.ArchiveK.Bourne
import YM.SU5.FiniteGaugeData.Crest.Alps
set_option autoImplicit false
set_option maxHeartbeats 500000
set_option maxRecDepth 3000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.May.Lunar
open Function Filter Finset Fir Lattice Laurent Next.Free Bloch Lat Ember Jill Rush
open scoped Topology BigOperators ContDiff InnerProductSpace Matrix MatrixOrder Kronecker Matrix.Norms.L2Operator Classical
attribute [local instance] opCStarAlgebra
open Onyx Fock SU
open Crest.Shore Floe Window.ArchiveK Window.Largo WithLp
variable (N:Side)(x:Cover)(q y:E4)(p:Momentum)
-- x+1/2 unwrapped centers. AP momenta
noncomputable def tune (N:Side):= 2*Real.pi/N.val
lemma tune_p : 0 < tune N:= by unfold tune; positivity
def apAt (l:Cover):E4:= toLp 2 fun i=>tune N*((l i:ℝ)+1/2)
lemma ap_fee (i:Axis): apAt N x i = tune N*((x i:ℝ)+1/2):=rfl
-- all include N from variable section.
private def chart (i:Per N):ℤ:= if Lat.winding i ≤ Real.pi then (i.val:ℤ) else (i.val:ℤ)-N.val
private lemma chart_id (i:Per N): (↑(chart N i):Per N)= i:=by unfold chart; split <;> simp
lemma chart_locus(k:Per N): Lat.principal k=tune N*((chart N k:ℝ)+1/2):=by
 unfold Lat.principal chart; split_ifs <;> push_cast <;> unfold tune Lat.winding <;> field_simp <;> ring
private def Unwrap (p:Site N×Cover) :Cover:=fun i=> chart N (p.1 i)+N.val * p.2 i
lemma localization (p:Site N×Cover): wrap N (Unwrap N p)=p.1:=by ext1 i; change (↑(chart ..+ _:ℤ):Per N)=_; simp [chart_id]; -- arg chart ..+ parsing?
lemma unwrap_in : Injective (Unwrap N):=by
 rintro ⟨i,j⟩ ⟨k,l⟩ h; have e: i=k:= (localization N (i,j)).symm.trans ((congrArg _ h).trans (localization N (k,l))); subst k; congr; ext1 a; exact mul_left_cancel₀ (show (↑N.val:ℤ)≠0 by positivity) (add_left_cancel (congrFun h a)) -- wrong cast
lemma unwrap_sur : Surjective (Unwrap N):=by
 intro l; let z:=wrap N l; have he(i:Axis): (↑N.val:ℤ) ∣ l i-chart N (z i):= by rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]; simp [z,chart_id,wrap] -- tune
 choose w u using he; refine ⟨(z,w),funext fun i=>?_⟩; unfold Unwrap; rw [show (↑N.val:ℤ)*w i=l i-chart N (z i) from (u i).symm]; abel
noncomputable def allAP : Site N×Cover≃Cover:= Equiv.ofBijective (Unwrap N) ⟨unwrap_in N,unwrap_sur N⟩
lemma ap_under(k:Site N)(l:Cover): apAt N (allAP N (k,l))=toLp 2 (pm k+stem l):=by
 apply PiLp.ext; intro i; rw [ap_fee]; change tune N*((↑(chart N (k i)+N.val*l i :ℤ):ℝ)+1/2)= Lat.principal (k i) + stem l i
 rw [chart_locus]; unfold tune stem; push_cast; field_simp; ring
lemma apat_neq : apAt N x≠0:=by
 intro t; have he: ((↑(x 0):ℝ)+1/2)=0:= (mul_eq_zero.mp (show tune N*((↑(x 0):ℝ)+1/2)=0 from congrArg (fun x:E4=>x 0) t)).resolve_left (tune_p N).ne'
 have hp:(↑(x 0):ℤ)*2+1=0:= by exact_mod_cast (show ((↑(x 0):ℝ)*2+1)=0 from by linarith)
 omega
lemma hReal: Bound Real.pi (pm (wrap N x)):= by
 exact (pi_norm_le_iff_of_nonneg Real.pi_pos.le).mpr fun i=> abs_le.mpr ⟨(pm_zone _ i).1.le,(pm_zone _ i).2⟩
lemma pmOK (k:Site N): Bound Real.pi (pm k):=by simpa only [wrap_lift] using hReal N (Lattice.lift k)
-- convergence pay
lemma sphereQ : leer (brushQ q)= Crest.Shore.weave q.ofLp:=by unfold leer Crest.Shore.weave; exact prod_congr rfl fun i _=> rustQ ..
lemma cSphere(u:Bin): (↑(radius u):ℂ)=pass (tmap u):=by unfold radius pass; push_cast; rfl
lemma prism(k:Site N)(l:Cover)(i:Axis): ironQ (apAt N (allAP N (k,l))) i= slat (pm k) l i:=by
 rw [ap_under]; unfold ironQ slat amiX; rw [sphereQ]; rw [cSphere]; rfl
-- define currency in components before merging
noncomputable def spectral (q y:E4):Momentum:= coastE (inner ℝ q y) • ironQ q
lemma spectrumPay(k:Site N)(l:Cover): spectral (apAt N (allAP N (k,l))) (emitX x)= mode (mel k) x • slat (pm k) l:=by
 unfold spectral; rw [← surfK]; have he: ironQ (apAt N (allAP N (k,l)))= slat (pm k) l:=funext (prism N k l)
 rw [he, ap_under, show brushQ _= mel k+reciprocal l from map_stem .., mode_phase, mode_periodic,mul_one] -- tune
noncomputable def poll:= ∑' l:Cover,spectral (apAt N l) (emitX x)
lemma gear(k:Site N): HasSum (fun l:Cover=> spectral (apAt N (allAP N (k,l))) (emitX x)) (mode (mel k) x • tough (pm k)):=by
 simp_rw [spectrumPay]; refine HasSum.const_smul _ ?_; refine Pi.hasSum.mpr (fun i=>(spending (pmOK N k) (pm_nonzero k) i).of_norm.hasSum) -- tune
lemma voter_sum : Summable (fun l:Cover=> spectral (apAt N l) (emitX x)):=by
 apply (allAP N).summable_iff.mp; apply Summable.of_norm; apply (summable_prod_of_nonneg (fun p=> norm_nonneg _)).mpr ?_
 exact ⟨(fun i=>(gear N x i).summable.norm), (hasSum_fintype _).summable⟩ -- tune
lemma voter_receipt : (∑ k:Site N, mode (mel k) x • tough (pm k))=poll N x:=by
 let q(p:Site N×Cover):=spectral (apAt N (allAP N p)) (emitX x); have he:Summable q:=(allAP N).summable_iff.mpr (voter_sum N x); unfold poll; rw [← (allAP N).tsum_eq]; change ∑ k:Site N, _=∑' p,q p; rw [he.tsum_prod' (fun i=>(gear N x i).summable),tsum_fintype]; exact sum_congr rfl fun i _=>(gear N x i).tsum_eq.symm
section
variable {X:Type*}{M:X→Jill.Male}{l:Filter X} (e:Tendsto (fun i=>(M i).val) l atTop)
include e
lemma fallMoney (k:Site N) (s t:SpinIdx): Tendsto (fun i=>wave 4 (M i) x s t (mel k)) l (𝓝 (lash (mode (mel k) x • tough (pm k)) s t)):=by
 unfold wave; simp_rw [dip_math]; rw [lash_s,Matrix.smul_apply]; let G(p:Peb):=p s t
 have hQ: Tendsto (fun i=>mixL 4 (M i).val (mel k)) l (𝓝 (tough (pm k))):= tendsto_pi_nhds.mpr fun i=>Crest.Shore.gulch e (F:=fun _=>mel k) tendsto_const_nhds (Eventually.of_forall (fun i=>(M i).property)) (pmOK N k) (pm_nonzero _) i (Eventually.of_forall fun _=> mel_h k)
 exact (((show Continuous (fun p:Peb=>G p) by unfold G; fun_prop).comp lashCL.continuous).continuousAt.tendsto.comp hQ).const_mul _
lemma apLimits (s t:SpinIdx): Tendsto (fun i=> delta N 4 (M i) 1 x s t) l (𝓝 (coins N 1*(lash (poll N x) s t))):=by
 unfold delta; apply Tendsto.const_mul; rw [← voter_receipt]; change Tendsto _ l (𝓝 ((lashCL (∑ k:Site N,_ : Momentum)) s t)); rw [map_sum,Matrix.sum_apply]; exact tendsto_finsetSum _ fun i _=> fallMoney N x e i s t
end
#print axioms voter_sum
#print axioms apLimits
end YM.CF.May.Lunar
