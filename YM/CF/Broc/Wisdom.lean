import YM.CF.Broc.Loci
/-! Local real trace pickup. -/
set_option autoImplicit false
set_option synthInstance.maxSize 8000
noncomputable section
namespace YM.CF.Broc
open Function Filter Lattice Metric Lat Finset Tenant Branch Fock Dial MeasureTheory Paige Phase Phase.Sample Brace Cube Peaks Tulip Rush Drapes
open scoped Topology Matrix BigOperators Matrix.Norms.L2Operator InnerProductSpace
attribute [local instance] opCStarAlgebra
variable {N P:Side}(G: Ratio N P)
abbrev Loom {N P: Side}(G: Ratio N P)(e:ℝ):= {x:Sew N P|Gild G x e}
def weave(e:ℝ):Light (Site (More P)) ↥(Loom G e) (Fend P→SU.E) where
 frame:= terr _
 rel T x y:= Agrees T x.val.1.1 y.val.1.1 ∧ Agrees (cloudG G T) x.val.1.2 y.val.1.2 ∧ AgreeF T x.val.2.1 y.val.2.1 ∧ AgreeF (cloudG G T) x.val.2.2 y.val.2.2
 expands _ _ h x y p:= ⟨fun i a b=>p.1 i (h a) (h b), fun i a b=>p.2.1 i ((cloud_grows G h) a) ((cloud_grows G h) b), p.2.2.1.less h,p.2.2.2.less (cloud_grows G h)⟩
 dress t x:=⟨frost G t x.val,solid G t x.property⟩
lemma green0(x y:Bkg N)(S:Seal (Site N))(g:Agrees S x y): fare S (profile x) (profile y)=0 :=by
  apply sum_eq_zero; intro i hi; have he:= g i (mem_filter.mp hi).2.1 (mem_filter.mp hi).2.2; rw [show profile x i= profile y i by funext b; simp [profile,he],sub_self,norm_zero]
lemma paid_zero(e:ℝ)(x y:Loom G e)(S:Seal (Site (More P)))(h:(weave G e).rel S x y): bookK G (post x.val) (post y.val) S=0:=by
  unfold bookK deal post unionP; simp only [green0 _ _ _ h.1, green0 _ _ _ h.2.1,zero_add];
  have he {N:Side} (x y:Stun N)(S:Seal (Site (More N)))(h: AgreeF S x y):∑ i∈S,‖palt x i-palt y i‖ =0:=by
    apply sum_eq_zero; intro i hi; unfold palt hook; rw [h i hi,sub_self,norm_zero]
  rw [he _ _ _ h.2.2.1,he _ _ _ h.2.2.2,zero_add]

def quartzK(a K:ℝ):ℝ:= (∑' i:ℕ, Real.exp (-a/2*i)*(quota*((i:ℝ)+1)^4))*K
lemma qp(a K:ℝ)(h:0≤K):0≤quartzK a K:=mul_nonneg (tsum_nonneg (fun i=>mul_nonneg (Real.exp_pos _).le (by have := quota_p; positivity))) h
lemma vertexP {u:AxisT}{A:Bale N P→ Op (Iota G)}{a c e:ℝ}(p: Crown (badge _) (rope G u e) (rope G u e) a c (fun i=> A i.val))(h:0<a)(g:0<e): Seat (weave G e) (fun i=> Matrix.trace (A (post i.val))) (a/2) (quartzK a c):=by
 let f(x:Loom G e): TopK G e:=⟨post x.val,x.val,x.property,by simpa using g⟩
 obtain ⟨F,C,q,W,r⟩:=p; let Q(S:Seal (Site (More P)))(x:Loom G e):=(F S (f x)).trace
 refine ⟨Q,_,⟨fun S=>?_,fun i=>Branch.tall (s:=rope G u e) (P:=F) (fun S=>(q S).toTicket) W h (cD G e) quota_p.le i⟩,fun i=> Eq.trans (congrArg Matrix.trace (r (f i))) (Matrix.trace_sum ..)⟩
 have he:= ledgerT (q S).toTicket
 refine ⟨he.posT,he.conduct, he.continuousE.comp ((post_c.comp continuous_subtype_val).subtype_mk _),fun x=> he.norms (f x),fun x y p=>?_,fun x g=>?_⟩
 · have hv:= he.varies (f x) (f y); rw [show (curveD G e).eval S (f x) (f y)=0 from (by change bookK _ _ _ S / _=0; rw [paid_zero G e x y S p,zero_div]),mul_zero] at hv; exact sub_eq_zero.mp (norm_le_zero_iff.mp hv)
 have hp: f ((weave G e).dress g x) = (curveD G e).drive g (f x):= Subtype.ext (speak G g _).symm
 exact (congrArg (fun i=>Matrix.trace (F S i)) hp).trans (he.gauge g _)

abbrev BinK(N:Side)(e p:ℝ): Set (Gaz N):= {x|Guard x.1 e∧Slow x.1 (hook x.2.1) p ∧ Slow x.1 (hook x.2.2) p}
lemma local_cpn (e p:ℝ)(N:Side) : LocallyCompactSpace (BinK N e p) :=by
 let S:Set (Bkg (More N) × Stun N):={x|Slow x.1 (hook x.2) p}
 have hp:IsOpen S:=by -- generalize above
    unfold S Slow; simp_rw [Set.setOf_forall]
    apply isOpen_iInter_of_finite; intro i; apply isOpen_iInter_of_finite; intro t
    apply isOpen_lt _ continuous_const; apply Continuous.norm
    have hz(i:Site (More N)): Continuous (fun x:Bkg (More N) ×Stun N=>hook x.2 i):=by unfold hook; fun_prop
    let F : Bkg (More N) ×Stun N → SU.E:=fun x=>x.1 (i,t)
    have hf:Continuous F:= (show Continuous (fun x:Bkg (More N)=>x (i,t)) from continuous_apply _).comp continuous_fst
    have hh:=hf.prodMk (hz (i+step t)); have he:= turn_cont.comp hh; exact he.sub (hz i)
 let Q:= {x:Gaz N|Guard x.1 e}; have he:IsClosed Q:= (cover_closed _ _).preimage continuous_fst
 exact (he.isLocallyClosed.inter (((hp.preimage (continuous_fst.prodMk (continuous_fst.comp continuous_snd))).inter (hp.preimage (continuous_fst.prodMk (continuous_snd.comp continuous_snd) ))).isLocallyClosed)).locallyCompactSpace -- tune

def foamK(N:Side)(e p:ℝ): Light (Fend N) (BinK N e p) (Fend N→SU.E) where
 frame:=terr _
 rel T x y:= Agrees T x.val.1 y.val.1 ∧ AgreeF T x.val.2.1 y.val.2.1 ∧ AgreeF T x.val.2.2 y.val.2.2
 expands _ _ h _ _ q:= ⟨fun i a b=> q.1 i (h a) (h b), q.2.1.less h,q.2.2.less h⟩
 dress g x:=⟨(gauge g x.val.1, feast g x.val.2.1,feast g x.val.2.2),Cube.Guard.cov x.property.1 g,slow_g _ _ g x.property.2.1,slow_g _ _ g x.property.2.2⟩
end YM.CF.Broc
