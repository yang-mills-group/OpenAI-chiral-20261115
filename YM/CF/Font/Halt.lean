import YM.CF.Font.Flow
set_option autoImplicit false
noncomputable section
namespace YM.CF.Font
open Function Filter Metric Lattice Wilson Laurent RG Precision Tree Finset Exterior Extra Extra.Iteration Bloch Matrix
open scoped Topology ContDiff BigOperators InnerProductSpace
variable {L f n c:Side}
abbrev Lett(n:Side):= form 1 n
def lamp (A:Lett n): Links (Per n) ℝ:= fun p=> A (p.1,coord p.2)
def amble (z:Axis→ℝ):Lett n:=fun p=>z (axisEquiv.symm p.2)
lemma lamp_f (A B:Lett n)(e:lamp A=lamp B): A=B:=by funext v; obtain ⟨u,rfl⟩:= (Channel.bondBody n).surjective v; exact congr_fun e u
lemma simpleH (x: Site n)(i:Axis)(z:Axis→ℝ)(k:ℕ): integralLink x (List.replicate k (posDir i)) (amble z)=k*z i:=by
 change linkSum _ _ _=_; induction k generalizing x with
 | zero=> simp [linkSum]
 | succ k h=> rw [List.replicate_succ, linkSum,h]; change z (axisEquiv.symm (axisEquiv i)) + _=_; rw [axisEquiv.symm_apply_apply]; simp [add_mul,add_comm]
lemma mend (x:Site n)(z:Axis→ℝ)(a:Axis):heat x (lamp (amble z)) (.inr a)=n.val*z a:= simpleH ..
lemma merr (x:Site n)(z:Axis→ℝ)(a:Ps n): heat x (lamp (amble z)) (.inl a) =0:=by rw [show heat x (lamp (amble z)) (.inl a)=_ from ring_plaquette a.1 a.2 (amble z),d_plaquettes]; unfold amble; ring_nf
lemma useful (x:Site n)(A:Lett n)(h:d 1 n *ᵥ A=0) :∃ v : form 0 n, ∃ z:Axis→ℝ, A = d 0 n *ᵥ v + amble z :=by
 let z:Axis→ℝ:=fun i=> heat x (lamp A) (.inr i)/n.val; let B:= A-amble (n:=n) z; let C:=sap x (lamp B); let v(u:Body 0 n):= C u.1
 have hz(i:Wind n): heat x (lamp B) i=0:=by cases i with
    | inl p=>
       have he(V:Lett n): heat x (lamp V) (.inl p)=(d 1 n*ᵥ V) (p.1,plaquette p.2):=ring_plaquette ..
       rw [he]; unfold B; rw [mulVec_sub,Pi.sub_apply,h,←he (amble z),merr]; simp
    | inr i=> change integralLink x _ _=_; unfold B; rw [map_sub]; rw [show integralLink x _ (amble z)=_ from (mend x z i)]; change _-n.val*(integralLink x (swirl n i) A/n.val)=0; field_simp; ring
 have hf: lamp B=pure C:=by
    funext i; obtain ⟨a,-,-,H⟩:= funnel ℝ x i; have hy:=H (lamp B); simp only [hz,smul_zero,sum_const_zero,Pi.sub_apply] at hy; exact sub_eq_zero.mp hy
 have hv: B=d 0 n *ᵥ v:= by apply lamp_f; rw [hf]; funext e; unfold lamp pure; rw [d_sites]
 refine ⟨v,z,?_⟩; rw [← hv] ; unfold B; rw [ sub_add_cancel]
lemma amble_zero (x:Site n)(z:Axis→ℝ)(v:form 0 n)(e:amble z=d 0 n *ᵥ v): z=0:=by
 funext a; have he: heat x (lamp (amble z)) (.inr a)=0:=by rw [e]; change integralLink _ _ _=_; rw [Precision.telescopes,swirl_stop, sub_self]
 rw [mend] at he; exact (mul_eq_zero.mp he).resolve_left (by exact_mod_cast n.property.ne')
variable (S:StepData c f)
lemma mean_s (z:Axis→ℝ): mean S *ᵥ amble z=amble (fun a=> S.patch.L.val * z a):=by
 funext v
 simp only [mean,LinearMap.toMatrix'_mulVec,LinearMap.pi_apply,LinearMap.sum_apply,LinearMap.smul_apply]
 let a:=axisEquiv.symm v.2
 have hf:S.repath a=List.replicate S.patch.L.val (posDir a):=by simp [StepData.repath,straight,posDir]
 change ∑ i:S.patch.Points, S.patch.weight i • integralLink _ (S.repath a) (amble z)= S.patch.L.val*z a; simp_rw [hf,simpleH,smul_eq_mul, ←sum_mul, S.patch.weight_sum,one_mul]
lemma dep_m(v:form 0 f):∃ u:form 0 c, mean S *ᵥ (d 0 f *ᵥ v)=d 0 c*ᵥ u:=by
 let u(b: Body 0 c):= ∑ a:S.patch.Points,S.patch.weight a*v (atPoint S b.1 a,vac)
 refine ⟨u,?_⟩; ext x; obtain ⟨⟨x,i⟩,rfl⟩:= (Channel.bondBody c).surjective x; rw [mean_site]; change (∑ a:S.patch.Points,S.patch.weight a*_)= (d 0 c *ᵥ u) (x,coord i); simp_rw [mul_sub, sum_sub_distrib]; rw [d_sites]; change _-_= u (x+step i,vac)- _; congr 1; unfold u; congr 1; simp [Channel.bondBody, show ∀ i:Axis,axisEquiv.symm (coord i)=i from (fun i=> axisEquiv.symm_apply_apply _)] -- tune
variable {P Q:Bed}{T:Towers S.patch.L}{a A B γ D:ℝ}(h:0<a)(he:P.dual_diag.strip a A)(hf:Q.diagonal.strip a B)(v:T.Deep a A 1){p:Clip}(H:Floor P p f γ D)(g:Towers.Diagonal S P Q T)
include h he hf v H g
lemma rotor (u:form 0 c): let w:=installed S.ratio T.A0; ∃ q:form 0 f,w *ᵥ (d 0 c *ᵥ u)=d 0 f *ᵥ q:=by
 intro w; let L:=d 0 c*ᵥ u; let z :=w*ᵥ L
 have ht: d 1 f*ᵥ z=0:=by unfold z; rw [mulVec_mulVec,show d 1 f*w=_ from (psi_curl h he hf (show 1 ≤1 from le_rfl) v S.sizes H.diagonalInv g.stays).symm,← mulVec_mulVec] ; unfold L; rw [mulVec_mulVec (M:=d 1 c) (N:=d 0 c),Exterior.closed 0, zero_mulVec,mulVec_zero]
 have hy : mean S *ᵥ z=L:=by unfold z; rw [mulVec_mulVec,show mean S*w=_ from g.trial.dual,sub_mulVec,one_mulVec,smul_mulVec]; unfold L; rw [mulVec_mulVec (M:=K (Q.metric.acts c)),K_kills,zero_mulVec,smul_zero,sub_zero] -- tune
 obtain ⟨x,l,hx⟩:=useful (0:Site f) z ht; obtain ⟨y,hg⟩:=dep_m S x; rw [hx,mulVec_add,hg,mean_s] at hy
 let V:=fun i=> (S.patch.L.val:ℝ)*l i; have hh : amble (n:=c) V=d 0 c *ᵥ (u-y):=by rw [mulVec_sub,show d 0 c*ᵥ u=_ from hy.symm]; abel -- tune
 have hv:l=0:=by
    have hk:=amble_zero 0 V _ hh; funext i; exact (mul_eq_zero.mp (congr_fun hk i : (S.patch.L.val:ℝ)*_=0)).resolve_left (by exact_mod_cast S.patch.L.property.ne')
 refine ⟨x,?_⟩; change z=_; rw [hx,hv,show amble (n:=f) 0=0 from rfl,add_zero]
end YM.CF.Font
