import YM.CF.Scroll.Chalk
set_option autoImplicit false
noncomputable section
namespace YM.CF.Scroll
open Function Filter Matrix NormedSpace Finset Fock Lat Lattice Rush Cube Next.Free Laurent Fir Bloch
open scoped Matrix.Norms.L2Operator Matrix Topology MatrixOrder BigOperators
attribute [local instance] opCStarAlgebra
-- read transform signs
variable {b r: Bool}{s:Signed}{U:UNI SpinIdx} (h:JetS s b r U)
variable (N:Side)(ho:Odd N.val)(p:Momentum)(hg:p∈baseCube)
def cadence (s:Signed) (b:Bool)(x:Momentum):Momentum:=hush b (s.act x)
lemma physical_s (s:Signed)(t:Bool)(hp:physical p): physical (cadence s t p):=by
 rw [physical_iff] at *; intro i; obtain ⟨i,rfl⟩:=s.perm.surjective i; cases t<;> cases h:s.flip i <;> simp [cadence,h,hp]
include hg in
lemma cadence_base (s:Signed)(t:Bool): cadence s t p∈baseCube:=by
 refine ⟨physical_s p s t hg.1,fun i=>?_⟩; obtain ⟨i,rfl⟩:=s.perm.surjective i; cases t<;> cases f:s.flip i<;> simpa [cadence,f] using hg.2 i
lemma ca_ne (s:Signed)(t:Bool)(g:p≠0):cadence s t p≠0:=by
  have hx:=s.act_injective.ne g; rw [Signed.act_zero] at hx; cases t<;>simpa [cadence]
lemma form (s:Signed)(t:Bool) (hp:physical p)(x:Cover): mode (cadence s t p) (s.act x)= cSignX t (mode p x):=by
 unfold mode; rw [←Equiv.sum_comp s.perm]; let f(i:Axis):= p i*x i; rw [physical_iff] at hp; cases t
 · change Complex.exp _=Complex.exp _; congr 2; apply sum_congr rfl; intro i _; cases h:s.flip i<;> simp [cadence,h]
 change Complex.exp _=star (Complex.exp _); rw [Complex.star_def,←Complex.exp_conj]; congr 1;
 rw [show (∑ i:Axis,cadence s true p (s.perm i)*((s.act x (s.perm i):ℤ):ℂ))=∑ i:Axis, -(p i*(x i:ℂ)) from Finset.sum_congr rfl (fun i _=> by cases h:s.flip i<;> simp [cadence,h]), Finset.sum_neg_distrib, map_mul, map_sum]
 simp only [Complex.conj_I, map_mul,map_intCast, Complex.conj_eq_iff_im, show ∀ i, (starRingEnd ℂ) (p i)=p i from fun i=> Complex.conj_eq_iff_im.mpr (hp i)]; simp
lemma sine_s (s:Signed)(t):sine (cadence s t p)=cadence s t (sine p):=by
 funext i; obtain ⟨i,rfl⟩:=s.perm.surjective i; cases t<;>cases f:s.flip i<;>simp [cadence,f,sine]
lemma kin_s (s:Signed)(t):kin (cadence s t p)=kin p:=by unfold kin; rw [← Equiv.sum_comp s.perm]; congr 1; apply sum_congr rfl; intro i _; cases t<;>cases f:s.flip i<;>simp [cadence,pl,f]
lemma prod_s (s:Signed)(t)(q:Momentum):prodM (cadence s t p) (cadence s t q)=prodM p q:=by
 unfold prodM; rw [← Equiv.sum_comp s.perm]; apply sum_congr rfl; intro i _; cases t<;>cases f:s.flip i<;>simp [f,cadence]
lemma gD_s (s:Signed)(t):gD (cadence s t p)=gD p:=by
 simp only [gD,rad,mag,sine_s,kin_s]; simp_rw [sq]; rw [show (∑ i:Axis,cadence s t (sine p) i*cadence s t (sine p) i)=_ from prod_s ..]; rfl
def Cad (s:Signed)(t:Bool): Momentum ≃+ Momentum where
 toFun:= cadence s t
 invFun:=cadence s⁻¹ t
 map_add' x y:= by cases t <;>simp [cadence]; abel -- tune
 left_inv x:=by cases t <;>simp [cadence]
 right_inv x:=by cases t<;>simp [cadence]
def CadSite(N:Side)(s:Signed)(t:Bool): Site N≃+Site N where
 toFun:=fun x=> hush t (s.act x)
 invFun:=fun x=>hush t (s⁻¹.act x)
 map_add' x y:= by cases t<;> simp; abel
 left_inv x:=by cases t<;>simp
 right_inv x:=by cases t<;>simp
lemma cadence_m (s:Signed)(u:Bool)(t:ℂ): cadence s u (t • p)= t • cadence s u p:=by
 funext i; obtain ⟨i,rfl⟩:= s.perm.surjective i; cases u<;>cases h:s.flip i<;> simp [cadence,h]
include ho
lemma muff_s (s:Signed)(t)(j):muff j N (cadence s t p)=muff j N p:=by unfold muff; rw [← Equiv.prod_comp s.perm]; congr 1; apply prod_congr rfl; intro i _; cases t <;>cases f:s.flip i<;>simp [cadence,f,plank_even N ho]
lemma alias_s (s:Signed)(t) (l:Site N): aliasAt (cadence s t p) (CadSite N s t l)=cadence s t (aliasAt p l):=by
 funext i; obtain ⟨i,rfl⟩:=s.perm.surjective i; cases t
 · cases h:s.flip i<;> simp [cadence, show CadSite N s false l=s.act l from rfl,alias_value,Ratio.lift_signed_of_odd ho,h] <;> ring
 rw [alias_value,show lift (CadSite N s true l)= -lift (s.act l) from ?_];
 · cases h:s.flip i<;>simp [cadence,alias_value,h,Ratio.lift_signed_of_odd ho] <;> ring
 change lift (-_)=_; apply lift_eq_iff.mpr; refine ⟨by simp,fun j=>?_⟩; have he:= centers_odd (s.act l) ho j; simp only [Pi.neg_apply]; omega
lemma mixL_s (s:Signed)(t)(j):mixL j N (cadence s t p)= cadence s t (mixL j N p):=by
 unfold mixL; rw [← Equiv.sum_comp (CadSite N s t).toEquiv,cadence_m]
 change _ • (∑ i:Site N, muff _ _ (aliasAt _ (CadSite N s t i))^2 • _) = _ • Cad s t (∑ l:Site N, _); rw [map_sum]; congr 1
 apply sum_congr rfl; intro i _; simp only [AddEquiv.coe_toEquiv,Cad,AddEquiv.coe_mk,Equiv.coe_fn_mk,bGraph,alias_s N ho,muff_s N ho,cadence_m]; rw [show (CadSite N s t).toEquiv i=CadSite N s t i from rfl,alias_s N ho,gD_s,sine_s] -- tune
omit ho
include h
lemma angleX (u: Bool): sings b U (angle u)=angle (r.xor u):=by
 have hx:sings b U Aop= angle (r.xor true):=by
   rw [Adef,singT,win_c,win_a,win_i,twist_scalar,map_add,map_one,← singT,h.grade]; have hh:cSignX b (1/2)=1/2:=by cases b <;> norm_num [cSignX]
   rw [hh]; cases r; exact Adef.symm
   change _=1-Aop; rw [Adef,hush_true]; module
 cases u; swap; exact hx
 change sings b U (1-Aop)=_; simp only [singT,win_l,win_i,map_sub,map_one]; rw [←singT,hx]; cases r; swap; simp [angle]; rfl
lemma zen_s (t:Momentum)(p:physical t): sings b U (zen (cadence s b t))=zen t:=by
 let w:=b; rw [zen,zen,singT, win_sum,map_sum,←Equiv.sum_comp s.perm]; refine sum_congr rfl fun i _=>?_
 simp only [win_c,twist_scalar, ←singT,h.cliff]; rw [physical_iff] at p
 have hx:star (t i)=t i:= Complex.conj_eq_iff_im.mpr (p i);
 cases h:b <;>cases g:s.flip i<;>simp [h,g,cadence,cSignX,hx]
include ho hg
lemma bent_s (u:Bool)(j:ℕ): sings b U (bent u j N (cadence s b p))=bent (r.xor u) j N p:=by
 let V:= mixL j N p; by_cases hx:p=0
 · subst p; rw [show cadence s b 0=0 from (Cad s b).map_zero]; -- formula bar0
   have hv (x:Bool): bent x j N 0=angle (!x):=by cases x<;>simp [bent,bar_origin,angle]
   rw [hv u,hv, angleX h]; cases r<;>cases u<;>rfl -- tune
 have hv:=ca_ne p s b hx; have hu:=base_subset_realCube zone_pos hg; have he:=base_subset_realCube zone_pos (cadence_base p hg s b); have hh:= phys_mix j N ho p hg.1
 have ht : shell j N (cadence s b p)=shell j N p:=by rw [shell_inv _ _ he hv,shell_inv _ _ hu hx,mixL_s N ho p,prod_s]
 have hm : cSignX b (shell j N p)= shell j N p:=by rw [shell_inv _ _ hu hx,prodM_self _ hh]; cases b<;>simp [cSignX]
 rw [aspTrace u j N ho he hv, aspTrace (r.xor u) j N ho hu hx]; rw [singT, win_c,ht,hm]; simp only [twist_scalar,win_m,win_l,win_a,map_mul,map_add,map_sub,win_i,map_one]; -- tune
 rw [mixL_s N ho p, ← singT,zen_s h _ hh,←singT, angleX h]
end YM.CF.Scroll
