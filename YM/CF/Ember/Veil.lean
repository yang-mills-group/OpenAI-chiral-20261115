import YM.CF.Ember.Rum
set_option autoImplicit false
noncomputable section
namespace YM.CF.Ember
open Function Filter Metric Fir Lattice Laurent Next.Free Bloch Finset Lat Stationary
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix Matrix.Norms.L2Operator Kronecker
attribute [local instance] opCStarAlgebra
variable {ι n:Type*} [Fintype n][DecidableEq n]
def spoon (p q:Momentum): Momentum:=p+(q+q)
lemma riverS {t:Tax ι}(i:ι)(p: Gaia)(a:Axis)(z:ℂ):spoon (river p) (spark a (raf t i z))=river p+spark a (2*raf t i z):=by rw [spoon, spark_plus]
lemma raf_star(t:Tax ι)(i:ι)(z:ℂ): star (raf t i z)=raf t i (star z):=by simp [raf,mul_comm]

def MountH(T:Op n)(p q:Momentum):Op (coneA n):=flint T*star (Lent n (star p))+Lent n (spoon p q)*star (flint T)
def oval(T:Op n)(p q:Momentum):ℂ:= Matrix.trace (tipH n (spoon p q)*MountH T p q*tipH n p*star (MountH T (star p) (star q)))
namespace Tween
variable {T:Op n}{j:ℕ}{M N:Side}{η C:ℝ}
def rail(U:Tween T j M N η C)(p q:Momentum):Op (coneA n):= U.stem (q,p)*star (fuel n j M (star p))+ fuel n j M (spoon p q)*star (U.stem (-star q, spoon (star p) (star q)))
def wheels(U:Tween T j M N η C)(p q:Momentum):ℂ:= Matrix.trace (edgeH n j M (spoon p q)*rail U p q*edgeH n j M p*star (rail U (star p) (star q)))
def sear(U:Tween T j M N η C)(p q:Momentum):ℂ:= Matrix.trace (edgeH n j M p * U.halo (q,p))
end Tween

variable {N M:ι→Side}{T:Op n}{j:ℕ}(y:1≤j){η C:ℝ}(h:0<η)(g:0<C)
variable (U:∀ i:ι,Tween T j (M i) (N i) η C)
variable {t:Tax ι}(R:∀ i,pinch (N i)≤ t.r i)(x:ι→Gaia)(w:∀ i,x i∈boundsEarth)(e:∀ i,t.r i=‖x i‖)
lemma coal {f:ι→ℂ→Op n}{s:ℤ}(h:Act t s f):Act t s fun i z=> Matrix.trace (f i z):= h.via (Matrix.traceLinearMap n ℂ ℂ).toContinuousLinearMap
lemma spar_move (a:Axis): Move t fun i z=> spark a (raf t i z):=by
 have ht:Move t fun _ _=>(0:Momentum):= Move.left (A:=1) (fun i=>⟨by simp [physical],fun p=>by simp [Real.pi_pos.le]⟩) one_pos (fun i=>by simp [(t.pos i).le]); simpa only [zero_add] using Move.add ht (sparkBud t (raft t) a) (fun i=>by simp [raf])
include y U h g R
lemma mount_motion (a:Axis)(p q:ι→ℂ→Momentum)(P:Move t p)(Q:Move t q):Act t 1 fun i z=> (U i).stem (q i z,p i z)-flint T:=by
 have hh:= Q.sand P (fun i=> (U i).quote) h g; have hx:=wardBud y h g U
 have he : Act t 1 fun (i:ι) _=> (U i).stem 0-flint T:=by
   obtain ⟨d,C,v,c,H⟩:=hx; refine ⟨d,C,v,c,fun i z hz=>⟨differentiableAt_const _,((H i z hz).2).trans ?_⟩⟩; simp only [_root_.zpow_one]; exact mul_le_mul_of_nonneg_left (R i) c.le
 convert hh.add he using 1; ext1 i; ext1 z; rw [sub_add_sub_cancel]
include w e
lemma under_r (a:Axis): Act t 1 (fun i z=> (U i).rail (river (x i)) (spark a (raf t i z)))∧Act t 2 fun i z=> (U i).rail (river (x i)) (spark a (raf t i z))-MountH T (river (x i)) (spark a (raf t i z)):=by
 let X(i:ι)(_ :ℂ):=river (x i); let Q(i:ι)(z:ℂ):= spark a (raf t i z); let Z(i:ι)(z:ℂ):= spoon (X i z) (Q i z); let V(i:ι)(z:ℂ):= -Q i z
 have hQ:Move t Q:= spar_move a; have hX:Move t X:= principal_in _ x e w; have hz:Move t Z:=by unfold Z X Q; simp_rw [riverS]; exact kinder e w a
 have ht: Move t V:=⟨hQ.act.neg,fun a h=> (hQ.hit a h).imp fun b ⟨hv,B⟩=> ⟨hv,fun i z hz=> cube_neg _ (B i z hz)⟩⟩
 have hh(i:ι):= (U i).oddV; have he:= hX.sap n M hh j y; have hL:= hX.pulseL n; have hg:=hz.pulseL n; have hr:=hX.fossil n M hh j y; have hn:=hz.fossil n M hh j y; have hm := hQ.bend hX (fun i=> (U i).quote) h g; have hy:= ht.bend hz (fun i=> (U i).quote) h g; have qz : Act t 1 fun i z=> (U i).rail (X i z) (Q i z):=by
    apply Act.transfer (Act.add (p:=1) (hm.mul hr.sun) (hn.mul hy.sun)); refine ⟨1,one_pos,fun i z hz=>?_⟩; unfold Tween.rail V Z Q X; rw [riv_phys, spark_star,raf_star]
 have hu:= mount_motion y h g U R a X Q hX hQ; have hf:= mount_motion y h g U R a Z V hz ht; let L:=MountH T
 refine ⟨qz,?_⟩
 have hb : Act t 1 fun i z=> star ((U i).stem (V i (star z),Z i (star z)))-star (flint T):=by simpa only [star_sub] using hf.sun
 have hx: Act t 2 fun i z=> star (fuel n j (M i) (X i (star z)))-star (Lent n (X i (star z))):=by simpa only [star_sub] using he.sun
 have hw:= Act.add (p:=2) (Act.diffM (p:=0) (a:=1) (Act.anchor t (flint T)) hr.sun hu hx) (Act.diffM (p:=1) (q:=0) (a:=1) hg hy.sun (hz.sap n M hh j y) hb)
 apply Act.transfer ?_ ⟨1,one_pos,?_⟩; rotate_left; exact hw -- goals order?
 intro i z _; unfold Tween.rail Z X Q V MountH; simp only [riv_phys,spark_star,raf_star,Q]
 abel -- tune
lemma stormL (a:Axis): Act t (-1) fun i z=> (U i).wheels (river (x i)) (spark a (raf t i z))-oval T (river (x i)) (spark a (raf t i z)):=by
 let X(i:ι)(_ :ℂ):=river (x i); let Q(i:ι)(z:ℂ):= spark a (raf t i z); let Z(i:ι)(z:ℂ):= spoon (X i z) (Q i z)
 have hQ:Move t Q:= spar_move a; have hX:Move t X:= principal_in _ x e w; have hZ:Move t Z:=by unfold Z X Q; simp_rw [riverS]; exact kinder e w a
 obtain ⟨hk,hv⟩:= under_r y h g U R x w e a; have hp(i):=(U i).oddV
 have he:= hZ.chillL n M hp j y x (fun i=> by unfold Z X Q; simp [raf,spoon]; rfl) e w; have hr:=hX.chillL n M hp j y x (fun _=>rfl) e w; have hm:= hZ.moisten n M hp j y x (fun i=>by unfold Z X Q; simp [raf,spoon]; rfl) e w; have ht:=hX.moisten n M hp j y x (fun _=>rfl) e w
 let F(i:ι)(z:ℂ):=MountH T (X i z) (Q i z); let f(i:ι)(z:ℂ):=(U i).rail (X i z) (Q i z)
 have hx: Act t (-2) fun i z=>tipH n (Z i z):=by apply Act.transfer (hm.sub (he.loose (by decide))); refine ⟨1,one_pos,fun i z _=>?_⟩; rw [sub_sub_cancel]
 have hy:Act t (-2) fun i z=>tipH n (X i z):=by apply Act.transfer (ht.sub (hr.loose (by decide))); refine ⟨1,one_pos,fun i z _=>?_⟩; rw [sub_sub_cancel]
 have hw:Act t 1 F:=by apply Act.transfer (hk.sub (hv.loose (by decide))); refine ⟨1,one_pos,fun i z _=>?_⟩; rw [sub_sub_cancel]
 have h1:Act t 0 fun i z=> edgeH n j (M i) (Z i z)*f i z-tipH n (Z i z)*F i z:= Act.diffM (p:=-2) (q:=1) (a:=1) hx hk he hv
 have h2:Act t (-2) fun i z=> edgeH n j (M i) (Z i z)* f i z*edgeH n j (M i) (X i z)-tipH n (Z i z)*F i z*tipH n (X i z):= Act.diffM (p:=-1) (q:=-2) (a:=1) (hx.mul hw) ht h1 hr
 have hn:Act t 2 fun i z=> star (f i (star z))-star (F i (star z)):=by simpa only [star_sub] using hv.sun
 have hz :Act t (-1) fun i z=> edgeH n j (M i) (Z i z)*f i z*edgeH n j (M i) (X i z)*star (f i (star z))-tipH n (Z i z)*F i z*tipH n (X i z)*star (F i (star z)):= Act.diffM (f:=fun i z=> edgeH n j (M i) (Z i z)*f i z*edgeH n j (M i) (X i z)) (p:=-3) (q:=1) (a:=1) ((hx.mul hw).mul hy) hk.sun h2 hn
 apply Act.transfer (coal hz); refine ⟨1,one_pos,fun i z _=>?_⟩; unfold Tween.wheels oval; rw [spark_star,riv_phys,raf_star,Matrix.trace_sub]
omit R in
lemma quake (a:Axis): Act t (-1) fun i z=> (U i).sear (river (x i)) (spark a (raf t i z))-(U i).sear (river (x i)) 0:=by
 let F:=principal_in _ x e w; have hx:= (spar_move (t:=t) a).sand F (fun i=>(U i).other) h g; have hp:Act t 1 fun i z=> (U i).halo (spark a (raf t i z),river (x i))-(U i).halo (0,river (x i)):=by apply (hx.sub hx.core).transfer; refine ⟨1,one_pos,fun i z _=>?_⟩; simp [raf]
 have he:= F.moisten n M (fun i=>(U i).oddV) j y x (fun i=>rfl) e w
 have hh:Act t (-1) fun i z=>(edgeH n j (M i) (river (x i)))*((U i).halo (spark a (raf t i z),river (x i))-(U i).halo (0,river (x i))):=he.mul hp
 apply Act.transfer (coal hh); refine ⟨1,one_pos,fun i z _=>?_⟩; rw [mul_sub,Matrix.trace_sub]; rfl
end YM.CF.Ember
