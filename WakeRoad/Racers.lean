import WakeRoad.Spread
/-! # Wake polynomial in the curl colors. First compute Fock vacuum at full list. -/
set_option autoImplicit false
set_option synthInstance.maxSize 24000
set_option maxHeartbeats 300000
noncomputable section
namespace YM.CF.Hiro
open Function Filter Metric Fock Finset Fir Jill Lat Lattice Laurent Next.Free Bloch Cube Sods Tulip Scroll Spire Pastry RP Branch Wilson Phase SU Rush Mir Reflect Buffered Lifted Bilinear Window Skye Emu Onyx Kea Flare Dial
open Cache Glaze
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators InnerProductSpace Topology Classical ContDiff
attribute [local instance] opCStarAlgebra
open YM.CF.Lamour YM.CF.Velvet
open YM.CF.Lamour.Bridge.Celeste
open YM.WakeRoad
open Ballad
namespace Hearth
variable {N:Side} {n j:ℕ}
variable (X:Fin n → Cover)(L:Fin n → Twah.DirSpin)(r:ℕ)(n_:Side)
abbrev scoreFlow (x:Fin n → ColorL) := serve (fun i=> wrapCurrent (X i) (L i) r n_ (x i))
abbrev swatches(n:ℕ):= Fin n→ SU.group.ColorIndex
abbrev fibers(n:ℕ):=Fin n × SU.group.ColorIndex
abbrev tintM (c:SU.group.ColorIndex):ColorL:= mug c
lemma mug_book (x:ColorL)(a:prismIndex):mug.coord a x=x a:=by change ((EuclideanSpace.basisFun prismIndex ℝ).toBasis.repr x) a=x a; simp
lemma mug_price (c:prismIndex): ‖tintM c‖=1:= (EuclideanSpace.basisFun prismIndex ℝ).orthonormal.1 c
lemma score_one (i:Fin n)(a:ColorL):wrapCurrent (X i) (L i) r N a= ∑ j:prismIndex, (↑(a j):ℂ) • wrapCurrent (X i) (L i) r N (tintM j):=by
 nth_rw 1 [show a=∑ i:SU.group.ColorIndex,(mug.coord i a) • mug i from (mug.sum_repr a).symm]; rw [map_sum]; refine sum_congr rfl fun i _=>?_ ; rw [map_smul,mug_book,RCLike.real_smul_eq_coe_smul (K:=ℂ)]; rfl
-- ordered ('time' is whatever endpoint layout the call gives)
def pigment (y w:Wave (Single n_))(c:swatches n): ℂ:= alleyR y w (scoreFlow X L r n_ (fun i=> tintM (c i)))
variable (P:swatches n→ℂ)
def brush (x:fibers n→ℝ) :ℂ:=∑ a: swatches n,(∏ i:Fin n,(↑(x (i,a i)):ℂ))*P a
variable (y w:Wave (Single n_))
lemma brush_life (x:Fin n→ ColorL): alleyR y w (scoreFlow X L r n_ x)= brush (pigment X L r n_ y w) (fun a=> x a.1 a.2):=by
 unfold scoreFlow;  erw [funext (fun i=>score_one X L r (N:=n_) i (x i))]; rw [serve_expand (fun i j=>(↑(x i j):ℂ)),map_sum]; apply sum_congr rfl; intro i _; rw [map_smul,smul_eq_mul]; rfl
private abbrev duets := SU.Slot × SU.Slot
abbrev Picture (n:ℕ):= Fin n × (SU.Slot × Bool)
private def ribbon (I:Fin n→duets)(i:Fin n):List (Picture n):=[(i,(I i).2,true),(i,(I i).1,false)]
def ribbonCast (I:Fin n→(SU.Slot×SU.Slot)):List (Picture n):= (List.ofFn (ribbon I)).flatten
abbrev toneChart (p:Picture n) : Reader0 (Single n_):= if p.2.2 then en0 r (X p.1) (L p.1) p.2.1 else ex0 r (X p.1) (L p.1) p.2.1
variable (M:Jill.Male)
private lemma scanner (I:Fin n → duets): serve (fun i:Fin n=> sold r (X i) (L i) (N:=n_) (I i).1 (I i).2)= rollC (ton ∘ toneChart X L r n_) (ribbonCast I):=by
 unfold rollC ribbonCast; rw [List.map_flatten, List.prod_flatten, List.map_map,List.map_ofFn]; apply congrArg List.prod; apply congrArg List.ofFn; funext i; simp [ribbon, Function.comp_apply,toneChart,sold]

lemma seasons_read {X:Type*} (Z: List X)(T:X→ Reader0 (Single N))(hL:∀ i,KeyT (T i) (tickA N))(M:Jill.Male)(x:Wave (Single N))(p:Sea (spar j M (1:Pane N)) x)(h:1≤j)(t:Kea.Pad j N): alleyR (mateK N) x (rollC (ton ∘ T) Z)=runes (fun i k=> rankG (lake N j M) (T i) (T k)) Z:=by -- from Hiro.Lard private
    have ht:= (pitch M h t.1); let L:= ht.1
    let y:= mateK N; have hv:Sea (Dofu N (field (too N) j M)) x:= coasting t M ▸ p; have Hy:=tickB N
    have hg: skyGlow y 1 x≠0:= shines L x y hv Hy
    change (inner ℂ y x)⁻¹*inner ℂ y (acts (rollC (ton ∘ T) Z) x)=runes _ Z
    have v:= Emu.frown L Hy hv T hL Z
    unfold pRead skyGlow at v; simp_rw [quant_one,mul_one,act_one,←ht.2] at v; rw [skyGlow,quant_one,act_one] at hg; rw [show inner ℂ y _= _ from v,inv_mul_cancel_left₀ hg]

/-- Also permit pricing without separating row powers. -/
def spinFilm(n:ℕ)(L:Fin n→Op SU.Slot)(D:Picture n→Picture n→ℂ):ℂ:=∑ a:Fin n→duets,(∏ i:Fin n,L i (a i).1 (a i).2)*runes D (ribbonCast a)
abbrev photo (j:ℕ)(M:Jill.Male) (a b:Picture n):ℂ := rankG (lake n_ j M) (toneChart X L r n_ a) (toneChart X L r n_ b)
lemma noble_photo (A:Fin n→ ColorL){v:Wave (Single n_)}(p:Sea (spar j M (1:Pane n_)) v)(h:1≤ j)(t:Kea.Pad j n_):
    alleyR (mateK n_) v (scoreFlow X L r n_ A)=spinFilm n (fun i=> walkC (A i)) (photo X L r n_ j M) := by
 let P(p:Fin n)(i:duets):= sold r (X p) (L p) (N:=n_) i.1 i.2; let χ(p:Fin n)(i:duets):ℂ:=walkC (A p) i.1 i.2
 have he(p:Fin n):wrapCurrent (X p) (L p) r n_ (A p)=∑ i:duets, χ p i • P p i:=by rw [Fintype.sum_prod_type,tomato]; rfl
 unfold scoreFlow; simp_rw [he]; rw [serve_expand χ P,map_sum]; refine sum_congr rfl fun i _=>?_ ; rw [map_smul,smul_eq_mul]
 unfold P; rw [scanner,seasons_read _ _ ?_ M v p h t]
 intro i; unfold toneChart; split <;> exact nac_k ..
lemma pigment_power (A:Fin n→ ColorL): scoreFlow X L r n_ A=((r:ℂ)^(3*n)) • scoreFlow X L 1 n_ A:=by
 have h(i:Fin n) : wrapCurrent (X i) (L i) r n_ (A i)=(r:ℂ)^3 • wrapCurrent (X i) (L i) 1 n_ (A i):=by simp_rw [dgC]; norm_num
 unfold scoreFlow; rw [funext h,serve_smul (fun _=> (r:ℂ)^3)]; simp [pow_mul]
lemma spin_moves {I:ℕ}(L:Fin I→Op SU.Slot)(V:ℕ→ Picture I → Picture I →ℂ)(A:Picture I→Picture I→ℂ)(h:∀ i j,Tendsto (fun m=> V m i j) atTop (𝓝 (A i j))) :
    Tendsto (fun m=> spinFilm I L (V m)) atTop (𝓝 (spinFilm I L A)):= tendsto_finsetSum _ (fun _ _=> (offer_v _ _ h _).const_mul _)
-- uniform price film shelf. compactness for fixed arity -- requires no height thresholds
lemma spin_shelf (A:ℝ)(χ:swatches n): ∃ C:ℝ,0≤C∧∀ p:Picture n→Picture n →ℂ,(∀ i j, ‖p i j‖≤A)→ ‖spinFilm n (fun i=>walkC (tintM (χ i))) p‖ ≤ C:=by
 let Y:= Picture n→ Picture n→ℂ; let x:=Metric.closedBall (0:Y) |A|
 let f(p:Y):=spinFilm n (fun i=>walkC (tintM (χ i))) p
 have he:Continuous f:= continuous_iff_seqContinuous.mpr (fun P q h=> spin_moves _ _ _ (fun i j=> by
    have he:Continuous (fun x:Y=> x i j):= (continuous_apply j).comp (continuous_apply i); exact he.continuousAt.tendsto.comp h))
 obtain ⟨C,p⟩:= (isCompact_closedBall (0:Y) |A|).exists_bound_of_continuousOn he.continuousOn
 refine ⟨|C|,abs_nonneg _,fun q K=> (p q ?_).trans (le_abs_self _)⟩
 rw [mem_closedBall,dist_zero_right]; exact (pi_norm_le_iff_of_nonneg (abs_nonneg A)).mpr fun i=> (pi_norm_le_iff_of_nonneg (abs_nonneg A)).mpr fun j=> (K i j).trans (le_abs_self _)

lemma brush_price(x:fibers n→ℝ){A H:ℝ}(p:∀ i,‖P i‖≤ A)(h:∀ i,‖x i‖≤H)(q:0≤H): ‖brush P x‖≤ (Fintype.card (swatches n):ℝ)*(H^n*A):=by
 apply finiteBound; intro i; rw [norm_mul]; exact mul_le_mul (propCost _ (fun i=> by rw [Complex.norm_real]; apply h) q) (p i) (norm_nonneg _) (pow_nonneg q _)
lemma brush_diff(x y:fibers n→ℝ){A H e:ℝ}(p:∀ i,‖P i‖≤ A)(h:∀ i,‖x i‖≤H)(h':∀ i,‖y i‖≤H)(k:∀ i,‖x i-y i‖≤e)(q:0≤H)(t:0≤e): ‖brush P x-brush P y‖≤ (Fintype.card (swatches n):ℝ)*(n*e*H^(n-1)*A):= by
 unfold brush; rw [←sum_sub_distrib]; apply finiteBound; intro i
 rw [←sub_mul,norm_mul]; refine mul_le_mul (propCompare _ _ (fun j=>by rw [Complex.norm_real]; apply h) (fun j=>by rw [Complex.norm_real]; apply h') (fun a=> ?_) q t) (p i) (norm_nonneg _) (by positivity)
 rw [←Complex.ofReal_sub,Complex.norm_real]; apply k
lemma brush_smooth : ContDiff ℝ ω (brush P):=by
 unfold brush; apply ContDiff.sum; intro i _; change ContDiff ℝ ω (fun x:fibers n→ℝ=> (∏ j, Complex.ofRealCLM (x (j,i j)))*P i); fun_prop

#print axioms brush_smooth
#print axioms spin_shelf
#print axioms brush_life
#print axioms noble_photo
end Hearth
end YM.CF.Hiro
