import SatinThinMaze
import Velour.Crepe.Dye
/-! # Buying up countably many families of operator caps. -/
set_option autoImplicit false
set_option maxRecDepth 2000
noncomputable section
namespace YM.Velour
open SatinNucleus Function TopologicalSpace Filter Set Metric
open scoped Topology InnerProductSpace BigOperators NNReal
/-- Eventually bounded strong* (along sequence). -/
structure Gleams (H:Hilbert) (f:ℕ→H.Op) (g:H.Op) : Prop where
 bought : ∃B:ℝ, ∀ᶠ i in atTop, ‖f i‖≤B
 gaze(y:H) : Tendsto (fun i=> f i y) atTop (𝓝 (g y))
 turn(y:H) : Tendsto (fun i=>star (f i) y) atTop (𝓝 (star g y))


variable {H:Hilbert}
private lemma converges (X:ℕ→H.Op)(D:ℕ→H)(hd:DenseRange D)
   {B:ℝ} (b:∀ᶠ i in atTop, ‖X i‖≤B)(v:∀k, ∃y, Tendsto (fun i=>X i (D k)) atTop (𝓝 y))(x:H):
   ∃y, Tendsto (fun i=> X i x) atTop (𝓝 y):=by
 obtain ⟨i,t⟩:=b.exists
 have hB:0≤B:=(norm_nonneg _).trans t
 apply cauchySeq_tendsto_of_complete
 rw [Metric.cauchySeq_iff]
 intro ε e
 have T :0< B+1:=by linarith
 obtain ⟨_,⟨k,rfl⟩,p⟩:= Metric.mem_closure_iff.mp (hd x) (ε/4/(B+1)) (by positivity)
 have q:∀ᶠ i in atTop, dist (X i x) (X i (D k))<ε/4:=by
   rw [dist_eq_norm,lt_div_iff₀ T] at p
   refine b.mono fun i r=> ?_
   rw [dist_eq_norm,←map_sub]
   exact ((X i).le_opNorm ..).trans_lt ((mul_comm ..).trans_lt
     (lt_of_le_of_lt (mul_le_mul_of_nonneg_left
        (r.trans (by linarith:B ≤ B+1)) (norm_nonneg _)) p))
 obtain ⟨y,g⟩:=v k


 obtain ⟨n,hn⟩:=eventually_atTop.mp (q.and (Metric.tendsto_nhds.mp g (ε/4) (by positivity)))
 refine ⟨n,fun i t j u=> ?_⟩
 have h{m:ℕ}(r:n ≤ m): dist (X m x) y< ε/2:=by
    obtain ⟨h,g⟩:=hn m r
    linarith only [h,g,dist_triangle (X m x) (X m (D k)) y]
 linarith only [h t,h u,dist_triangle_right (X i x) (X j x) y]

private lemma smoothLimit (X:ℕ→H.Op){B:ℝ}(b:∀ᶠ i in atTop, ‖X i‖≤B)
    (q:∀ x:H, ∃ y,Tendsto (fun i=>X i x) atTop (𝓝 y)):
   ∃Y:H.Op, ∀ x:H,Tendsto (fun i=>X i x) atTop (𝓝 (Y x)):=by
 choose y h using q
 let f:H →ₗ[ℂ] H:= {
    toFun:=y
    map_add':=fun x z=> tendsto_nhds_unique (h _) (((h x).add (h z)).congr (fun i=>(map_add _ _ _).symm))
    map_smul':=fun c x=> tendsto_nhds_unique (h _) (((h x).const_smul c).congr (fun i=>(map_smul _ _ _).symm))
 }
 refine ⟨f.mkContinuous B (fun x=>le_of_tendsto ((h x).norm) ?_),h⟩
 refine b.mono fun i r=>le_trans ((X i).le_opNorm ..) (mul_le_mul_of_nonneg_right r (norm_nonneg _))



lemma whole (X:ℕ→H.Op)(D:ℕ→H)(hd:DenseRange D)
   {B:ℝ} (b:∀ᶠ i in atTop, ‖X i‖≤B)(v:∀k, ∃y, Tendsto (fun i=>X i (D k)) atTop (𝓝 y))
   (v':∀k, ∃y, Tendsto (fun i=> star (X i) (D k)) atTop (𝓝 y)):
   ∃ Y,Gleams H X Y:=by
 obtain ⟨Y,h⟩:= smoothLimit (H:=H) X b (converges (H:=H) X D hd b v)
 refine ⟨Y,⟨B,b⟩,h,fun x=>?_⟩
 have hb:∀ᶠ i in atTop, ‖star (X i)‖ ≤B:= by simpa only [norm_star] using b
 obtain ⟨y,t⟩:=converges (H:=H) (fun i=>star (X i)) D hd hb v' x
 suffices he: y= star Y x by rwa [←he]
 apply ext_inner_left ℂ
 intro z
 have hg:= (tendsto_const_nhds (x:=z)).inner (𝕜:=ℂ) t
 have hx:= (h z).inner (𝕜:=ℂ) (tendsto_const_nhds (x:=x))
 have k(Z:H.Op): inner ℂ z (star Z x)=inner ℂ (Z z) x:= ContinuousLinearMap.adjoint_inner_right ..
 rw [k]
 exact tendsto_nhds_unique hg (hx.congr fun i=>(k _).symm)


def pool {G:Type*}[NormedAddCommGroup G][NormedSpace ℂ G] (q:ℕ → Coalition)(f:ℕ→G)(n:ℕ):=
    ∑i∈(q n).voters, ((q n).w i:ℂ) • f (n+i) -- ℂ?
lemma pool_star(q:ℕ → Coalition)(f:ℕ→H.Op)(n:ℕ):
   star (pool q f n)=pool q (fun i=>star (f i)) n:=by
 unfold pool; rw [star_sum]
 simp only [star_smul,Complex.star_def,Complex.conj_ofReal]
lemma pool_act(q:ℕ → Coalition)(f:ℕ→H.Op)(n:ℕ)(x:H):
   pool q f n x= pool q (fun i=>f i x) n:=by
 unfold pool; rw [sum_apply]
 rfl
lemma pool_exp {G:Type*}[NormedAddCommGroup G][NormedSpace ℂ G] (q:ℕ → Coalition)(f:ℕ→G)
    {B:ℝ}(b:∀ᶠ i in atTop, ‖f i‖ ≤ B):
   ∀ᶠ i in atTop, ‖pool q f i‖ ≤ B:=by
   obtain ⟨n,h⟩:=eventually_atTop.mp b
   refine (eventually_ge_atTop n).mono fun i e=> ?_
   refine (norm_sum_le ..).trans ((Finset.sum_le_sum (g:=fun m=> (q i).w m * B) (fun m z=>?_)).trans ?_)
   swap
   · rw [←Finset.sum_mul,(q i).pledges,one_mul]
   rw [norm_smul,Complex.norm_real,Real.norm_of_nonneg ((q i).signed m z)]
   exact mul_le_mul_of_nonneg_left (h _ (by omega)) ((q i).signed m z)


theorem pooled {I:Type} [Nonempty I] [Countable I](J:I→Hilbert)
   [∀i, SeparableSpace (J i).space]
   (T:∀ i: I, ℕ→(J i).Op) (b:∀i,∃B:ℝ, ∀ᶠ n:ℕ in atTop, ‖T i n‖≤ B):
   ∃q:ℕ → Coalition, ∀ i, ∃ Y:(J i).Op, Gleams (J i) (pool q (T i)) Y:=by
 obtain ⟨g,u⟩:=exists_surjective_nat (I × Bool × ℕ)
 let x(i:I):=denseSeq (J i).space
 let F(i:I)(d:Bool)(n:ℕ)(m:ℕ): J i:=(if d then star (T i m) else T i m) (x i n)
 have h(i:I)(d:Bool)(n:ℕ):∃B:ℝ,∀ᶠ m in atTop, ‖F i d n m‖ ≤ B:=by
   obtain ⟨B,h⟩:=b i; refine ⟨B*‖x i n‖,h.mono ?_⟩
   intro m w; refine le_trans (ContinuousLinearMap.le_opNorm ..) (mul_le_mul_of_nonneg_right ?_ (norm_nonneg _))
   split; rwa [norm_star]; exact w
 let f(t:ℕ):ℕ→J (g t).1:=F (g t).1 (g t).2.1 (g t).2.2
 obtain ⟨q,e⟩:= Coalitions (fun t=> J (g t).1) f (fun t=>h _ _ _)


 have p(s:I×Bool×ℕ):∃y,Tendsto (pool q (F s.1 s.2.1 s.2.2)) atTop (𝓝 y):=by
   obtain ⟨k,rfl⟩:= u s; exact e k
 refine ⟨q,fun i=>?_⟩
 obtain ⟨B,y⟩:=b i
 refine whole (pool q (T i)) (x i) (denseRange_denseSeq _) (pool_exp q (T i) y) (fun k=>?_) (fun k=>?_)
 · obtain ⟨a,t⟩:=p (i,false,k)
   exact ⟨a,t.congr fun m=>(pool_act q (T i) m (x i k)).symm⟩
 obtain ⟨a,t⟩:=p (i,true,k)
 refine ⟨a,t.congr fun m=>?_⟩
 rw [pool_star,pool_act]; rfl
end YM.Velour

