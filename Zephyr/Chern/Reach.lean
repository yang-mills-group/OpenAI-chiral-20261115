import Zephyr.Chern.Coats
import Zephyr.Chern.Decay
import Zephyr.Chern.Glaze
import Zephyr.Chern.Tug
import Zephyr.Chern.Port
set_option autoImplicit false
noncomputable section
namespace Zephyr.Chern

open YM YM.Lattice Filter Topology YM.CF YM.CF.Tulip YM.CF.Cube YM.CF.Rush YM.Laurent


/-- No conditions on how Male changes along the regulator net. -/
structure Cross {κ : Type*} (s:ℕ) (L:Filter κ) where
  N:κ→Side
  M:κ→Male
  grow:Tendsto (fun u=>(N u).val) L atTop
  yes:1≤s

abbrev Stack := Three (Coats IS)
def tip (p:Stack) (x:Cover) (i j:IS): Three ℂ :=fun k=>seam x (p k) i j

variable {κ:Type*}{s:ℕ}{L:Filter κ}

namespace Cross
variable (X:Cross s L)
abbrev oil (u:κ) := funde s (X.M u) (X.N u)
abbrev test (x:Cover) (i j:IS)(k:Fin 3)(u:κ) : ℂ:=
  tuft (X.oil u) (stream _) (-x) 0 i j k

lemma later (n:ℕ): ∀ᶠ u in L, n≤(X.N u).val := X.grow.eventually (eventually_ge_atTop _)
lemma later' (n:ℕ): ∀ᶠ u in L, n<(X.N u).val := X.grow.eventually (eventually_gt_atTop _)

def Relax (p:Stack) :=∀ x i j k, Tendsto (X.test x i j k) L (𝓝 (tip p x i j k))

lemma oils : ∃ a r e :ℝ, 0<a ∧ 0<r ∧ 0<e ∧ ∀ᶠ u in L,Solo a r (X.oil u) e:=by
  obtain ⟨a,r,e,h,n,p,v,k⟩:=funde_s s X.yes
  exact ⟨a,r,e,h,n,p,(X.later v).mono (fun _ t=>k _ _ t)⟩

lemma apply_down : ∀ᶠ u in L, Down (X.oil u):=by
  obtain ⟨n,q⟩:=down s X.yes
  exact (X.later n).mono (fun _ h=>q _ h _)

lemma apply_mends:∀ᶠ u in L,Mended (X.oil u):=by
  obtain ⟨n,q⟩:=mends_limit s X.yes
  exact (X.later n).mono (fun _ h=>q h _)

lemma apply_lift (z:Cover):∀ᶠ u in L, lift (wrap (X.N u) z)=z:=
  (X.later' _).mono (fun _ h=>close_wrap _ h)

lemma builds {U:Ultrafilter κ} (Y:Cross s (U:Filter κ)): ∃ p,Y.Relax p := by
  obtain ⟨a,r,e,h,n,v,S⟩:=Y.oils
  obtain ⟨W,⟨w⟩⟩:= oily h v 16
  let f i j k := fun u x => if lift (wrap (Y.N u) x)=x then Y.test x i j k u else 0
  have t : ∀ i j k,∃ q:Silk,∀ x,Tendsto (Y.test x i j k) U (𝓝 (q.co x)) := by
    intro i j k
    have b:0<W*r:=mul_pos w.bound n
    have hc :Swift U (f i j k):= by
      apply swift_exp (a:=a/4) (by positivity) (W*r)
      filter_upwards [S] with u hu x
      unfold f
      split
      · exact tuft_fall hu w _ (by assumption) ..
      rw [norm_zero]; exact mul_nonneg b.le (Real.exp_pos ..).le
    obtain ⟨q,g⟩:=hc.arrive
    refine ⟨q,fun x=> (g.co x).congr' ((Y.apply_lift x).mono fun u y=>if_pos y)⟩
  choose p hp using t
  exact ⟨fun k=>Matrix.of fun i j=>p i j k, fun x i j k=>hp i j k x⟩
end Cross

lemma splice_limit {u v : κ→Three ℂ} {x y:Three ℂ}
    (hu:∀ k,Tendsto (fun i=>u i k) L (𝓝 (x k)))(hv:∀ k,Tendsto (fun i=>v i k) L (𝓝 (y k)))
    (k:Fin 3):Tendsto (fun i=>splice (u i) (v i) k) L (𝓝 (splice x y k)):=by
  have t m n:= (hu m).mul (hv n)
  fin_cases k
  · exact t 0 0
  · exact (t 0 1).add (t 1 0)
  exact ((t 0 2).add (t 2 0)).add (t 1 1)

lemma splice_norm {x y:Three ℂ}{u v:ℝ}(hu:∀ k,‖x k‖≤u)(hv:∀ k,‖y k‖≤v)(k:Fin 3) :
    ‖splice x y k‖≤3*(u*v):=by
  have b:= (norm_nonneg _).trans (hu 0)
  have w:=mul_nonneg b ((norm_nonneg _).trans (hv 0))
  have h m n: ‖x m*y n‖≤u*v:=by
    rw [norm_mul]; exact mul_le_mul (hu _) (hv _) (norm_nonneg _) b
  fin_cases k
  · exact (h 0 0).trans (by linarith)
  · exact (norm_add_le ..).trans ((add_le_add (h 0 1) (h 1 0)).trans (by linarith))
  exact (norm_add_le ..).trans ((add_le_add
    ((norm_add_le ..).trans (add_le_add (h 0 2) (h 2 0))) (h 1 1)).trans (by ring_nf;exact le_rfl))

lemma makes_small {u:κ→ℂ} (a b:ℝ) (ha:0<a)
    (h:∀ m:ℕ,∀ᶠ i in L, ‖u i‖≤ b*Real.exp (-a*m)) : Tendsto u L (𝓝 0) := by
  have w:Tendsto (fun m:ℕ => b*Real.exp (-a*m)) atTop (𝓝 (b*0)):=by
    simp only [neg_mul]
    exact (Real.tendsto_exp_neg_atTop_nhds_zero.comp (Tendsto.const_mul_atTop ha
      tendsto_natCast_atTop_atTop)).const_mul b
  rw [mul_zero] at w
  apply Metric.tendsto_nhds.mpr
  intro c e
  obtain ⟨m,k⟩:=(w.eventually (gt_mem_nhds e)).exists
  filter_upwards [h m] with i hi
  rw [dist_zero_right];exact hi.trans_lt k

def pulseJet (y z:Cover) (i:IS) := ringlet (wgt i.2*(2*flux y z:ℝ))

namespace Cross

variable {X:Cross s L} {p:Stack}
lemma Relax.pulse (h:X.Relax p)(y z:Cover)(i j:IS)(k:Fin 3):
    Tendsto (fun u=>tuft (X.oil u) (stream _) (-y-z) (-z) i j k) L
      (𝓝 (splice (pulseJet y z i) (tip p y i j) k)) := by
  let g (A:(N:Side)→StemA N) (v w:Cover):=fun u=>tuft (X.oil u) (A (X.N u)) v w i j k
  have hd: g stream (-y-z) (-z) =ᶠ[L] g (fun N=>transA N z) (-y) 0 :=
    X.apply_down.mono fun u hu=>congrFun (hu z y i j) k
  obtain ⟨a,r,e,b,c,f,jh⟩:=X.oils
  have hz : Tendsto (g (fun N=>glazed N z) (-y) 0) L
      (𝓝 (splice (pulseJet y z i) (tip p y i j) k)):= by
    refine (splice_limit (fun _=> tendsto_const_nhds)
      (u:=fun _=>pulseJet y z i)
      (v:=fun u=>tuft (X.oil u) (stream _) (-y) 0 i j)
      (h y i j) k).congr' ?_
    filter_upwards [jh,X.later' (2*size y)] with u hu lu
    exact congrFun (tuft_glazed hu f z y lu i j).symm k
  have hp:Tendsto (fun u=>
    g (fun N=>transA N z) (-y) 0 u-g (fun N=>glazed N z) (-y) 0 u)
    L (𝓝 0):=by
    obtain ⟨W,⟨w⟩⟩:=oily b f (rim z)
    apply makes_small _ (2*(W*r)) (half_pos b)
    intro m
    filter_upwards [jh,X.later' (4*m+2*size z+1)] with u hu t
    rw [mul_assoc]
    exact tuft_fringe hu z y i j k m t w
  have e:=hp.add hz
  simp only [sub_add_cancel,zero_add] at e
  exact e.congr' hd.symm

def forge (p:Stack) (y z:Cover)(i j:IS) (k:Fin 3) : ℂ :=
  ∑ l:IS,splice (splice (pulseJet y z i) (tip p y i l)) (tip p z l j) k

lemma Relax.forge (h:X.Relax p)(x z:Cover)(i j:IS)(k:Fin 3):
    Tendsto (fun u=>due (X.oil u) x z i j k) L (𝓝 (forge p (x-z) z i j k)):=by
  unfold due Cross.forge
  apply tendsto_finsetSum
  intro l _
  have f:=fun m=>h.pulse (x-z) z i l m
  rw [show -(x-z)-z= -x by abel] at f
  exact splice_limit f (v:=fun u=>tuft (X.oil u) (stream _) (-z) 0 l j)
    (h z l j) k

lemma dominates (X:Cross s L) (x:Cover):
    ∃ b:Cover→ℝ,Summable b ∧ ∀ᶠ u in L, ∀ z i j k,
      ‖(if lift (wrap (X.N u) z)=z then due (X.oil u) x z i j k else 0)‖≤ b z:=by
  obtain ⟨a,r,e,h,c,p,S⟩:=X.oils
  obtain ⟨W,⟨w⟩⟩:=oily h p 16
  obtain ⟨Y,q,g⟩:=tuft_far_price (r:=r) x h p
  let b :ℝ:=Fintype.card IS* (3*((Y*r)*(W*r)))
  have b0:0≤b:=by have := w.bound;unfold b; positivity
  refine ⟨fun z=>b*Real.exp (-(a/4)*size z),
    (Width.compactPay (α:=Axis) (a/4) (by positivity)).2.1.mul_left b, ?_⟩
  filter_upwards [S] with u hu z i j k
  by_cases t:lift (wrap (X.N u) z)=z
  case neg=>rw [if_neg t,norm_zero]; positivity
  rw [if_pos t]
  have h1(l k):‖tuft (X.oil u) (stream _) (-x) (-z) i l k‖ ≤ Y*r:=
    g _ _ hu z i l k
  have h2(l k):‖tuft (X.oil u) (stream _) (-z) 0 l j k‖ ≤ W*r *
      Real.exp (-(a/4)*size z):= tuft_fall hu w z t l j k
  have bound := fun l=>splice_norm (h1 l) (h2 l) k
  exact (norm_sum_le ..).trans ((Finset.sum_le_sum (fun l _=>bound l)).trans
    (le_of_eq (by rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ]; unfold b; ring)))

lemma Relax.hasSum [L.NeBot] (h:X.Relax p) (x:Cover)(i j:IS)(k:Fin 3):
    HasSum (fun z=> Cross.forge p (x-z) z i j k) (tip p x i j k):=by
  obtain ⟨b,hb,v⟩:=X.dominates x
  let g:= fun z=>Cross.forge p (x-z) z i j k
  let f:=fun u z=> if lift (wrap (X.N u) z)=z then due (X.oil u) x z i j k else 0
  have q z:Tendsto (fun u=>f u z) L (𝓝 (g z)):=
    (h.forge x z ..).congr' ((X.apply_lift z).mono fun _ p=>(if_pos p).symm)
  have w:Summable g:=hb.of_norm_bounded fun z=> le_of_tendsto
    (q z).norm (v.mono (fun _ a=>a z i j k))
  have a:=tendsto_tsum_of_dominated_convergence hb q
    (v.mono (fun _ v z=>v z i j k))
  have c:Tendsto (fun u=>∑' z,f u z) L (𝓝 (tip p x i j k)):=
    (h ..).congr' (X.apply_mends.mono fun _ hv=>hv ..)
  rw [tendsto_nhds_unique c a];exact w.hasSum

end Cross
