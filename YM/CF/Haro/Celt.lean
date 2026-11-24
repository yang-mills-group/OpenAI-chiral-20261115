import YM.CF.Haro.Wind
set_option autoImplicit false
set_option maxHeartbeats 500000
set_option synthInstance.maxSize 24000
noncomputable section
namespace YM.CF.Haro
open Function Filter Metric Fir Lattice Laurent Next.Free Bloch Finset Lat Stationary Rush Cube Scroll SU Drapes Fir Peaks Dial Paige Brace Vault Fock Tulip Font Spire Nacre Ember Pec
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix Matrix.Norms.L2Operator Kronecker MatrixOrder Classical
attribute [local instance] opCStarAlgebra
open Tap Hake Urn Yaw Levier Proa Rill
variable {c f:Side}(j m:ℕ)(e:Even j)(h:2 ≤ j)
variable (G:Ratio c f)(ho:Odd G.count.val)
open Branch Laic
variable {t:ℝ}(Y: cro G t)(W: Meter TailB G t)(V: Meter Grave G t)
open Skye Precision
open Jet
variable {E:Type}[NormedAddCommGroup E][NormedSpace ℝ E]{z:E}
lemma chill_d (p:0<t): ball (1:Urn.Co (N:=c) (P:=f)) t⊆ cro G t:=by
 let X:= (1: Nom c f); have hx:JointB G X t:=by
    refine ⟨guard0 p.le,guard0 p.le,fun i=>?_⟩; have ht(i:Site (More f))(j:Walk): travel X.1 i j=1:=by induction j generalizing i with|nil=>rfl|cons a b ih=>rw [travel,ih]; simp [X,Step.read]
    rw [ht]; exact (show ‖brand 1-brand 1‖≤ t from by simp [p.le]) -- tune space
 intro u v; have hv(u: Urn.Co (N:=c) (P:=f)):u.1-(1:Coil c f)=(u-1).1:=rfl; rw [mem_ball_iff_norm] at v
 refine ⟨⟨X,hx,?_⟩,⟨1,guard0 p.le,?_⟩⟩; swap; · rw [profile_trivial]; exact (norm_snd_le (u-1)).trans_lt v
 rw [show unionP X=1 from by simp [X,unionP,profile_trivial]]; exact (norm_fst_le (u-1)).trans_lt v
-- use arbitrary card.Y. true collar Σ.V# field interpolation along ball.Construct VALUE through K.L.
lemma shakesH {F:Type}[NormedAddCommGroup F][NormedSpace ℝ F](T:E→ F)(y:E)(b:ℝ)(n:ℕ)(h:Shake T y b n)(V:F):Shake (fun i=> T i - V) y b n:=by
 let f(i:E):=V; have hp:ContDiffAt ℝ (↑n) f y:= contDiffAt_const; refine ⟨h.price,h.smooth.sub hp,fun i u v=>?_⟩
 change ‖iteratedFDeriv ℝ i (T-f) y‖≤_; rw [iteratedFDeriv_sub_apply (h.smooth.of_le (Nat.cast_le.mpr v)) (hp.of_le (Nat.cast_le.mpr v))]; unfold f; rw [iteratedFDeriv_const_of_ne (ne_of_gt u), Pi.zero_apply,sub_zero]; exact h.bill i u v
abbrev lamQ {E:Type}[NormedAddCommGroup E][NormedSpace ℝ E](b z:ℝ)(C:ℝ)(n:ℕ): Prop:=∀ U:E→ SU.group.El,∀ y:E,Rill.Tender U y b n→∀ i:Bool,Shake (fun v=>if i then brand (U v) else star (brand (U v))) y (C*b) n
def NearS (S:Side)(Z:Support (More S))(T:Pane S)(v:ℝ):Prop:=∀ i:Pressure.Bond (More S),ends i⊆ Z→‖(Tulip.profile T i)-1‖ ≤ v
lemma highB (N:Side)(S:Support (More N))(A:Pane N)(v:ℝ)(hp:0 ≤ v)(h:NearS N S A v): ‖Rill.twin (Tulip.profile A) S 1-1‖ ≤ v:=by
 apply (pi_norm_le_iff_of_nonneg hp).mpr; intro i; unfold Rill.twin; simp only [Pi.sub_apply]; split
 · next ht=> exact h i (insert_subset (mem_filter.mp ht).2.1 (singleton_subset_iff.mpr (mem_filter.mp ht).2.2))
 rw [sub_self,norm_zero]; exact hp
variable {v b t' k a:ℝ} (U:E→ Rill.Arch G t) {m}
variable (D:Support (More f))
abbrev sumL(m:ℕ)(t:ℝ):= ((1+(2:ℝ)^m/(t/2))^m)
omit W
lemma heart (p:0<t)(g:0 < m)(F:cro G t→ Op (Iota G))(u r:Bool)(W:Toll (Iota G))(q:Suite (badge _) (pinH G t u) (pinH G t r) D W F)(K:ℝ)(hp:0 ≤ b)(pv:0 ≤ v)(h1:0≤K)(tF:lamQ (E:=E) b t K m)(Y:cro G t)(ht:Y.val=1) (hv:v ≤ t/2)(hW:K*b≤1)
 (z1:NearS f D (U z).val.1.1 v)(z2:NearS c (cloudG G D) (U z).val.1.2 v)(z3:NearS f D (U z).val.2 v)(t1:∀ i:Pressure.Bond (More f),Skye.ends i⊆ D → Rill.Tender (fun y=> (U y).val.1.1 i) z b m ∧ Rill.Tender (fun y=>(U y).val.2 i) z b m)(t2:∀ i:Pressure.Bond (More c),Skye.ends i⊆ cloudG G D → Rill.Tender (fun y=> (U y).val.1.2 i) z b m)(i j:Iota G) : Allows m (fun y=> F (bring p (U y)) i j-F Y i j) z (W i j*sumL m t*(Shake.quota m*(K*b)+v)):=by
 let T'(y:E):= (U y).val.1; let V(y:E):=(U y).val.2; let Φ(y:E):Urn.Co (N:=c) (P:=f):=((Rill.twin (Tulip.profile (T' y).1) D 1,Rill.twin (Tulip.profile (T' y).2) (cloudG G D) 1), Rill.twin (Tulip.profile (V y)) D 1)
 have hz: ‖Φ z-1‖≤ v:=by rw [Prod.norm_def]; refine max_le ?_ (highB f D _ v pv z3); rw [Prod.norm_def]; exact max_le (highB f D _ v pv z1) (highB c _ _ v pv z2)
 let f:= fun x=> F x i j; have hQ: 0 ≤ W i j:= q.nonn ..
 let C:= W i j*sumL m t; have HH(y:Urn.Co (N:=c) (P:=_))(h:y ∈ closedBall (1:Urn.Co (N:=c) (P:=_)) v): Allows m (Jet.equalizer f) y C:=by
    refine allows_looks (q.fuel i j) (q.expo i j).connected ?_ (half_pos p) m (q.expo i j).bounded
    intro u k; apply chill_d G p; change dist _ _<_; change dist u y<_ at k; change dist _ _ ≤ _ at h; exact (dist_triangle u y _).trans_lt (by linarith)
 have hy:= HH (Φ z) (show Φ z ∈ closedBall 1 v from mem_closedBall_iff_norm.mpr hz)
 have hΦ :Shake Φ z (K*b) m:=by
    have hh {n:Side}(A:E→Pane n)(S:Support (More n))(h:∀ i:Pressure.Bond (More n),Skye.ends i ⊆ S→ Rill.Tender (fun y=> A y i) z b m): Shake (fun y=>Rill.twin (Tulip.profile (A y)) S 1) z (K*b) m:=by
       apply Shake.various _ (by positivity); intro j; apply Shake.various _ (by positivity); intro z'; unfold Rill.twin; split
       · next t=> exact tF _ z (h j (insert_subset (mem_filter.mp t).2.1 (singleton_subset_iff.mpr (mem_filter.mp t).2.2))) z'
       exact (Shake.holds _).bag (by positivity)
    exact ((hh (fun v=>(T' v).1) _ (fun i u=>(t1 i u).1)).team (hh (fun v=>(T' v).2) _ t2)).team (hh _ _ (fun i u=>(t1 i u).2))
 have hp0: Φ z∈ball 1 t:= mem_ball_iff_norm.mpr (hz.trans_lt (hv.trans_lt (half_lt_self p)))
 let A:= (Jet.equalizer f) ∘ Φ; have heq : A=ᶠ[𝓝 z] fun y=> F (bring p (U y)) i j:=by
    filter_upwards [hΦ.smooth.continuousAt.eventually (isOpen_ball.mem_nhds hp0)] with y v; unfold A Jet.equalizer Function.comp; dsimp only; have hp':Φ y∈ cro G t:=chill_d G p v; rw [dif_pos hp']; apply sub_eq_zero.mp; apply norm_le_zero_iff.mp; have hu:=(q.expo i j).variation ⟨_,hp'⟩ (bring p (U y)); rw [show (hall G t).eval D ⟨_,hp'⟩ (bring p (U y))=0 from ?_,mul_zero] at hu; exact hu
    change deal _ D (Φ y).1 _/ _ + _/_=_; dsimp only [Φ, deal,unionP,bring]; unfold T' V; simp [tipper] -- tune
 have hs:= shakesH _ z _ m ((hΦ.thorn (Shake.pick hy) hW).same heq) (F Y i j); have hc:0 ≤ C:= hy.nonneg
 have ht' : ‖A z - F Y i j‖ ≤ C*v:=by
    have hp := Convex.norm_image_sub_le_of_norm_fderiv_le (f:=Jet.equalizer f) (C:=C) (fun i hi=>(HH i hi).smooth.differentiableAt (by simp [ne_of_gt g])) (fun x hx=> (norm_iteratedFDeriv_one (𝕜:=ℝ) _).symm.trans_le ((HH x hx).norm_le 1 g)) (convex_closedBall 1 v) (mem_closedBall_self pv) (mem_closedBall_iff_norm.mpr hz)
    have hu:Jet.equalizer f Y.val=F Y i j:=by unfold Jet.equalizer; rw [dif_pos Y.property]
    rw [ht] at hu; rw [←hu]; exact hp.trans (mul_le_mul_of_nonneg_left hz hc)
 rw [heq.self_of_nhds] at ht'; have hg:= (hs.paid ht'); apply hg.mono; change max (Shake.quota m * (C*(K*b))) (C*v) ≤ C*_ ; rw [mul_add]; apply max_le; apply le_trans _ (le_add_of_nonneg_right (mul_nonneg hc pv)); exact le_of_eq (by ring); exact le_add_of_nonneg_left (mul_nonneg hc (mul_nonneg (Shake.quake m) hΦ.price))
end YM.CF.Haro
