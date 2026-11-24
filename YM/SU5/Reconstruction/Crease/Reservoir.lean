import YM.SU5.Reconstruction.Crease.House
import YM.SU5.Reconstruction.Crease.Sensor
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.BridgeClub
open Function Set Filter MeasureTheory Spectral Analysis Metric ContinuousLinearMap Picket CrossedFrame Anvil
open scoped BigOperators Topology InnerProductSpace ComplexOrder
variable {H K D:Hilbert}(C:Clasp K H D)(J:Flash H)(B:Flash D)
local notation "P" => C.plume
local notation "R" => C.shadow
-- no unjustified subsequence.Latch affine & graph weak receipt. Note J on H uses θ_perp, B on D uses θ_other
variable {ι:Type*}(q:Filter ι)[NeBot q]
lemma press (x y : H)(u v: ι→H)(a:ι→ D) (k:ι→ D.Op) (e:∀ n, C.Latch (u n) (a n))(h:∀ n, C.Latch (v n) (k n (B.f (a n)))) (p:∀ s t:K, inner ℂ (J.f (C.l s)) (C.l t)= inner ℂ (B.f (C.r s)) (C.r t))
   (r:∀ z: H,Tendsto (fun i=>inner ℂ z (u i)) q (𝓝 (inner ℂ z x))) (b:∀ z:H,Tendsto (fun i=>inner ℂ z (v i)) q (𝓝 (inner ℂ z y))) (U:ℝ) (bU:∀ i,‖a i‖ ≤U) (sp:∀ z:D,Tendsto (fun i=> star (k i) z) q (𝓝 z)): P (J.f y)= R x:=by
 have lp (z:D): Tendsto (fun i=> inner ℂ z (B.f (k i (B.f (a i))))- inner ℂ z (a i)) q (𝓝 0):= by
   let H'(i:ι):= star (k i) (B.f z)- B.f z
   have hx(i): inner ℂ z (B.f (k i (B.f (a i))))-inner ℂ z (a i)= inner ℂ (B.f (a i)) (H' i):= by
       have hb : inner ℂ z (B.f (k i (B.f (a i))))= inner ℂ (B.f (a i)) ((k i).adjoint (B.f z)):= by
          calc
            _ = inner ℂ (k i (B.f (a i))) (B.f z):= by nth_rw 1 [← B.twice z]; rw [B.light]
            _ = _:= (adjoint_inner_right (k i) (B.f (a i)) (B.f z)).symm
       rw [hb,← B.light (a i) z]; unfold H'; rw [inner_sub_right]; rfl
   have ht:Tendsto H' q (𝓝 0):=by simpa [H'] using (sp (B.f z)).sub (tendsto_const_nhds (x:=B.f z))
   simp_rw [hx]; apply squeeze_zero_norm' (Eventually.of_forall (fun i=> (norm_inner_le_norm ..).trans (mul_le_mul_of_nonneg_right (le_trans (B.bill (a i)).le (bU i)) (norm_nonneg (H' i)))));
   simpa using ht.norm.const_mul U
 have ht(T:H): Tendsto (fun i=>inner ℂ T (J.f (v i))) q (𝓝 (inner ℂ T (J.f y))):= by
    have he(y:H): inner ℂ T (J.f y)=star (inner ℂ (J.f T) y):=by
       conv_lhs=> lhs; rw [← J.twice T]; -- layout
       exact (J.light (J.f T) y).trans (inner_conj_symm y _).symm
    simp_rw [he]; exact (b _).star
 apply ext_inner_left ℂ; intro z
 have hm(i):inner ℂ z (R (u i))-inner ℂ z (P (J.f (v i))) = inner ℂ (C.r (C.l.adjoint z)) (a i)- inner ℂ (C.r (C.l.adjoint z)) (B.f (k i (B.f (a i)))):=by
   obtain ⟨s,p',f⟩:=e i; obtain ⟨t,f',q'⟩:= h i
   rw [←p', ← f',←q',← f]; rw [C.warmer,←adjoint_inner_left, adjoint_inner_right]
   rw [← Clasp.through_self _ C.plume_self];
   rw [C.plume_graph z]
   have hh:= congrArg (fun t:ℂ=>star t) (p t (C.l.adjoint z)); simp only [Complex.star_def,inner_conj_symm] at hh; rw [hh]

 apply Eq.symm; apply sub_eq_zero.mp
 have he : Tendsto (fun i=> inner ℂ z (R (u i))-inner ℂ z (P (J.f (v i)))) q (𝓝 0):=by
    have hk:=(lp (C.r (C.l.adjoint z))).neg; rw [neg_zero] at hk; simp_rw [hm]; simpa only [neg_sub] using hk -- reverse rewrite direction?
 refine tendsto_nhds_unique ((?_:Tendsto (fun i=>inner ℂ z (R (u i))) q (𝓝 (inner ℂ z (R x)))).sub (?_: Tendsto (fun i=>inner ℂ z (P (J.f (v i)))) q (𝓝 (inner ℂ z (P (J.f y)))))) he
 all_goals first | (simp_rw [← Clasp.through_self _ C.plume_self]; exact ht _) | (simp_rw [←Clasp.through_self _ C.shadow_self]; exact r _)
end YM.BridgeClub
