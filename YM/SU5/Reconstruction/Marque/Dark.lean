import YM.SU5.Reconstruction.Marque.Flight
import YM.SU5.Reconstruction.Crease.Keeper
set_option autoImplicit false
noncomputable section
namespace YM.Marque
open Function Set Filter Metric NormedSpace ContinuousLinearMap Complex BridgeClub CrossedFrame Picket Spectral Analysis Multiplier
open scoped ComplexOrder InnerProductSpace BigOperators Topology Classical Complex
variable {H D E K W:Hilbert} (Z:Clasp D H E) (F:Clasp K H W) {v:Wander H.space}{a:Bool}(p:Fleet v a)
local notation "P"=> Z.plume
local notation "Q"=> Z.shadow
local notation "P'"=> F.plume
local notation "Q'"=> F.shadow
variable {J L:Flash H}{Γ T:Set H.Op}{M N:Net H}{x y:H}(g:Club Z J M x Γ)(m:Club F L N y T)(z:Conveys v M N)(t:v x=y)
include p in
lemma reverserve (x y:H):inner ℂ (v⁻¹ x) y= Hue a (inner ℂ x (v y)):= by obtain ⟨w,rfl⟩:= v.surjective x; rw[wander_front,p.innerP,hue_duo]
local notation "k"=> (rain L*v*rain J)
include p g m z t
lemma Mara (x':H) : P' (k (Q x'))=Q' (v (P x')):= by
 let s (i:H):= P' (k (Q i)); let r (i:H):= Q' (v (P i));
 have hk:Fleet k a:= by rw [show k=k from rfl]; simpa using ((rainPrice J).times (p.times (rainPrice L))) -- order assoc
 refine g.economize {w:H|s w=r w} (isClosed_eq ((P').continuous.comp ((k).continuous.comp (Q).continuous)) ((Q').continuous.comp (v.continuous.comp (P).continuous))) ?_ ?_ ?_ ?_ x'
 · intro A e; change P' (k _)=Q' (v _); rw [g.pose A e,g.rePose A e];
   have h:= m.charge (p.Form A) ((z _ _ (p.arr A)).1 (g.pin e)); rw[← t,p.stars (p.arr A) x,p.arr _ _] at h
   rw [wander_mul,wander_mul,rain_at J,J.twice,rain_at L]; exact h
 · change P' (k (Q 0))=Q' (v (P 0)); rw [map_zero Q, map_zero P,hk.bases,p.bases,map_zero,map_zero] -- wander_mul simplify interferes
 · exact fun i (e:P' (k _)=Q' (v (P i))) u (h:P' (k _)=Q' (v (P u)))=> show P' (k (Q (i+u)))=Q' (v (P (i+u))) by rw [map_add Q,map_add P,hk.plus,p.plus,map_add,map_add,e,h] -- rw map_add accidental
 exact fun i (e:P' (k _)=Q' (v (P i))) c=> show P' (k (Q (c • i)))=Q' (v (P (c • i))) by rw[map_smul Q,map_smul P,hk.conj,p.conj,map_smul,map_smul,e]
lemma opposite (x':H): Q' (k (P x'))= P' (v (Q x')):= by
 let i:= k; have h(y':H):P (k⁻¹ (Q' y'))=Q (v⁻¹ (P' y')):= by
    have h':rain J*v⁻¹*rain L=k⁻¹:=by rw[mul_inv_rev,mul_inv_rev,rain_inv,rain_inv];group -- unfold notation error
    rw[←h']; exact Mara _ _ p.inv m g z.back (show v⁻¹ y= _ from (by rw [← t,wander_front])) y' -- collision y
 -- transfer via pairing
 apply ext_inner_left ℂ; intro b
 have hw:Fleet k a:=by simpa using (rainPrice J).times (p.times (rainPrice L))
 rw [← Clasp.through_self _ F.shadow_self,← Clasp.through_self _ F.plume_self]; apply Involutive.injective (hue_duo a); rw [← reverserve hw, ← reverserve p, ← Clasp.through_self _ Z.shadow_self, ← Clasp.through_self _ Z.plume_self,h b]
omit g m p z t
noncomputable def Cusp:=P-Q
include Z
lemma Cusp_self:IsSelfAdjoint (Cusp Z):= Z.plume_self.sub Z.shadow_self
lemma empties (x:H): Tendsto (fun n:ℕ=> ((Cusp Z)^n:H.Op) x) atTop (𝓝 0):= by
 let A:= Z.angle; let B:=(1-A:D.Op); let R:= A-B; let f:= Z.realF
 let U(s:ℝ) := s - (1-s)
 let V:= fun i=> (U (f i):ℂ); have he:Registers Z.motion V R:= by
    convert Z.angle_reads.sub ((Registers.one Z.motion).sub Z.angle_reads) using 1; ext1 i; dsimp[U,V,f]; push_cast; rfl -- tune
 have hv(n:ℕ)(x:D): (Cusp Z^n:H.Op) (Z.Left x)=Z.Left ((R^n:D.Op) x) := by
    induction n generalizing x with
    | zero=> simp
    | succ n e=> simp only [pow_succ,mul_apply_eq_comp]; have ht:Cusp Z (Z.Left x)=Z.Left (R x):= by rw [Cusp,sub_apply,(Club.pearlA ..).1,(Club.pearlA ..).2]; exact (map_sub ..).symm -- tune
                 rw [ht, e]
 obtain ⟨x,rfl⟩:=Z.Left.surjective x
 simp_rw [hv]; rw [←map_zero Z.Left]; apply (Z.Left.continuous.continuousAt.tendsto).comp (show Tendsto (fun n:ℕ=> (R^n:D.Op) x) atTop (𝓝 0) from ?_)
 have hp:(∀ᵐ y ∂(Z.motion.diagonal x), ‖V y‖ < 1) := (Z.inOpen x).mono fun y (p:f y∈ Ioo (0:ℝ) 1)=>by unfold V; rw [norm_real, Real.norm_eq_abs,abs_lt]; unfold U; constructor<;> linarith [p.1,p.2]
 apply Registers.tends atTop (fun n=> V^n) (fun n=> R^n) (Registers.none _) (fun i=> Registers.pow he i) x 1 (Eventually.of_forall fun n=>hp.mono fun y v=> ?_) (hp.mono fun y h=>?_) -- tune
 change ‖(V y)^n‖≤1; rw[norm_pow]; exact pow_le_one₀ (norm_nonneg _) v.le
 exact tendsto_pow_atTop_nhds_zero_of_norm_lt_one h
include g m p z t Z F
private lemma smash(w:H) : Cusp F (k (Cusp Z w)-v (Cusp Z w))=k w-v w:= by
 -- expand T * (??) ; sign check PTQ = -QTP implies C T C = T
 let D (x:H):= k x-v x
 have he(x:H):P' (D (Q x))= -(Q' (D (P x))):= by
    unfold D; rw [map_sub,map_sub,Mara _ _ p g m z t, ← opposite _ _ p g m z t]; abel
 have hx(w:H):P w+ Q w=w:= DFunLike.congr_fun Z.unites w
 have hy(w:H):P' w+Q' w=w:= DFunLike.congr_fun F.unites w
 have hk:Fleet k a:= by simpa using (rainPrice J).times (p.times (rainPrice L))
 have hv:D (P w) + D (Q w)= D w:= by unfold D; rw [show k w-v w=k (P w+Q w)-v (P w+Q w) from (by rw [hx]), hk.plus,p.plus];abel
 have hr:Q' (D (Q w))= D (Q w)- P' (D (Q w)):=by rw [eq_sub_iff_add_eq,add_comm,hy]
 have hl:P' (D (P w))=D (P w)-Q' (D (P w)):=by rw[eq_sub_iff_add_eq,hy]
 rw [show k (Cusp Z w)-v (Cusp Z w) =D (P w)-D (Q w) from (by unfold Cusp D; rw[sub_apply,hk.sub,p.sub];abel), Cusp,sub_apply,map_sub (P'),map_sub (Q'),hl,hr,he]; change _= D w
 rw [← hv]; abel
private lemma crush(b w:H) : inner ℂ b (k w-v w)=0:= by
 have he(n:ℕ)(u y:H): inner ℂ u (k y-v y)= inner ℂ ((Cusp F^n:H.Op) u) (k ((Cusp Z^n:H.Op) y)-v ((Cusp Z^n:H.Op) y)):=by
      induction n generalizing u y with
      | zero=> simp
      | succ n h=> rw [pow_succ,pow_succ]; conv_lhs => rhs; rw [← smash Z F p g m z t y]
                   rw[← Clasp.through_self _ (Cusp_self F)]; exact h _ _
 have hk:Fleet k a:= by simpa using (rainPrice J).times (p.times (rainPrice L))
 refine tendsto_nhds_unique_of_eventuallyEq (tendsto_const_nhds (f:=atTop)) ?_ (Eventually.of_forall fun n:ℕ=> he n b w)
 have hv:= (empties F b).inner (𝕜:=ℂ) ((((k).continuous.continuousAt.tendsto.comp (empties Z w))).sub (v.continuous.continuousAt.tendsto.comp (empties Z w))) -- tune
 simpa only [hk.bases,p.bases,sub_self,inner_zero_right] using! hv
lemma groundMirror : v*rain J=rain L*v:= by
 apply mul_left_cancel (a:=rain L); rw [←mul_assoc, ←mul_assoc,rain_mul,one_mul]; ext1 y; apply ext_inner_left ℂ; intro b; exact sub_eq_zero.mp (by rw[←inner_sub_right]; exact crush _ _ p g m z t _ _)
lemma groundPlume : Across v P P':= by
 have hw:k=v:= by rw [← groundMirror _ _ p g m z t, mul_assoc,rain_mul,mul_one]
 intro x; have ht:= Mara _ _ p g m z t x; rw [hw,Clasp.shadow, Clasp.shadow,sub_apply,sub_apply] at ht; change (P') (v (x-P x))=v (P x)-P' (v (P x)) at ht; rw [p.sub,map_sub] at ht; grind
end YM.Marque
