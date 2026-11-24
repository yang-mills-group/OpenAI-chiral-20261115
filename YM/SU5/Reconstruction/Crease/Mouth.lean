import YM.SU5.Reconstruction.Crease.Receiver
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.BridgeClub.Club
open Function Set Filter MeasureTheory Spectral Analysis Metric ContinuousLinearMap Anvil Picket CrossedFrame
open scoped BigOperators Topology InnerProductSpace ComplexOrder NNReal ENNReal Complex Classical
variable {H D K:Hilbert}{M: Net H}(C: Clasp K H D){J:Flash H}{Γ:Set H.Op}{Ω:H}
local notation "P"=>C.plume
local notation "R"=>C.shadow
abbrev BasePort := C.plume*C.shadow
local notation "B"=>BasePort C
def Lumen := R^2 + P^2
local notation "E"=>Lumen C
lemma beacon (x:H):Lumen C x=R (R x)+P (P x):= by unfold Lumen; simp only [sq,add_apply,mul_apply_eq_comp]
lemma luminance : AntilipschitzWith 2 (Lumen C):= by
 have ht(x:H): ‖x‖≤ (2:ℝ)*‖E x‖:= by
   have hp:P x+R x=x:=DFunLike.congr_fun C.unites x; have h:‖x‖≤ ‖P x‖+‖R x‖:=by nth_rw 1 [← hp]; exact norm_add_le ..
   have he: ‖R x‖^2 + ‖P x‖^2≤ ‖E x‖*‖x‖:= by
      have e': (inner ℂ (E x) x).re=‖R x‖^2+‖P x‖^2:= by
         rw [beacon,inner_add_left,Clasp.through_self _ C.shadow_self (R x) x,Clasp.through_self _ C.plume_self (P x) x,Complex.add_re,show (inner ℂ (R x) (R x)).re=‖R x‖^2 from inner_self_eq_norm_sq (𝕜:=ℂ) _,show (inner ℂ (P x) (P x)).re=‖P x‖^2 from inner_self_eq_norm_sq (𝕜:=ℂ) _]
      exact le_trans (le_of_eq e'.symm) ((Complex.re_le_norm _).trans (norm_inner_le_norm ..))
   nlinarith [pow_le_pow_left₀ (norm_nonneg _) h 2,sq_nonneg (‖P x‖-‖R x‖),norm_nonneg (E x),norm_nonneg x]
 exact AntilipschitzWith.of_le_mul_dist (fun x y=>by simpa only [dist_eq_norm, NNReal.coe_ofNat, ← map_sub] using ht (x-y))
lemma sharpL : Bijective (Lumen C):= by
 let p:=luminance C; let u:=p.injective
 have ht:IsSelfAdjoint (Lumen C):= (C.shadow_self.pow 2).add (C.plume_self.pow 2)
 exact ⟨u,fun x=> closure_minimal (s:=Set.range (Lumen C)) (Set.Subset.refl _) (p.isClosedEmbedding (E).uniformContinuous).isClosed_range (polar_dense ht u x)⟩
lemma l_port : Commute (BasePort C) (Lumen C):=
 let h : Commute B P:= (Commute.refl P).mul_left C.opponents.symm
 let p : Commute B R:= C.opponents.mul_left (Commute.refl R)
 (p.pow_right 2).add_right (h.pow_right 2)
variable {C} (h:Club C J M Ω Γ)
include h
lemma admission : Dense {x:H|∃ A∈ M, BasePort C x=A Ω}:= by
 let L:=ContinuousLinearEquiv.ofBijective (E) (LinearMap.ker_eq_bot.mpr (sharpL C).1) (LinearMap.range_eq_top.mpr (sharpL C).2) -- name?
 have hd:DenseRange (fun x:H=> L.symm (J.f x)):=fun x=> subset_closure ⟨J.f (L x),by simp only [J.twice,ContinuousLinearEquiv.symm_apply_apply]⟩
 refine (hd.dense_image (L.symm.continuous.comp J.f.continuous) h.away_bank).mono ?_
 rintro _ ⟨x,⟨A,v,rfl⟩,rfl⟩; let q:=L.symm (J.f (A Ω)); let N:=star A; have ht:=h.reverse (star A) (star_mem v); rw [star_star] at ht
 obtain ⟨Y,p,e⟩:= h.cranes 1 (1/2) (by norm_num) (by norm_num) (star A) (star_mem v); refine ⟨Y,p,(sharpL C).1 ?_⟩; unfold WPort at e; rw [one_smul] at e; change E (B q) = E (Y Ω)
 rw [← show B (E q)= E (B q) from DFunLike.congr_fun (l_port C).eq q, show E q=J.f (A Ω) from L.apply_symm_apply _, beacon,← e]; change P (R _) = _; rw [← ht]
end YM.BridgeClub.Club
