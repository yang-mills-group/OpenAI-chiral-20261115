import YM.SU5.FiniteGaugeData.Tower.GermUnit
import YM.SU5.FiniteGaugeData.Tower.MeshClock
/- Signed grid shifts and real shifts on canonical continuous part. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.MeshClock
open Function Set Metric Filter
open scoped Topology InnerProductSpace NNReal ComplexOrder
open Germ
variable (M:Mesh)
def bell (s:ℕ)(i:ℤ):ℝ:=i * (mill M s:ℝ≥0).val
def castor(s r:ℕ)(i:ℤ):ℤ:= (M.L:ℤ)^(r-s)*i
lemma natural_time (s i:ℕ):bell M s i=(whenly M s i:ℝ≥0).val:=by simp [bell,whenly]
lemma refineZ(s r:ℕ)(p:s≤ r)(i:ℤ): bell M r (castor M s r i)=bell M s i:=by
 unfold bell castor; push_cast; rw [mul_comm _ (i:ℝ),mul_assoc]
 have h:(M.L:ℝ)^(r-s)*(mill M r:ℝ≥0).val=(mill M s:ℝ≥0).val:=by simpa using congrArg ((↑) : ℝ≥0→ℝ) (mill_finer M s r p)
 rw [h]
lemma tight(s:ℕ):Injective (bell M s):=by intro i j h; unfold bell at h; have ht: 0 < (mill M s:ℝ≥0).val:=mill_pos M s; exact_mod_cast mul_right_cancel₀ ht.ne' h
lemma bell_add (s:ℕ)(i j:ℤ):bell M s (i+j)=bell M s i+bell M s j:=by simp [bell,add_mul]
lemma bell_le (s:ℕ)(i j:ℤ):bell M s i≤bell M s j↔i≤j:=by unfold bell; rw [mul_le_mul_iff_left₀ (show 0<(mill M s:ℝ≥0).val from mill_pos M s)]; norm_cast
noncomputable def marks : AddSubgroup ℝ where
 carrier:={x:ℝ|∃(s:ℕ)(i:ℤ),bell M s i=x}
 zero_mem':= ⟨0,0,by simp [bell]⟩
 neg_mem':=by rintro _ ⟨s,i,rfl⟩; exact ⟨s,-i,by simp [bell]⟩
 add_mem':=by
    rintro _ _ ⟨s,i,rfl⟩ ⟨u,b,rfl⟩; let t:=max s u
    exact ⟨t,castor M s t i+castor M u t b,by rw [bell_add,refineZ M _ _ (le_max_left ..),refineZ M _ _ (le_max_right ..)]⟩
lemma existsZ (x:marks M):∃(s:ℕ)(i:ℤ),bell M s i=x:=x.property
noncomputable def notch(s:ℕ)(i:ℤ):marks M:=⟨bell M s i,s,i,rfl⟩
lemma notch_up (s r:ℕ)(p:s≤r)(i:ℤ):notch M r (castor M s r i)=notch M s i:=Subtype.ext (refineZ M s r p i)
lemma notch_zero (s:ℕ):notch M s 0=0:=Subtype.ext (by change bell _ s 0=_; simp [bell])
lemma notch_add (s:ℕ)(i j:ℤ):notch M s (i+j)=notch M s i+notch M s j:=Subtype.ext (bell_add M s i j)
lemma notch_tight (s:ℕ):Injective (notch M s):=fun i j h=>tight M s (congrArg Subtype.val h)
lemma notch_exists(x:marks M):∃ s i,notch M s i=x:=by obtain ⟨s,i,h⟩:= x.property; exact ⟨s,i,Subtype.ext h⟩
lemma daylight:Dense (marks M:Set ℝ):=by
 have he {x:ℝ≥0}{a:ℝ}(h:a=1∨ a=-1): (a*(x:ℝ≥0).val:ℝ)∈closure (marks M:Set ℝ):=by
    have ht: Tendsto (fun s => a*((whenly M s (⌊ x/mill M s⌋₊+1):ℝ≥0):ℝ)) atTop (𝓝 (a*x.val)):=tendsto_const_nhds.mul (NNReal.tendsto_coe.mpr (shade M x))
    refine mem_closure_of_tendsto ht (Eventually.of_forall fun s=>?_)
    rcases h with h|h <;> rw [h]
    · rw [one_mul]; exact (by change (whenly M s _).val∈ marks M; rw [←natural_time]; exact (notch M s _).property)
    rw [neg_one_mul]; exact (marks M).neg_mem (by change (whenly M s _).val∈ marks M; rw [←natural_time]; exact (notch M s _).property)
 intro x; by_cases h:0≤x
 · exact (one_mul x) ▸ (he (a:=1) (x:=⟨x,h⟩) (Or.inl rfl))
 have p:=he (a:=-1) (x:= ⟨-x,by linarith⟩) (Or.inr rfl); simpa using p

structure Lunation (H:Hilbert) where
 nav (s:ℕ)(i:ℤ):H.Op
 zero(s:ℕ):nav s 0=ContinuousLinearMap.id ℂ _
 sums(s:ℕ)(i j:ℤ): (nav s i).comp (nav s j)=nav s (i+j)
 changeover(s t:ℕ)(p:s≤t)(i:ℤ):nav s i=nav t (castor M s t i)
 limited(s:ℕ)(i:ℤ): ‖nav s i‖≤1
namespace Lunation
variable{M} {H:Hilbert}(L:Lunation M H)
def ship(x:marks M):H.Op:=L.nav (notch_exists M x).choose (notch_exists M x).choose_spec.choose
lemma navZ (s:ℕ)(i:ℤ): L.ship (notch M s i)=L.nav s i:=by
 unfold ship
 let x:=notch M s i; let r:=(notch_exists M x).choose; let j:=(notch_exists M x).choose_spec.choose
 let t:=max s r; have e:s ≤ t:=le_max_left ..; have jh:r ≤t:=le_max_right ..
 change L.nav r j = _
 have hz:notch M r j = notch M s i:= (notch_exists M x).choose_spec.choose_spec
 rw [←notch_up M r t jh j,←notch_up M s t e i] at hz
 rw [L.changeover r t jh,L.changeover s t e,(notch_tight M t hz)]
lemma ship_early:L.ship 0=ContinuousLinearMap.id ℂ _:=by rw [←notch_zero M 0,navZ,L.zero]
lemma ship_add(x y:marks M): (L.ship x).comp (L.ship y)=L.ship (x+y):=by
 obtain ⟨s,i,rfl⟩:=notch_exists _ x; obtain ⟨r,j,rfl⟩:=notch_exists _ y
 rw [←notch_up M r (max r s) (le_max_left ..),←notch_up M s (max r s) (le_max_right ..),←notch_add,L.navZ,L.navZ,L.navZ,L.sums]
def plays : Players (marks M) H where
 play:=L.ship
 pulls i x:=((L.ship i).le_opNorm _).trans (mul_le_of_le_one_left (norm_nonneg _) (L.limited ..))
 play_zero:= L.ship_early
 piles := L.ship_add
end Lunation
end YM.CF.Buffered.Afterglow.Tower.MeshClock
namespace YM.CF.Buffered.Afterglow.Tower.Germ
open Function Set Filter Metric
open scoped InnerProductSpace Topology
namespace Players
variable {Γ:AddSubgroup ℝ}{H:Hilbert}(P:Players Γ H)(d:Dense (Γ:Set ℝ))
-- real continuation with law at zero identifying projector rather than id
noncomputable def wind (u:H):ℝ→H:=(d.extend (fun i=> P.play i (P.pi_c u)))
lemma wind_uc (u:H):UniformContinuous (wind P d u):=d.uniformContinuous_extend (P.far (P.repaired u))
lemma wind_on (u:H)(i:Γ):wind P d u i=P.play i (P.pi_c u):= d.extend_of_ind (P.far (P.repaired u)) i
include d
private lemma both {Y:Type*}[TopologicalSpace Y][T2Space Y]{f g:ℝ→Y}(p:Continuous f)(t:Continuous g)(h:∀ i:Γ,f i=g i)(b:ℝ):f b=g b:=by
 exact congrFun (d.denseRange_val.equalizer p t (funext h)) b
lemma wind_plus(u v:H)(b:ℝ):wind P d (u+v) b=wind P d u b+wind P d v b:=
 both d (P.wind_uc ..).continuous ((P.wind_uc d u).continuous.add (P.wind_uc d v).continuous) (fun i=>by change wind _ _ _ _=wind _ _ _ _+wind _ _ _ _; rw [wind_on,wind_on,wind_on,map_add,map_add]) b
lemma wind_smul(c:ℂ)(u:H)(b:ℝ):wind P d (c•u) b=c•wind P d u b:= both d (P.wind_uc ..).continuous (continuous_const.smul (P.wind_uc ..).continuous) (fun i=>by simp [wind_on]) b
lemma wind_norm(u:H)(b:ℝ): ‖wind P d u b‖=‖P.pi_c u‖:= by
 apply both d (f:=fun b=>‖wind P d u b‖) (g:=fun _=>‖P.pi_c u‖) (P.wind_uc d u).continuous.norm continuous_const
 intro i; simp [wind_on,P.wins]
noncomputable def route(b:ℝ):H.Op:= (show H→ₗ[ℂ] H from {
    toFun u:=wind P d u b
    map_add' u v:=P.wind_plus d u v b
    map_smul' c u:=P.wind_smul d c u b}).mkContinuous ‖P.pi_c‖ (fun u=>by change ‖wind P d u b‖≤ _; rw [wind_norm]; exact ContinuousLinearMap.le_opNorm ..)
lemma route_uc (u:H):UniformContinuous (fun i=> route P d i u):=P.wind_uc d u
lemma route_source: route P d 0=P.pi_c:=by ext x; have h:=P.wind_on d x 0; rwa [P.play_zero] at h
lemma route_on(i:Γ)(x:H):route P d i x=P.play i (P.pi_c x):=P.wind_on d x i
lemma route_sum(t u:ℝ): (route P d t).comp (route P d u)=route P d (t+u):=by
 ext1 x; change route P d t (route P d u x)=route P d (t+u) x
 apply both d (f:=fun u=>route _ _ t (route P d u x)) (g:=fun u=>route _ _ (t+u) x)
 · exact (route P d t).continuous.comp (P.route_uc d x).continuous
 · exact (P.route_uc d x).continuous.comp (continuous_const.add continuous_id)
 intro i; apply both d (f:=fun t=>route _ _ t _) (g:=fun t=>route _ _ (t+_) x)
 · exact (P.route_uc d _).continuous
 · exact (P.route_uc d x).continuous.comp (continuous_id.add continuous_const)
 intro j
 simp only [P.route_on d]; change P.play j (P.pi_c (P.play i (P.pi_c x)))=route P d _ _
 rw [←ContinuousLinearMap.comp_apply _ (P.play i),← P.pi_play,ContinuousLinearMap.comp_apply,P.pi_idem,P.paved,← AddSubgroup.coe_add,P.route_on d]
lemma route_fixed (q:H.Op)(p:∀ i:Γ,(P.play i).comp q=q.comp (P.play i))(t:ℝ): (route P d t).comp q=q.comp (route P d t):=by
 ext1 x
 apply both d (f:=fun t=> (route P d t) (q x)) (g:=fun t=>q ((route P d t) x)) (P.route_uc d _).continuous (q.continuous.comp (P.route_uc d _).continuous)
 intro i; simp only [P.route_on d, ←ContinuousLinearMap.comp_apply q]
 change P.play i (P.pi_c (q x))=(q.comp _) (P.pi_c x); rw [←ContinuousLinearMap.comp_apply _ q,← P.commutes_c q p,←p]; rfl
lemma revolve (i:ℝ)(x y:H):inner ℂ (P.route d i x) y=inner ℂ x (P.route d (-i) y):=by
 apply both d (f:=fun t=>inner ℂ (P.route d t x) y) (g:=fun t=>inner ℂ x (P.route d (-t) y)) ((P.route_uc d _).continuous.inner continuous_const) (continuous_const.inner ((P.route_uc d _).continuous.comp continuous_neg))
 intro r
 rw [P.route_on d,← AddSubgroup.coe_neg,P.route_on, P.shift_g H,neg_neg]
 rw [←ContinuousLinearMap.comp_apply (P.play r),P.pi_play,ContinuousLinearMap.comp_apply,←ContinuousLinearMap.adjoint_inner_right P.pi_c,P.pi_adj] -- check
end Players
end Germ
end YM.CF.Buffered.Afterglow.Tower -- bad?

#print axioms YM.CF.Buffered.Afterglow.Tower.Germ.Players.route_sum
#print axioms YM.CF.Buffered.Afterglow.Tower.Germ.Players.route_fixed
#print axioms YM.CF.Buffered.Afterglow.Tower.Germ.Players.revolve

