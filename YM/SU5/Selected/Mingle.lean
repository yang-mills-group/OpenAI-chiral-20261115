import YM.SU5.Selected.Sentry
import YM.SU5.Selected.CompassGlass
/-! # CP5. Partial clusters (spatial coordinates not of bounded speed with respect
 to each other). Use all-positive time to get full vacuum cluster. Also on Glass. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.SelectionAnalysis
open Function Set Filter Metric NormedSpace
open CF.Buffered.Afterglow.Tower MeshClock Germ Vacancy ContinuousLinearMap
open scoped Topology InnerProductSpace NNReal ENNReal Classical
variable {H:Hilbert}

namespace Sunbelt
variable {a:Axis}{M:Mesh}(X:Sunbelt a (marks M) H) (S : OS.Semigroup H a)
local notation "A"=> {v:Axis // v ≠ a}
local notation "P"=> X.track
local notation "Γ" => marks M
local notation "U" k:max t:max=> (X.track.crew k).play t
local notation "Ω" x:max => X.plane x
local notation "fΛ"=> Axis → Γ
local notation "χ" v:max=> show A→Γ from fun k=> v k.val
local notation "E'" n:max=> show ℝ≥0 from Real.toNNReal (show ℝ from ((n:Γ):ℝ))
-- fold transport tools
variable (e:X.heat=S.E) (ind : ∀ (k:{v:Axis//v ≠ a})(v:marks M)(t:ℝ≥0), ((X.track.crew k).play v).comp (S.E t)=(S.E t).comp ((X.track.crew k).play v))
local notation "L" s:max => spotter M X.track s
local notation "K" k:max t:max=> ((spotter M X.track t).move k).calm
variable (p:∀ (k:{x:Axis//x≠a}) (x y:H),X.Coasts k x y)
include e ind p
local notation "κ" t:max r:max=> Moving.pause (L r) t
lemma worldly (x y:H)(r:ℕ)(t:List A)(ε:ℝ)(h:0<ε): ∃ l:ℝ,∀ u:fΛ,(∀ k∈t,l≤|(u (k:A).val:ℝ)|) → 0 ≤ (u a:ℝ)→
    ‖inner ℂ x ((Ω u) y)-inner ℂ x ((Ω u) ((κ t r) y))‖≤ε :=by
 induction t generalizing ε with
 | nil=> exact ⟨0,fun u t _=> by rw [(L r).pause_nil]; simp [le_of_lt h]⟩
 | cons k t ih=>
    obtain ⟨w,hw⟩:=X.symmetric_mix S e ind k x ((κ t r) y) r (p k) (ε/2) (by positivity)
    obtain ⟨d,hd⟩:= ih (ε/2) (by positivity)
    refine ⟨max w d,fun u v q=>?_⟩
    specialize hd u (fun i hi=> (le_max_right ..).trans (v i (List.Mem.tail _ hi))) q
    specialize hw u ((le_max_left ..).trans (v k (List.Mem.head ..))) q
    rw [Moving.compose, ContinuousLinearMap.comp_apply]
    exact (norm_sub_le_norm_sub_add_norm_sub (inner ℂ x ((Ω u) y)) (inner ℂ x ((Ω u) ((κ t r) y))) _).trans ((add_le_add hd hw).trans_eq (by ring)) -- tune
lemma salvos(k:A)(t:List A)(h:k∈t)(r:ℕ)(x:H)(u:Γ): (U k u) ((κ t r) x)= (κ t r) x:= ((X.quiet S e k _ r (p k)).mp (((L r).move k).calm_mem _ |>.mpr ((L r).aligned_ok.mp ((L r).par t x) k h))) u
omit p e in
lemma pause_heat(t:List A)(r:ℕ)(u:ℝ≥0) : (κ t r).comp (S.E u)=(S.E u).comp (κ t r):=by
 induction t with
 | nil=> rw [Moving.pause_nil]; rfl
 | cons k t ih=> rw [Moving.compose]; exact Alliance.slide _ _ _ (calm_heat X S ind k r u) ih
omit e ind p in
lemma purview (t:ℝ≥0) (v:Γ) (p:(t:ℝ) ≤ (v:ℝ)) : t ≤ v.val.toNNReal:= by change (t:ℝ)≤ (↑(v.val.toNNReal):ℝ); rwa [Real.coe_toNNReal _ ((NNReal.zero_le_coe ..).trans p)]
omit e ind p in
lemma rest (x:H) (t:List A) (p:∀ i∈t,∀ v:Γ,(U i v) x=x)(u:A→Γ) : (P).raw t u x=x:=by
 induction t with
 | nil=> rfl
 | cons i t ih=> rw [Alliance.raw_step,ContinuousLinearMap.comp_apply,ih (fun i h=> p i (List.Mem.tail _ h)),p i (List.Mem.head ..)]
lemma blend (x:H)(r:ℕ) : (∀ (i:A) (u:Γ), (U i u) (S.orth ((κ X.list r) x))= S.orth ((κ X.list r) x)):=by
  intro i u; let f(t:ℝ≥0):=S.E t ((κ X.list r) x); have h:=S.emerges ((κ X.list r) x); apply tendsto_nhds_unique (((U i u).continuous.continuousAt.tendsto.comp h)) (h.congr (fun v=>?_)); rw [Function.comp_apply];
  change f v=(U i u) (S.E v _); unfold f; rw [←ContinuousLinearMap.comp_apply (U i u),ind,ContinuousLinearMap.comp_apply,X.salvos S e ind p i X.list (X.traverses _) r x]
variable (w:H)(hl:∀ y:H, y∈ S.ground→ (∀ (i:{v:Axis//v≠a})(u:marks M),(X.track.crew i).play u y=y)→∃ b:ℂ,b • w = y) (hp:∀(i:{v:Axis//v≠a})(u:marks M),(X.track.crew i).play u w=w)(ht:w∈ S.ground) (hw:‖w‖=1)
include hl hp ht hw
local notation "T"=> X.list
local notation "Z" x:max y:max => inner ℂ x w * inner ℂ w y
lemma projection_home (y:H)(r:ℕ): S.orth ((κ T r) y)= (inner ℂ w y) • w:=by
  have hv : (κ T r) w=w:= (L r).pin _ (((L r).aligned_ok).mpr (fun i _ _=> hp i _))
  obtain ⟨b,h⟩:=hl (S.orth ((κ T r) y)) (Submodule.starProjection_apply_mem ..) (blend X S e ind p y r)
  have hx : inner ℂ w (b • w)=inner ℂ w y:=by rw [h,← Submodule.inner_starProjection_left_eq_right, Submodule.starProjection_eq_self_iff.mpr ht,←(L r).swing, hv]
  rw [inner_smul_right, inner_self_eq_norm_sq_to_K, hw] at hx; rw [←h,←hx]; simp
omit hl hp ht hw in
lemma eliminates (u:fΛ) (y:H) (r:ℕ) : (Ω u) ((κ T r) y)=S.E (E' (u a)) ((κ T r) y) :=by
  unfold plane; rw [e,ContinuousLinearMap.comp_apply, X.rest _ _ (by intro i w t; exact (salvos X S e ind p i T w r y t))] -- name implicit fix omit
lemma intermingled (x y:H)(l:ℝ)(h:0<l): ∃ t:ℝ,0≤ t ∧ ∀ u:fΛ,t ≤ (u a:ℝ)→(∀ i : A, t ≤ |(u i.val:ℝ)|) → ‖inner ℂ x ((Ω u) y)- Z x y‖ ≤ l :=by
  obtain ⟨t,r⟩:= X.worldly S e ind p x y 0 T (l/2) (by positivity)
  let y':= (κ T 0) y; have hi: Tendsto (fun a:ℝ≥0=> inner ℂ x (S.E a y')) atTop (𝓝 (Z x y)):=by
    have he : Tendsto (fun t=> inner ℂ x (S.E t y')) atTop (𝓝 (inner ℂ x (S.orth y'))):=tendsto_const_nhds (x:=x)|>.inner (S.emerges y'); rw [show S.orth y'=_ from projection_home X S e ind p w hl hp ht hw y 0,inner_smul_right,mul_comm (inner ℂ w y)] at he; exact he
  obtain ⟨d,hd⟩:= Filter.eventually_atTop.mp (Metric.tendsto_nhds.mp hi (l/2) (by positivity))
  refine ⟨max t (d:ℝ),le_max_of_le_right (by positivity),fun u v b=>?_⟩
  refine (norm_sub_le_norm_sub_add_norm_sub _ (inner ℂ x ((Ω u) y')) _).trans ((add_le_add (r u (fun i _=> (le_max_left ..).trans (b i)) (le_trans (le_max_of_le_right (by positivity)) v)) (show _ ≤ l/2 from ?_)).trans_eq (by ring))
  unfold y'; rw [X.eliminates S e ind p u y 0]; rw [← dist_eq_norm]
  exact le_of_lt (hd _ (purview d (u a) ((le_max_right ..).trans v))) -- naming
-- Extend to ALL real separated coordinates *on glass*, open eps method (no PPC)
local notation "V"=> (X.track.Realm X.list)
local notation "Π"=> glass X (daylight M) S ind
lemma glass_mingle (x y: X.track.Realm X.list)(l:ℝ)(h:0<l): ∃ t:ℝ,0≤ t ∧ ∀ u:Axis→ℝ,t < (u a:ℝ) → (∀ i:A,t < |u i.val|) →
    ‖ inner ℂ x ((Π).E ((u a).toNNReal) ((Π).U (diameter u) y)) - Z x.val y.val‖ ≤ l:=by
  let f(u:Axis→ℝ):ℝ:= ‖X.curtain (daylight M) x.val y.val u - Z x.val y.val‖
  have hx : Continuous f:= ((X.curtain_cont (daylight M) ..).sub continuous_const).norm -- tune
  obtain ⟨t,h₀,hp⟩:= X.intermingled S e ind p w hl hp ht hw x.val y.val l h
  let d:Axis→ℝ→Prop:= fun i z=> if i=a then t<z else t< |z|
  let u0 : Set (Axis→ℝ):= Set.pi (Set.univ: Set Axis) (fun i=> {z:ℝ|d i z})
  have hu : IsOpen u0:= isOpen_set_pi (Set.finite_univ) fun i _=>by
     by_cases v:i=a; · simp only [d,v,↓reduceIte]; exact isOpen_Ioi
     simp only [d,v,↓reduceIte]; exact isOpen_lt continuous_const continuous_abs
  let Z'(u:Axis→Γ):Axis→ℝ:=fun i=> (u i:ℝ); have he : DenseRange Z' := DenseRange.piMap (f:=fun i:Axis=> fun v:Γ=>(v:ℝ)) (fun h:Axis=> (daylight M).denseRange_val)
  have hz (u:Axis→Γ)(v:Z' u∈u0): f (Z' u) ≤ l:=by
     unfold f Z'; rw [← curtain_eq,playback, (X.track).grounded X.list (show (y.val:H) ∈ _ from y.property)]
     apply hp u; · exact (show t < (u a:ℝ) from (by simpa [d,Z'] using v a (mem_univ _))).le
     rintro ⟨i,j⟩; exact (show t < |(u i:ℝ)| from (by simpa [d,Z',j] using v i (mem_univ _))).le
  refine ⟨t,h₀,fun u p0 p1=>?_⟩
  have hm:u∈ u0:= by
     intro i _; by_cases p:i=a; · simpa [d,p] using p0
     simpa [d,p] using p1 ⟨i,p⟩
  suffices s:f u ≤ l by
     unfold f at s; rw [glass_window X (daylight M) S e ind,Submodule.orthogonalProjectionOnto_mem_subspace_eq_self,Submodule.orthogonalProjectionOnto_mem_subspace_eq_self] at s; exact s
  by_contra! hh
  let K':= f ⁻¹' Set.Ioi l; obtain ⟨w,q,r⟩:= he.exists_mem_open (s:=K'∩u0) (IsOpen.inter (hx.isOpen_preimage _ isOpen_Ioi) hu) ⟨u,hh,hm⟩; exact not_le_of_gt q (hz w r)
end Sunbelt
end YM.SelectionAnalysis
#print axioms YM.SelectionAnalysis.Sunbelt.intermingled

#print axioms YM.SelectionAnalysis.Sunbelt.glass_mingle
