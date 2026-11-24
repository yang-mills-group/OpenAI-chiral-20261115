import YM.SU5.Selected.Halo
import YM.SU5.Selected.SpatialCard
/-! # Canonical compass glass. Continue time consistently with real-mesh ext on spatial projection. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.SelectionAnalysis
open Function Set Filter Metric MeasureTheory Measure InnerProductSpace
open CF.Buffered.Afterglow.Tower MeshClock Germ Spectral OS Analysis Semigroup
open scoped Topology InnerProductSpace NNReal ENNReal
variable {H : Hilbert} {Γ : AddSubgroup ℝ} {a : Axis}
variable (X : Sunbelt a Γ H) (d : Dense (Γ:Set ℝ))
variable (S : OS.Semigroup H a) (t : X.heat=S.E)
local notation "P"=> X.track
local notation "T"=> X.track.aviator X.list
local notation "A"=> X.track.Realm X.list
local notation "π"=> (T).orthogonalProjectionOnto
local notation "E₀" k:max=> S.E k
variable (h : ∀ i,∀ (z : Γ) (t:ℝ≥0), ((X.track.crew i).play z).comp (S.E t)=(S.E t).comp ((X.track.crew i).play z))
local notation "τ" t:max=> (P).lame X.list (S.E t) (fun i _ v=> h i v t)
-- adapt from Tower's continuous sub-semigroup. view S.U not needed
noncomputable def glass : OS.Semigroup (X.track.Realm X.list) a where
 E t:= τ t
 U x:= (P).aviation d X.list (fun i=> x.val i.val)
 eZero:=by ext1 x; apply Subtype.ext; rw [Alliance.grating,S.eZero]; rfl
 time t b:=by ext1 x; apply Subtype.ext; change (E₀ (t+b)) (x.val:H)=(E₀ t) ((E₀ b) _); rw [S.time]; rfl
 shrinks t:=ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun x=>by rw [one_mul]; have he:=ContinuousLinearMap.le_opNorm (E₀ t) x.val|>.trans (mul_le_of_le_one_left (norm_nonneg _) (S.shrinks t)); exact he)
 sym t:=by
    ext1 x; apply ext_inner_left ℂ; intro y; rw [ContinuousLinearMap.adjoint_inner_right]; exact S.swing t y.val x.val
 uZero:=by
    have hv:(fun (i:{x:Axis // x≠a})=> (0:E4) (i:Axis))=0:=rfl
    rw [show ((0:OS.Cross a).val)=(0:E4) from rfl,hv,Alliance.aviation_zero]
 space x y:=by
    have he:(fun i:{x:Axis // x≠a}=>(x+y).val (i:Axis))=(fun (i:{x:Axis//x≠ a})=> x.val (i:Axis)) + (fun (i:{x:Axis//x≠ a})=> y.val (i:Axis)):=rfl
    rw [he,← Alliance.aviation_group]
 independent t x:=by
    ext1 i; apply Subtype.ext
    change (E₀ t) ((P).flight d X.list (fun i=>x.val i.val) i.val)=(P).flight d X.list _ ((E₀ t) i.val)
    rw [← ContinuousLinearMap.comp_apply _ (E₀ t),Alliance.fluid _ _ _ _ (fun i _ v=> h i v t)]; rfl
 unitary t x:= Alliance.aviation_unit ..
 continuousE x:=Continuous.subtype_mk (S.continuousE x.val) _
 continuousU x:=Alliance.aviation_cont _ _ _ _ (fun i _=>show Continuous (fun v:OS.Cross a=>(v.val:E4) i.val) by fun_prop) x
local notation "Ξ"=> glass X d S h
abbrev habited (u:T) : H:=u.val
lemma glass_heat (z:ℝ≥0)(u:T) : ((Ξ).E z u : T).val=S.E z u.val:= rfl

-- uniqueness of holomorphic continuation
lemma glass_room {z:ℂ} (k:z∈ OS.Semigroup.inside)(x:A) : ((Ξ).F z x : T).val=S.F z x.val:=by
  let W:= OS.Semigroup.inside; let F (z:ℂ) : H:= ((Ξ).F z x:T).val-S.F z x.val
  have he (y:ℝ≥0)(u:0<y) : F (duration y)=0:=by unfold F; rw [(Ξ).roots_heat u, S.roots_heat u]; exact sub_self _
  have hk(X:Hilbert){f:ℂ→X}(v:X→L[ℂ]H) (a) (u: AnalyticAt ℂ f a) : AnalyticAt ℂ (fun t:ℂ=>v (f t)) a:= (v.analyticAt _).comp u
  have ht : AnalyticOnNhd ℂ F W:=fun z hz=> (hk (A) (T).subtypeL z (((ContinuousLinearMap.apply ℂ (A).space x).analyticAt _).comp ((Ξ).localHeat z hz))).sub (((ContinuousLinearMap.apply ℂ H.space x.val).analyticAt _).comp (S.localHeat z hz))
  let i:ℂ:=duration 1
  have hv : 0 < (1:ℝ≥0) := by norm_num
  apply sub_eq_zero.mp (ht.eqOn_zero_of_preconnected_of_frequently_eq_zero (convex_halfSpace_gt Complex.reCLM.toLinearMap.isLinear 0|>.isPreconnected) (show i∈W from dur.mpr hv) ?_ k)
  let f:=fun t:ℝ=> (t:ℂ)+ i
  have hx:Tendsto f (𝓝[>] (0:ℝ)) (𝓝[≠] i):=by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · have h:= ((Complex.continuous_ofReal.add (continuous_const (y:=i))).tendsto (0:ℝ)).mono_left (nhdsWithin_le_nhds (s:=Set.Ioi 0)); simpa [f] using (show Tendsto f _ (𝓝 (f 0)) from h)
    filter_upwards [self_mem_nhdsWithin] with x (i:0<x); intro u; simp [f] at u; linarith
  intro l
  obtain ⟨t,v,g⟩:= ((hx.eventually l).and self_mem_nhdsWithin).exists
  change 0 < t at g; let t':ℝ≥0:= ⟨t,g.le⟩; apply v; rw [show f t=duration (t'+1) from ?_]; exact he _ (by positivity)
  unfold duration f; simp [i,duration,t']; rfl
lemma glass_strikes (z:ℝ) (u:A) : ((Ξ).edge z u:T).val=S.edge z u.val:= by
  let f(x:A) : H:= ((Ξ).edge z x:T).val; let g(x:A):H:=S.edge z x.val
  have he : f=g := ((Ξ).whole 1).equalizer (continuous_subtype_val.comp (show Continuous ((Ξ).edge z) from ((Ξ).edge z).continuous)) ((S.edge z).continuous.comp continuous_subtype_val) (by
    funext x; change ((Ξ).edge z _ : T).val= S.edge z ((Ξ).E 1 x:T).val; rw [high, glass_heat,high]; exact glass_room X d S h (OS.Semigroup.length.mpr one_pos) _)
  exact congrFun he u
-- exact projected pair including arbitrary stamp t and spatial double vectors at all u:Axis
abbrev diameter (w:Axis→ℝ) : OS.Cross a:= (OS.Semigroup.SEP a) (WithLp.toLp 2 w)
lemma diameter_at (w:Axis→ℝ) (i : Axis) (h : i≠ a): (diameter (a:=a) w).val i=w i:=by change ((_-(w a) • basis a : E4) i)=_; simp [h] -- tune
include t
lemma glass_window (x y:H) (u:Axis→ℝ) :
    X.curtain d x y u= inner ℂ (π x) ((Ξ).E (u a).toNNReal ((Ξ).U (diameter u) (π y))) := by
  let A' := (P).stackS X.list; let L₀ :=(P).flight d X.list (fun i=> u i.val)
  have he(f:H) : A' f=π f:=by unfold A'; rw [stack_projection]; rfl
  unfold Sunbelt.curtain; rw [t]
  let U:= (u a).toNNReal
  have hE : (fun i:{x:Axis // x≠a}=> (diameter (a:=a) u).val i.val)=(fun i=>u i.val):=funext fun i=> diameter_at _ _ i.property
  have hx : ((Ξ).U (diameter u) (π y):T).val=L₀ y:=by change (P).flight d X.list _ (↑(π y):H)=_; rw [hE,← he, (P).over]
  let z : T:= ((Ξ).E (u a).toNNReal ((Ξ).U (diameter u) (π y)) : A)
  rw [←hx, ←glass_heat]; exact ((T).inner_orthogonalProjectionOnto_eq_of_mem_right z x).symm -- hx rewrite h loc; check args
omit t
local notation "D₁"=> {j:Axis // j≠ a}
lemma glass_move (x:T)(u:Axis→Γ) : ((Ξ).U (diameter (fun i=> (u i:ℝ))) x : T).val=(P).raw X.list (fun i=> u i.val) x.val:=by
 change ((P).aviation d _ _ x : T).val = _; rw [Alliance.avails]
 rw [show (fun i:D₁=> (diameter (a:=a) _).val (i:Axis))=(fun i=> (u i.val).val) from funext (fun i:D₁=> diameter_at (fun v=> (u v:ℝ)) _ i.property), (P).smooth_notch,ContinuousLinearMap.comp_apply,(P).grounded _ x.property] -- implicit
lemma glass_single (x:T)(i:D₁)(v:Γ) : ((Ξ).U (diameter (fun j=> (Function.update (0:Axis→Γ) i.val v j:ℝ))) x :T).val= ((P).crew i).play v (x.val:H):=by
 rw [glass_move,show (fun k:D₁=>Function.update (0:Axis→Γ) i.val v k.val)= Function.update (0:D₁→Γ) i v from ?_, spotlight (P) _ X.unique_list (X.traverses i)]
 funext a; by_cases e:a=i; subst a; rw [Function.update_self,Function.update_self]
 rw [Function.update_of_ne e,Function.update_of_ne (show a.val≠ i.val from fun q=> e (Subtype.ext q))]; rfl
lemma invariant_glass (x:A): (∀ i:E4,(Ξ).unit.translation i x=x) ↔
    (∀ q:ℝ,S.edge q (x.val:H)=x.val) ∧ ∀ (i:{j:Axis // j≠a})(u:Γ), ((P).crew i).play u (x.val:H)=x.val:=by
 let W:= OS.Semigroup.SEP a; have h₁(j:ℝ):W (j • basis a) = 0:= Subtype.ext (by change (j:ℝ) • basis a-_=_; simp)
 have h₂ (y:OS.Cross a): W y.val=y:= by apply Subtype.ext; change y.val-y.val a • basis a=_; rw [show y.val a=0 from y.property]; simp
 have hm (v:E4): (Ξ).unit.translation v=((Ξ).edge (v a)).comp ((Ξ).U (W v)):=rfl
 constructor
 · intro p; have he(j:ℝ) := p (j • basis a); have hx(z:OS.Cross a): (Ξ).U z x=x:=by
    specialize p z.val; rw [hm,h₂ z,show z.val a=0 from z.property,(Ξ).birth] at p; exact p
   constructor; · intro z; have h:= he z; rw [hm,h₁ z,(Ξ).uZero] at h; simp at h; exact (glass_strikes X d S (by assumption) z x).symm.trans (congrArg (fun x:A=> (x.val:H)) h)
   intro i k; rw [← glass_single X d S h x i k,hx]
 rintro ⟨p,w⟩ v; have hz (u:D₁) : ContinuousAt (fun i:Γ=> ((P).crew u).play i (x.val:H)) 0:= by rw [show _=(fun _=> (x.val:H)) from funext (w u)]; exact continuousAt_const -- maybe wildcard
 have he (U : OS.Cross a) : (Ξ).U U x=x:=by
    apply Subtype.ext; change ((P).flight d X.list (fun i=>U.val i.val) x.val)= (x.val:H);
    let V(i:D₁):=U.val i.val
    suffices H₁ : ∀ t,(P).flight d t V x.val = (x.val:H) from H₁ _
    intro t
    induction t with
    | nil=> rfl
    | cons i t ih=> -- beware ih needs extra e
       rw [Alliance.fly_step,ContinuousLinearMap.comp_apply,ih]; -- not generalize e
       let b:= ((P).crew i); exact congrFun (d.denseRange_val.equalizer (b.route_uc d x.val).continuous (continuous_const (y:=(x.val:H))) (funext (fun (p:Γ)=> by dsimp only [Function.comp_apply]; rw [b.route_on,b.pi_fixer]; exact w i p; exact hz i))) (V i)
 rw [hm, ContinuousLinearMap.comp_apply,he]; apply Subtype.ext; exact (glass_strikes X d S h (v a) x).trans (p _)

end YM.SelectionAnalysis
#print axioms YM.SelectionAnalysis.glass
#print axioms YM.SelectionAnalysis.glass_window
#print axioms YM.SelectionAnalysis.glass_strikes

#print axioms YM.SelectionAnalysis.invariant_glass
