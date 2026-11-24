import GaugeFieldConstruction.DreamVU
import GaugeFieldConstruction.StencilAngleOrbit
/-!
 # Choose an actual probing contour still satisfying Pose order and positive
 at **both** Eu & unpadded real W for these two labels. Can adjust
 apertures using this with Eu LagOp fees. Better than only Mink ±. No claim on sign of the
 direct W reading on the *supplied* Portrait's original pair of smears.
 -/
set_option autoImplicit false
set_option synthInstance.maxSize 15000
set_option maxHeartbeats 300000
noncomputable section
namespace YM.GaugeFieldConstruction.Ember.Volumetric
open Calibration Raw Cauchy Phys Apit Stage Fathom Function Set Filter Module Empire Hulse Salam Palace
open Floor Carat Dawn Sailing Angles Points Bulb Analysis MeasureTheory Complex Finset
open scoped Topology BigOperators Matrix.Norms.Frobenius ComplexConjugate ContDiff Kronecker InnerProductSpace
attribute [local instance] iG iF iX iU iT2 iW2 iV iS
variable {S:City}{P:Axis→Across}{L:Sheds S P}{C:Supplies L}{u:ℕ→Carat}
namespace FirstPackMars
open Loft Cell NSF.Boundary NSF.Work.C20 NSF.LD
open YM.Boundary (Probe Probe.bar Joint Test4 Distn)
attribute [local instance] floatA floatY
attribute [local instance 30000] topx topg
variable (p:Ticket u C)
variable {A Z:CloudsL}(H:SurfCheckL A)(G:SurfCheckL Z)
local notation "S_A"=> SurfRimL A
variable (W:NSF.Boundary.Surface (SurfRimL A)) (F:NSF.Boundary.Waves (SurfRimL A))(N:W.Aurora drapeL)
local notation "M_ν" => H.TinCanL
open YM.Boundary (Joint.push Joint.materialize)
variable (s:(SurfRimL A).RealSpin)
variable {B0:NSF.Boundary.LRoom (SurfRimL Z) timeAxis} {Bκ:Small (SurfRimL A) B0}
variable (d:PredictionL W F (SurfCheckL.HeightsKL p H) (H.AsterBackL) Bκ (SurfCheckL.VesselPL p H) s) (wX:N.FullBody F)
open Metric Stage.PlaneL
abbrev duoSt (x:Points 2): E4:= x 1-x 0
abbrev rectoAngleSt (x y:E4):Points 2:= WithLp.toLp 2 (![x,y])
abbrev coastAngleSt (T:ℝ)(x:Points 2):Prop:= 0<T ∧ 2*T < duoSt x 3 ∧ (∀ i:Axis,2*T < |duoSt x i|) ∧ |duoSt x 3| + T < duoSt x 0
private lemma costWhite (m:Axis)(v:m≠3)(j:Axis)(a:j≠3)(b:m≠j)(t:ℝ) :∀ i:Axis, parcelMars (Ψ j 3 t).val i m= if i=m then 1 else 0:=by
 intro i; let M:= (Ψ j 3 t).val.motion; have e : M (basis m)=basis m:= by
    ext1 i; obtain ⟨x,y,h⟩:= _root_.YM.Work.A13.plane_givens a (basis m) t; by_cases p:i=j
    · subst i; change Ortho.move (Ortho.oneParameter (Ortho.plane j 3) t) _ _= _; rw [x]; simp [b,v,Ne.symm b,Ne.symm v]
    by_cases q:i=3
    · subst i; change Ortho.move (Ortho.oneParameter (Ortho.plane j 3) t) _ _= _; rw[y]; simp [b,v,Ne.symm b,Ne.symm v]
    exact h _ p q
 have he:(M (basis m)) i=((Ψ j 3 t).val.val) i m:= by change M4.move _ (basis m) i = _; simp
 unfold parcelMars; rw [← he,e]; by_cases h:i=m <;> simp [h]
variable (m:Axis)(c:m≠3)(X:Axis→ UV four)(K:UV four)(x:Points 2)(σ:ℂ)(T:ℝ)
local notation "qν"=> ![σ • X m,K]
variable (U: SurfCheckL.boisterL p Z)(Jg:∀ s:SO,∀ i, compassPiMars p s (X i) = ∑ j:Axis,parcelMars s.val j i • X j)(Kg:∀ s:SO,compassPiMars p s K=K)
variable (Y:coastAngleSt T x)(hx:x∈conf 2)(z:(0:ℝ)< (Z _ x ![σ • X m,K]).re)
include c G Y hx z U Jg Kg
private lemma atEquatorAngleSt : ∃ o:Points 2, o∈conf 2∧o∈Gate2VU.gap∧ readings o=0∧ (0:ℝ)<(Z _ o qν).re ∧ duoSt o 0>0 ∧∀ i:Axis, i≠3→ duoSt o i≠0:=by
 let t':= x
 let y:=NSF.Points.across (-(x 0)) x
 have hy:y 0=0:=add_neg_cancel _; have hz:y∈conf 2:=NSF.Points.across_in _ hx
 let V:=y 1; have he:V=duoSt x:= (by change x 1+ -x 0=_-_; rw [sub_eq_add_neg])
 have ht(i:Axis): V i ≠ 0:=by rw [he]; exact abs_pos.mp ((by linarith only [Y.1] : 0<2*T).trans (Y.2.2.1 i))
 have hw:0< V 0:= by rw [he]; have z:=abs_nonneg (duoSt x 3); linarith [Y.1,Y.2.2.2]
 obtain ⟨j,f,h,g⟩:=(show ∃ j:Axis,j≠m ∧ j≠0 ∧ j≠3 from (by fin_cases m<;> decide))
 obtain ⟨s',p'⟩:=_root_.YM.Work.A13.plane_eliminates g V
 let u:=Ψ j 3 s'; let W:= u.val.motion V; let F':= motionMoonMars u y; let K0:= u.val.val; have hu:F' 0=0:=by change _root_.YM.Ortho.motion u.val (y 0)=_; rw[hy,map_zero];
 have hv:F' ∈conf 2:=NSF.Points.move_in _ hz
 have hK:F' 1=W:=rfl; have ht₃ : W 3=0:=p'
 have hM: compassPiMars p u (X m)=X m:= by
    rw [Jg]; unfold u; simp_rw [costWhite m c j g (Ne.symm f)]; simp
 have hL:compassPiMars p u ∘ qν=qν:=by funext i; fin_cases i <;> simp [Function.comp_apply,hM,Kg] -- `qν` notation
 have e: duoSt F'=W:=by unfold duoSt; rw [hK,hu,sub_zero]
 obtain ⟨a,b,c'⟩:= _root_.YM.Work.A13.plane_givens g V s'
 refine ⟨F',hv,(show _ from ?_),funext (fun i=>?_),?_,e.symm ▸ (show 0 < W 0 from (by rw [show W 0=_ from c' _ (Ne.symm h) (by decide)]; exact hw)),fun i p=>?_⟩ -- readings maybe defeq function not PiLp ext.
 · change duoSt F'∈ Mink.spacelike; have el:duoSt F' ≠ 0:=sub_ne_zero.mpr (hv.ne (by decide)); rw [e] at el ⊢
   have h0: YM.time W=0:=p'; rw [Mink.lateral]; change |time W|<‖YM.spatial W‖; rw[h0,abs_zero,norm_pos_iff]; intro u; apply el; exact Mink.ext_by u h0
 · fin_cases i
   · change YM.time (F' 0) = _; rw [hu]; rfl
   exact ht₃ -- rw hK if needed
 · have e:= U _ qν y hz u; rw[hL,G.even _ qν x hx] at e -- y notation local
   rw [show Z _ _ _=_ from e]; exact z
 rw [e]
 by_cases v:i=j
 · subst i; intro hm; apply ht j; change W j=_ at a; change W 3=_ at b
   linear_combination -(Real.cos s')*a+(Real.sin s')*b-(V j)*(Real.sin_sq_add_cos_sq s')+(Real.cos s')*hm-(Real.sin s')*ht₃ -- signs inspect
 exact (c' _ v p).symm ▸ ht i
include wX d
structure GoldAreaSt (U:Set (Points 2))(R:Points 2→ℂ)(T δ:ℝ):Prop where
 high : 0<T
 reserve : 0<δ
 space : Nonempty U
 upfront : IsOpen U
 contour : ∀ x∈U, coastAngleSt T x ∧ x∈conf 2∩Gate2VU.gap
 margin : ∀ x∈U, δ<(Z 2 x ![σ • X m,K]).re ∧ δ< (R x).re -- explicit
 ready : ContinuousOn R U
 ink : ∀ f:Joint 2,HasCompactSupport ⇑f→tsupport ⇑f ⊆ U→W.W 2 ((M_ν) ∘ qν) f= ∫ y,R y * f y
-- open locus. Supplies even positive clocks & all-axis separation. May differ from direct stage/ripp.
omit c G Y hx z U Jg Kg wX d
private lemma snowAreaSt (T:ℝ)(x:Points 2)(u:coastAngleSt T x): {x : Points 2| coastAngleSt T x} ∈ 𝓝 x:=by
 let Z(i:Axis)(x:Points 2):=duoSt x i; have hf(i:Axis) : Continuous (Z i):=by
    change Continuous (fun x:Points 2=> x 1 i- x 0 i); fun_prop
 exact (Eventually.of_forall (p:=fun _=> 0<T) fun _=>u.1).and (((hf 3).continuousAt.tendsto.eventually (lt_mem_nhds u.2.1)).and ((eventually_all.mpr fun i:Axis=> ((hf i).abs.continuousAt.tendsto.eventually (lt_mem_nhds (u.2.2.1 i)))).and (isOpen_lt ((hf 3).abs.add continuous_const) (hf 0) |>.mem_nhds u.2.2.2))) -- tune binder
include c G Y hx z U Jg Kg wX d
lemma forecastGoldSt : ∃ (B:Set (Points 2))(S':Points 2→ℂ)(q d:ℝ), GoldAreaSt (Z:=Z) H W m X K σ B S' q d:=by
 obtain ⟨u,ht,hf,θ,e,h,v⟩:= atEquatorAngleSt p G m c X K x σ T U Jg Kg Y hx z
 obtain ⟨P,hB,pL,r,hC,q,wr⟩:= ResolveVU p H G W F N s d wX qν u ht hf θ
 let δ:ℝ:=(Z _ u qν).re/2; have hp:0<δ:=half_pos e; have hu:δ < (hB u).re:=by rw [q]; exact half_lt_self e
 have he₀ := hC u r |>.continuousAt (pL.mem_nhds r)
 let B:Set (Points 2):= {x | x∈P∧ x∈conf 2∩ Gate2VU.gap∧δ < (Z _ x qν).re∧ δ < (hB x).re}
 have he:B ∈ 𝓝 u:= inter_mem (pL.mem_nhds r) (inter_mem (inter_mem ((conf_open _).mem_nhds ht) (Gate2VU.open_gap.mem_nhds hf)) (inter_mem ((Complex.continuous_re.continuousAt.tendsto.comp ((G.sm qν).continuousOn.continuousAt ((conf_open _).mem_nhds ht))).eventually (lt_mem_nhds (show δ< (Z _ u qν).re from half_lt_self e))) ((Complex.continuous_re.continuousAt.tendsto.comp he₀).eventually (lt_mem_nhds hu))))
 let F(s:ℝ):= u+s • (mirDirYL 1 3); have hi:Tendsto F (𝓝[>]0) (𝓝 u):=by
    have hw:Tendsto F (𝓝[>]0) (𝓝 (F 0)):= (show ContinuousAt F 0 from (continuous_const.add (continuous_id.smul continuous_const)).continuousAt).tendsto.mono_left nhdsWithin_le_nhds
    rwa [show F 0=u from (by simp [F])] at hw
 have ed(s:ℝ): duoSt (F s)=duoSt u+s • basis 3:=by unfold duoSt; change (u 1+ _)-(u 0+ _)=_; simp [mirDirYL,NSF.Points.direction]; abel -- tune
 have hz(s:ℝ): duoSt (F s) 3=s:=by rw [ed]; have h₀:time (u 0)=0:=congr_fun θ 0; have h₁: time (u 1)=0:=congr_fun θ 1; change u 1 3-u 0 3+s*(basis (3:Axis) 3)=_; change u 0 3=0 at h₀; change u 1 3=0 at h₁; simp [h₀,h₁]
 have hy₀(s:ℝ)(i:Axis)(a:i≠3): duoSt (F s) i= duoSt u i:=by rw [ed]; simp [a,Ne.symm a]
 have he₁ : ∀ᶠ s:ℝ in 𝓝[>] 0,s+s/4<duoSt u 0:= Filter.Eventually.filter_mono nhdsWithin_le_nhds (isOpen_lt (show Continuous (fun s:ℝ=> s+s/4) from (by fun_prop)) (continuous_const (y:=duoSt u 0))|>.mem_nhds (show 0+(0:ℝ)/4<duoSt u 0 by simpa using h)) -- open.mem args
 have hp(i:Axis): ∀ᶠ s:ℝ in 𝓝[>] 0, i≠3 → 2*(s/4) < |duoSt u i|:=by
    by_cases p:i=3; · exact Eventually.of_forall fun _ q=>(q p).elim
    refine Filter.Eventually.mono (p:=fun s:ℝ=>2*(s/4) < |duoSt u i|) ?_ (fun _ h _=> h)
    apply Filter.Eventually.filter_mono nhdsWithin_le_nhds; exact isOpen_lt (show Continuous (fun s:ℝ=>2*(s/4)) from (by fun_prop)) continuous_const |>.mem_nhds (show 2*((0:ℝ)/4) < |duoSt u i| by simpa using abs_pos.mpr (v i p))
 obtain ⟨w,uF,w0,p1,w1⟩:= ((hi.eventually (interior_mem_nhds.mpr he)).and ((show ∀ᶠ s:ℝ in 𝓝[>]0, 0<s from self_mem_nhdsWithin).and (he₁.and (eventually_all.mpr hp)))).exists
 let U:= interior (interior B∩ {x| coastAngleSt (w/4) x}); have hU(x:Points 2)(hx:x∈ U): x∈ B∧ coastAngleSt (w/4) x:= ⟨interior_subset (interior_subset hx).1,(interior_subset hx).2⟩
 change 0<w at w0
 have ht:coastAngleSt (w/4) (F w):=by
    rw [coastAngleSt,hz, abs_of_pos w0,hy₀ _ 0 (by decide)]; refine ⟨by linarith only [w0],by linarith only [w0],fun i=>?_,p1⟩
    by_cases p:i=3; · subst i; rw[hz,abs_of_pos w0]; linarith only [w0]
    rw [hy₀ _ _ p]; exact w1 i p
 have h':U⊆P:=fun x p=> (hU _ p).1.1
 refine ⟨U,hB,w/4,δ,ht.1,?_ ,⟨⟨F w,?_⟩⟩,isOpen_interior,(fun x p=>⟨(hU x p).2,(hU x p).1.2.1⟩),(fun x p=>(hU x p).1.2.2), hC.mono h',fun f u t=>wr f u (Set.Subset.trans t h')⟩ -- names w shadow earlier.
 · exact half_pos e
 exact mem_of_mem_nhds (interior_mem_nhds.mpr (inter_mem (isOpen_interior.mem_nhds uF) (snowAreaSt (w/4) (F w) ht)))
#print axioms forecastGoldSt
end FirstPackMars
end YM.GaugeFieldConstruction.Ember.Volumetric
end
