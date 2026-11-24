import YM.CF.Spire.City
import GaugeFieldConstruction.Myrtle
set_option autoImplicit false
set_option maxHeartbeats 240000
set_option synthInstance.maxSize 24000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Fock.Celeb
open Filter NormedSpace Function Finset
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators ContDiff Topology
attribute [local instance] opCStarAlgebra
open Lattice SU Phase Lat Jet Fock Dial Brace Paige Peaks Spire Scroll Tulip Rush Vault Cube
section helper
variable {I:Type*}[Fintype I][LinearOrder I]
abbrev zeno(x: ℂ):= Spire.zen x
abbrev zcl:ℂ→L[ℝ]ℂ:= Complex.I • (Complex.ofRealCLM.comp Complex.imCLM)
lemma z_ap(x:ℂ):zcl x=zeno x:=rfl
lemma ske_J {F:ℝ→Op I} {f:Op I}{x:ℝ}(hP:∀ᶠ i in 𝓝 x,IsStarProjection (F i))(hf:HasDerivAt F f x): star (dg (dir_g (F x) f))= -dg (dir_g (F x) f):=by
 have he:star f=f:= ((hf.star).congr_of_eventuallyEq (hP.mono fun _ p=>(show _=_ from p.isSelfAdjoint).symm)).unique hf; have hh:star (F x)=F x:= hP.self_of_nhds |>.2
 rw [←dg_star,←dg_neg]; unfold dir_g; rw [star_sub,star_mul,star_mul,he,hh]; abel
variable (Xi Ψ:ℝ→ Wave I)(F C:ℝ→Op I)(φ:ℝ→ℂ)(x:ℝ){f c:Op I}{φ':ℂ}(hF:HasDerivAt F f x)(hC:HasDerivAt C c x)(hφ:HasDerivAt φ φ' x)(hP:∀ᶠ i in 𝓝 x,IsStarProjection (F i))(H:∀ᶠ i in 𝓝 x,(C i)ᵀ= -(C i))(Hp:IsUnit (stage (F x) (C x)))(Hu:filled (F x) (C x)≠0)(h0:∀ᶠ i in 𝓝 x,‖Ψ i‖=1)
local notation "qv"=> Sobiq (F x) (C x) f c
local notation "J"=>dir_g (F x) f
include Hp Hu h0 H hF hC hP hφ
lemma scale_Bay (p:∀ᶠ i in 𝓝 x, Complex.exp ((Real.log ‖filled (F i) (C i)‖:ℂ)+ zen (φ i)) • Ψ i= filled (F i) (C i)): HasDerivAt Ψ (acts (dg J) (Ψ x)+(zen qv-zen φ') • Ψ x) x:=by
 let A:=fun i=> filled (F i) (C i); let U:= Ψ x; let u:=fun i=> Real.log ‖A i‖; let h:= deriv u x; let L(i):= (u i:ℂ)+zen (φ i); let V(i):=Complex.exp (-(L i)); let N:=dg J; let α:= -(h:ℂ)-zen φ'+qv
 have he:=Prime_Q F C x hF hC hP H Hp Hu
 have hv:HasDerivAt u h x:= ((DifferentiableAt.norm ℂ he.differentiableAt Hu).log (norm_pos_iff.mpr Hu).ne':DifferentiableAt ℝ u x).hasDerivAt
 have hL:HasDerivAt V (V x * (-((h:ℂ)+zen φ'))) x:=by exact (((Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt x hv).add (show HasDerivAt (fun i=> zeno (φ i)) (zen φ') x from zcl.hasFDerivAt.comp_hasDerivAt x hφ)).neg.cexp)
 have hk:∀ᶠ i in 𝓝 x,V i • A i= Ψ i:=by
    filter_upwards [p] with i r; change Complex.exp (L i) • Ψ i=A i at r; change (Complex.exp (-(L i))) • A i=_; rw [←r,smul_smul,←Complex.exp_add,neg_add_cancel,Complex.exp_zero,one_smul]
 have hU: (V x) • (A x)= U :=hk.self_of_nhds
 have hd: HasDerivAt Ψ (acts N U + α • U) x:=by
    refine ( (hL.smul he).congr_of_eventuallyEq (hk.mono fun _ p=>p.symm)).congr_deriv ?_
    change V x • (acts N (A x)+qv • A x) + (V x * -_) • A x = _ -- order
    rw [←hU,map_smul]; unfold α; module
 let K':=inner ℂ U (acts N U); have hs: inner ℂ (acts N U) U= -K' :=by
    nth_rw 1 [← star_star N]; rw [act_inner]; unfold K'; rw [show star N= -N from ske_J hP hF,act_neg, inner_neg_right] -- tune orientation
 have hx :inner ℂ U U=1:=by rw [inner_self_eq_norm_sq_to_K,show ‖U‖=1 from h0.self_of_nhds]; simp -- U notation
 have hz:= hd.inner ℂ hd; have ht:= (hz.congr_of_eventuallyEq (show (fun _:ℝ=>(1:ℂ)) =ᶠ[𝓝 x] fun i=> inner ℂ (Ψ i) (Ψ i) from h0.mono fun i p'=>by dsimp only; rw [inner_self_eq_norm_sq_to_K,p']; simp)).unique (hasDerivAt_const ..); change inner ℂ U (_+α • U)+inner ℂ (_+α • U) U=0 at ht; rw [inner_add_left,inner_add_right,hs,inner_smul_left,inner_smul_right,hx,mul_one,mul_one] at ht
 have ha:α.re=0:=by have h:= congrArg Complex.re ht; change (K'+α+(-K'+star α)).re=(0:ℂ).re at h; simp only [Complex.add_re,Complex.star_def,Complex.conj_re, Complex.zero_re, Complex.neg_re] at h; linarith
 have hq:α=zen qv-zen φ':= Complex.ext (by rw [ha]; simp [Spire.zen]) (by simp [α,Spire.zen]; ring); rw [hq] at hd; exact hd
end helper
section map
variable {I J:Type*}[Fintype I][Fintype J][LinearOrder I][LinearOrder J] (T:I≃J)
lemma parkT (U V: Op I):portW T (stage U V)=stage (portW T U) (portW T V):=by
 let X:= Matrix.reindexAlgEquiv ℂ ℂ T; change X (stage U V)=stage (X U) (X V); unfold stage body; have hh(F:Op I):cc (X F)=X (cc F):=rfl; simp only [map_mul,map_add,map_sub,map_one, hh U, cc_sub,cc_one] -- tune
lemma parkUnit (U V:Op I)(h:IsUnit (stage U V)): IsUnit (stage (portW T U) (portW T V)):= by rw [← parkT]; exact IsUnit.map (f:=(Matrix.reindexAlgEquiv ℂ ℂ T)) h -- tune
lemma parkV (U:Op I)(h:IsUnit U): portW T U⁻¹=(portW T U)⁻¹:=by
 let X:=Matrix.reindexAlgEquiv ℂ ℂ T; change X U⁻¹=(X U)⁻¹; have he:= (live h).2; have hv:X (U⁻¹)*X U=1:=by rw [←map_mul,he,map_one]
 nth_rw 1 [←mul_one (X U⁻¹),←show X U*(X U)⁻¹=1 from (live (h.map X)).1, ←mul_assoc, hv]; simp
end map
section physics
variable {m B L:Side}{j:ℕ}{e:ℝ} {ho:Odd L.val}{Y:Pricing j L ho (Thread j)}{P:Grasp Y B e}
local notation "Λ"=>CSide m B
variable (p:Pearl P)(w:Stamped j L ho Y)(k:P.roundZ ≤ (CSide m B).val)(v:1≤ j)(x:ℝ)(F:ℝ→ Skin m B)(r:ℝ→Cue m)
abbrev Bomb (x:Skin m B)(y:Cue m): Op (Single (CSide m B)):= postC (starfish m B x y)
abbrev Mood (P: Grasp Y B e)(x: Skin m B)(y:Cue m):ℂ:= hum m B (P.cost m firstM) x (starfish m B x y)
include k
lemma box_T (U: Skin m B)(hg:Guard U e)(i:Cue m)(u:Phase.ZeroF m B U i): Bomb U i=portW (helix _).symm (bow m B U (slot m i) (stick 0)):=by unfold Bomb starfish postC spotC; rw [poet P.topB hg P.baseY.1 (r':={0}) u (stick_in _ (mem_singleton_self _))]; rfl
lemma MoodUnit (U: Skin m B)(g:Guard U e)(i:Cue m)(u:Phase.ZeroF m B U i):IsUnit (stage (spar j firstM U) (Bomb U i)):=by rw [box_T k _ g i u,frame_init P.topB P.baseY (P.couture k firstM) g]; exact parkUnit _ _ _ (bow_ok _ P.baseY g (r:={0}) u (stick_in _ (mem_singleton_self _))).2
include v w p
-- genuine phase derivative recipe. call r fixed later. No off-top activation. Will set j= Λ.R.J.
lemma motionK {f B':Op (Single (CSide m B))}{φ:ℂ}(hF:HasDerivAt (fun i=>spar j firstM (F i)) f x)(hB:HasDerivAt (fun i=>Bomb (F i) (r i)) B' x)(hφ:HasDerivAt (fun i=>Mood P (F i) (r i)) φ x)(hp:∀ᶠ i in 𝓝 x,Guard (F i) e)(ht:∀ᶠ i in 𝓝 x,Phase.ZeroF m B (F i) (r i)): HasDerivAt (fun i=>changeM P (F i) firstM) (acts (dg (dir_g (spar j firstM (F x)) f)) (changeM P (F x) firstM) + (zen (Sobiq (spar j firstM (F x)) (Bomb (F x) (r x)) f B')-zen φ) • changeM P (F x) firstM) x:=by
 let T':=fun i=> starfish m B (F i) (r i); let P' := fun i=> spar j firstM (F i); let A:=fun i=>filled (P' i) (Bomb (F i) (r i)); have hx:∀ᶠ i in 𝓝 x,Slow (F i) (hook (T' i)) P.p:=by filter_upwards [hp,ht] with i e h; exact starK P.topB P.baseY.1 e h
 have he:∀ᶠ i in 𝓝 x,A i≠0:=by filter_upwards [hp,hx] with i g h; exact ((P.couture k firstM).rhythm _ g _ h _ h).2
 refine scale_Bay (fun i=>changeM P (F i) firstM) (fun i=>spar j firstM (F i)) (fun i=>Bomb (F i) (r i)) (fun i=>Mood P (F i) (r i)) x hF hB hφ (hp.mono fun i e=> (P.broadness _ k firstM).projection _ e) (Filter.Eventually.of_forall fun i=> starC _ (fun j=> hookN (starfish m B (F i) (r i)) (node j))) (MoodUnit k _ hp.self_of_nhds (r x) ht.self_of_nhds) he.self_of_nhds (hp.mono fun i e=>(sea_g k _ e firstM).2) ?_
 filter_upwards [hp,ht,he] with i g h E; exact change_v p w k v firstM (F i) g (T' i) (fun u b=> (starK p.ample P.baseY.1 g h u b).trans_le p.wide) _ (Real.exp_log (norm_pos_iff.mpr E))
end physics
end YM.CF.Fock.Celeb
end
