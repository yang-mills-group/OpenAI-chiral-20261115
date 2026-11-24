import YM.CF.Spark.Blush
set_option autoImplicit false
noncomputable section
namespace YM.CF.Spark
open scoped Topology BigOperators Matrix MatrixOrder ContDiff InnerProductSpace Matrix.Norms.L2Operator ComplexOrder
open Function Filter Metric Finset NormedSpace Lattice Laurent Lat Tulip Rush Cube Tenant Mir Mir.Trip Phase Branch Vale MeasureTheory RG Wilson WilsonStartup RP Nova Sample Reflect Fock
attribute [local instance] opCStarAlgebra
variable {n m B: Side} {e β:ℝ} (p:Clip)
local notation "G0"=>SU.group
local notation "n'"=> Domain m B
local notation "F'"=> Face (Per n)
local notation "U'"=> Pack m B
-- rebuild from supplied seam. Smooth weight.
variable (i:Axis)(x y z:Pack m B)(S T:ℝ)
lemma truly : tiedK m B i x x (Pbar m B i x)=x:=by
 unfold tiedK; rw [rpbar]; unfold stitch; apply Prod.ext
 · funext k; simp [patchF]
 funext k; simp [patchF]
def rollR (i:Axis)(x:Pack m B): Skin m B := (tiedK m B i x x x).1
lemma rollT(h:NorthOf m B i x y):rollR i x=rollR i y:=by
 funext k; unfold rollR
 have he(k)(u:k∈E₁ m B i):(tiedK m B i x x x).1 k= (tiedK m B i y y y).1 k:=by simpa only [upU i x x x k u,upU i y y y k u,ite_self] using h.gaugeS k (mem_filter.mp u).2.1 (mem_filter.mp u).2.2
 rcases all_vars i k with u|u; exact he _ u
 have hp(a: Pack m B): let V:= (tiedK m B i a a a); let U:=V.1; U k=(if k.2=i then (U (rayE m B i k))⁻¹ else U (rayE m B i k)):=by
    intro V U; rw [← reflect_E]; change V.1 k= (Pbar m B i V).1 k; unfold V; rw [sew]
 rw [hp x,hp y,he _ ((flipsP ..).2 u)]
lemma swung: rollR i (Pbar m B i x) = (tiedK m B i x (Pbar m B i x) (Pbar m B i x)).1 :=by
 funext k; let U:= Pbar m B i x
 unfold rollR
 have he k (u:k∈E₁ m B i):(tiedK m B i U U U).1 k= (tiedK m B i x U U).1 k:=by
    rw [upU _ _ _ _ _ u,upU _ _ _ _ _ u,ite_self]; split_ifs with h
    · change rayUK m B i x.1 k=x.1 k; rw [reflect_E, if_neg (sharedE k i u h).1,(sharedE k i u h).2]
    rfl
 rcases all_vars i k with u|u; exact he k u
 have hp(a: Pack m B): let V:= tiedK m B i a (Pbar m B i x) (Pbar m B i x); let U:=V.1; U k=(if k.2=i then (U (rayE m B i k))⁻¹ else U (rayE m B i k)):=by intro V U; rw [← reflect_E]; change V.1 k= (Pbar m B i V).1 k; unfold V; rw [sew]
 change (tiedK m B i U (Pbar m B i x) (Pbar m B i x)).1 k=_
 unfold U at *; rw [hp (Pbar m B i x),hp x,he _ ((flipsP ..).2 u)] -- tune
-- finite amplitude transport
variable (v:ℕ)
def sail(v:ℕ)(U:Config G0 n):= -(T * basicP p U)-v*tollX S U
lemma sail_c:Continuous (sail (n:=n) p S T v):= Continuous.sub (Continuous.neg (continuous_const.mul (ren_c p))) (continuous_const.mul (tc S))
lemma staff(u:Trip m): sail p S T v (onPack B u x).1=sail p S T v x.1:=by
 change sail p S T v (pull _ _ x.1)=_; unfold sail; rw [pull_basic,pull_toll]
lemma steer: let Y(a b):=tiedK m B i x a b; let V(a b):=sail p S T v (Y a b).1; V y z+V z y=V y y+ V z z:=by
 intro Y V
 let W(a b):=basicP p (Y a b).1; let U(a b):= tollX S (Y a b).1; have h(a b):V a b= -(T* W a b)-(v:ℝ)*U a b:=rfl
 have he:U y z+U z y=U y y+ U z z:=braid i x y z (voice S)
 have hx:W y z+W z y=W y y+ W z z:=econX .. -- tune
 rw [h,h,h,h]
 linear_combination -T*hx-v*he
lemma hurst: sail p S T v (rollR i x)+sail p S T v (rollR i (Pbar m B i x))=2*sail p S T v x.1:=by
 rw [swung]; change sail _ _ _ _ _+sail _ _ _ _ _=_; have he:= steer p i x x (Pbar m B i x) S T v; let y:= Pbar m B i x; let Y:=tiedK m B i x
 have hz:Pbar m B i x= Y y x:= (congrArg (Pbar m B i) (truly i x).symm).trans (sew ..)
 have hp:= staff p x S T v (slideM m i); change sail p S T v (Pbar m B i x).1 =_ at hp
 let V:=sail (n:=Domain m B) p S T v
 change V (Y x y).1+ V (Y y x).1= _ at he; rw [show Y y x=Pbar m B i x from hz.symm,show Y x y=x from truly i x,show V (Pbar m B i x).1= _ from hp] at he
 rw [two_mul]; exact he.symm
variable (k:Site (More m))(l: Foot m B)(f:RP.Test m B)(b:Bool)
def loadR(i:Axis)(f:RP.Test m B) (x:Pack m B):= (Real.exp (sail p S T v (rollR i x)/2) : ℂ) • f x -- NOTE weight? P diag=≥ applied both halves gives sailYes
lemma wellR (h:OfferedF m B i f b): OfferedF m B i (loadR p S T v i f) b:=by
 have hp:Continuous (rollR (m:=m) (B:=B) i):= continuous_fst.comp ((tiedC (m:=m) (B:=B) i).comp (continuous_id.prodMk (continuous_id.prodMk continuous_id)))
 exact ⟨((Complex.continuous_ofReal.comp Real.continuous_exp).comp (((sail_c p S T v).comp hp).div_const 2)).smul h.cont,fun x=> (h.sector x).scale _,fun x y t=>by rw [loadR,loadR,h.localU x y t,rollT _ _ _ t]⟩
lemma vibes: fiscal m B i (loadR p S T v i f) b x=(Real.exp (sail p S T v x.1) : ℂ) • fiscal m B i f b x:=by
 unfold fiscal loadR
 rw [theta_smul,Algebra.smul_mul_assoc,Algebra.mul_smul_comm,smul_smul,Complex.star_def,Complex.conj_ofReal,smul_smul,mul_assoc,← Complex.ofReal_mul]; -- tune combine two Smul
 rw [←Real.exp_add, show sail _ _ _ _ _/2+ sail _ _ _ _ _/2= _ from (show sail p S T v (rollR i (Pbar m B i x))/2+sail p S T v (rollR i x)/2=sail p S T v x.1 from by linarith only [hurst p i x S T v]), ←smul_smul]; apply smul_comm
lemma lax: squareR m B k l i (loadR p S T v i f) b x= (Real.exp (sail p S T v x.1):ℂ) • squareR m B k l i f b x:=by unfold squareR; rw [vibes,staff,twist_formula,Algebra.mul_smul_comm,Algebra.smul_mul_assoc,twist_formula]
end YM.CF.Spark
