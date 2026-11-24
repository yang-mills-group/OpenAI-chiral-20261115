import YM.CF.Ups.Weak
import YM.CF.Ups.Cosy
set_option autoImplicit false
set_option quotPrecheck false
set_option synthInstance.maxSize 20000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 800000
noncomputable section
namespace YM.CF.Pyx
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open Cube SU Fock Skye Scree Spire Dial Laic Pec Hest Hive
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix MatrixOrder Kronecker Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
open Rush Tulip Vault Paige Drapes Peaks Brace Branch Lat Kennel CF.Jet Pressure
open Girt
local notation "G₀"=> SU.group
open Scroll
variable {f n :Side}{a d w e:ℝ}
open Work.F05
variable {B C L:Side}{j:ℕ}{ho:Odd L.val}{Y:Pricing j L ho (Thread j)}{P':Grasp Y B e}
open Broc
variable {M:Side}{x W:ℝ}
variable (P:Grasp Y B e) (G:Ratio (CSide M B) (mid C B))(R:GramM (mid C B))(F₁:Scree.Loom (mid M B))(F₂:Scree.Loom (mid C B))(q:Chi)(u:ℝ)
variable {P G R F₁ F₂ q u}(X:BaseL P G R F₁ F₂ q u)(T:StepData (Domain M B) (Domain C B))(p:T.ratio=ratio G)(t:T.patch.Branches T.kernel SU.group)
variable (P G R F₁ F₂ q u)
local notation "NQ"=> mid M B
local notation "HQ"=> mid C B
variable {P G R F₁ F₂ T q u}{F:Oracle (mid M B)}{W:Oracle (mid C B)}(b:BoundedT (n:=mid M B) F)
open Haro Tap Cascade
-- independent of the numerical Male; canonical re-normal and signed W operator moved via projection-preserving scale, complex linear. not claiming power or gauge perturbative response
variable (G F₁ F₂ q u T)
local notation "VU"=> Phys (mid C B)
local notation "QY"=>Phys (mid M B)
variable (Yw:Orbit (mid M B)) (Xw:Orbit (mid C B))
section
include j
noncomputable def sPout (F:Forest (ratio G)):VU→L[ℂ]QY:= let i:Male:=⟨1,odd_one⟩; let z:= unionP (YF G F₁ F₂ q u F Yw Xw); let T:= Thread j; let Z:=chargeA T G i z
       ((sect0 G * Z)⁻¹:ℂ) • ((pailL (patchQ G) (reefS G true)).comp ((acts (quant (ticketT T true i G z))).comp (hoist (switchG G).symm.toEmbedding ∅)))
#check sPout
open Haro Tap
local notation "KΘ"=> Iota G
lemma cent_c (i:Male)(F:Forest (ratio G))(W:Phys (mid C B)) : sPout (j:=j) G F₁ F₂ q u Yw Xw F W=fire (Thread j) G i (unionP (YF G F₁ F₂ q u F Yw Xw)) (cartsL (switchG G).symm W):=rfl
end
lemma glory_t (x:Scree.Phys n): Continuous fun i : SpaceM=>scaleW n i.val x:=by
 let p(i:SpaceM):=-(Tap.plankP n i.val); have hv(i:SpaceM):scaleW n i.val x=acts (exp (dg (p i)-Matrix.trace (tickA n * p i) • 1)) x:=Sault.bet _ _ i.property.adj
 have he:Continuous p:=by
    unfold p Tap.plankP headW; apply Continuous.neg; let Z:=Fir.Aop-(1/2:ℂ) • 1; let G(i:SpaceM):Op (Model n):=jump (Equiv.refl _) (fun _=> Z ⊗ₖ i.val); have he:Continuous G:=by
       unfold G; apply continuous_matrix; intro a b; change Continuous fun i:SpaceM=> if a.1=b.1 then _ else _; split; swap; · exact continuous_const
       exact continuous_const.mul (continuous_subtype_val.matrix_elem _ _) -- tune
    exact (love n).toAlgEquiv.toLinearEquiv.toLinearMap.continuous_of_finiteDimensional.comp he
 letI:NormedAlgebra ℚ (Op (Finset (Single n))):= NormedAlgebra.restrictScalars ℚ ℂ _; simp_rw [hv]; apply Continuous.clm_apply _ continuous_const; refine acts_cont.comp (exp_continuous.comp (Continuous.sub ?_ ((continuous_const.mul he).matrix_trace.smul continuous_const))) -- ℚ.stars
 unfold dg; exact continuous_finsetSum _ fun i _=>continuous_finsetSum _ fun j _=>(Continuous.matrix_elem he _ _).smul continuous_const
-- generic bases envelope.CL
variable (P)
include X
lemma pans_PS (F:Forest (ratio G))(y:VU): Envelope fun z:Orbit (mid M B)×Orbit (mid C B)=> sPout (j:=j) G F₁ F₂ q u z.1 z.2 F y:=by
 let h:=X; obtain ⟨b',v,w,p,l⟩:= X.cap; obtain ⟨s,a,h,d,H,u',g⟩:= X.wick; let L'(Z: Orbit NQ× Orbit HQ):=YF G F₁ F₂ q u F Z.1 Z.2
 have hf:Measurable (fun i:Orbit NQ× Orbit HQ=>F₁ i.1) := p.bill.comp measurable_fst
 have he:Measurable L':= (((brake G q u F X.legal.1 X.legal.2).measurable.comp ((l.bill.comp measurable_snd).prodMk hf)).prodMk hf)
 exact Girt.heat_k (pM:=R.J.M) X.power _ H u' g X.pe X.size L' (fun _=>y) (fun z=>X.trial ..) he (rite_c y) -- tag Male irrelevant
omit X
-- lift from probe theorem for finite-dimensional real operator
section
variable {N E F:Type}[NormedAddCommGroup E][InnerProductSpace ℝ E][FiniteDimensional ℝ E][NormedAddCommGroup F][NormedSpace ℝ F][FiniteDimensional ℝ F]
local notation "𝕏"=> E→L[ℝ] F
private lemma saleQt (A:𝕏): A=∑ i,(innerSL ℝ ((stdOrthonormalBasis ℝ E) i)).smulRight (A ((stdOrthonormalBasis ℝ E) i)):=by
 ext v; let S:=stdOrthonormalBasis ℝ E; simp only [ContinuousLinearMap.sum_apply,ContinuousLinearMap.smulRight_apply]; simp_rw [← map_smul]; rw [←map_sum]; exact congrArg A (S.sum_repr v|>.symm.trans (Finset.sum_congr rfl (fun i _=>congrArg (· • S i) (S.repr_apply_apply v i)))) -- repr_apply
private lemma ink_ps {X₀:Type}[MeasurableSpace X₀](A:X₀→𝕏)[MeasurableSpace F][BorelSpace F][MeasurableSpace (E→L[ℝ] F)][BorelSpace (E→L[ℝ] F)](h:∀ x:E, Envelope fun z=> A z x): Envelope A:=by
 rw [funext (fun z=>saleQt (A z))]; exact Env.total _ (fun i=>Girt.pole_w _ (fun x:F=> (innerSL ℝ ((stdOrthonormalBasis ℝ E) i)).smulRight x) (by fun_prop) (h _)) -- tune _ index
lemma chB {Z:Type}[TopologicalSpace Z](A:Z→𝕏)(h:∀ x:E,Continuous fun z=>A z x):Continuous A:=by
 rw [funext fun z=>saleQt (A z)]; refine continuous_finsetSum _ (fun i _=>?_ ); exact (show Continuous (fun x:F=> (innerSL ℝ ((stdOrthonormalBasis ℝ E) i)).smulRight x) from by fun_prop).comp (h _)
end
lemma letter_t(n:Side): Continuous fun i:SpaceM=>scaleW n i.val:= chB _ fun x=>glory_t x
include j
abbrev gentK (x:Orbit (mid M B))(y:Orbit (mid C B)) : VU→L[ℂ]QY:= (Fintype.card (Forest (ratio G)):ℝ)⁻¹ • ∑ i:Forest (ratio G), sPout (j:=j) G F₁ F₂ q u x y i
abbrev Fps (β:ℝ)(W:SpaceM)(V:Orbit (mid M B))(Y:Orbit (mid C B)): VU→L[ℝ]QY := T.density β Y.1 V.1 • (scaleW NQ W.val).comp ((gentK (j:=j) G F₁ F₂ q u V Y).restrictScalars ℝ) -- T explicit via variable but include W? 
lemma Fps_path (P':Grasp Y B e)(W:SpaceM)(x:ℂ):Fps (j:=j) G F₁ F₂ q u T R.beta W Yw Xw (x • denZ R P' F₂ Xw)= x • integrated P' F₁ R F₂ G T q u W.val Yw Xw:=by
 unfold Fps integrated; let r:= (Fintype.card (Forest (ratio G)):ℝ)⁻¹; let d:= T.density R.beta Xw.1 Yw.1; let v:= denZ R P' F₂ Xw
 change d • (scaleW NQ W.val ((gentK (j:=j) G F₁ F₂ q u Yw Xw) (x • v)))=x • r • ∑ F, carrier P' F₁ R F₂ G T q u W.val F Yw Xw; rw [map_smul (gentK ..)]
 have hP (v:QY):scaleW NQ W.val (x • v)=x • scaleW NQ W.val v:=by rw [ans,ans]; unfold scaleZ; dsimp only; rw [map_smul, smul_comm x]
 rw [hP,smul_comm d x]; apply congrArg (x • ·); unfold gentK; change d • scaleW NQ W.val (r • (∑ i:Forest (ratio G),sPout (j:=j) G F₁ F₂ q u Yw Xw i) v)= r • _; rw [map_smul, smul_comm d r]; apply congrArg (r • ·); rw [ContinuousLinearMap.sum_apply,map_sum,Finset.smul_sum]; refine sum_congr rfl fun i _=>?_ ; rfl
local notation "Λ"=> (VU→L[ℝ] QY)
local notation "XK"=> Orbit (mid C B)
include t p X
open Push.BetaTransport
lemma earn_ps (a b:ℝ)(pQ:0 ≤ b):∃ B:ℝ,∀ W:SpaceM, ‖W‖ ≤ b→ ∀ β:ℝ,|β| ≤ a → Measurable (Fps (j:=j) G F₁ F₂ q u T β W Yw) ∧∀ v:XK, ‖Fps (j:=j) G F₁ F₂ q u T β W Yw v‖ ≤B:=by
 let V(z:XK):VU→L[ℝ] QY:=(gentK (j:=j) G F₁ F₂ q u Yw z).restrictScalars ℝ; have he:Envelope V:=by
    apply ink_ps; intro x; let H' : Fintype (Forest (ratio G)):=Scree.woodF .. -- tune
    have ht(D:Forest (ratio G)):Envelope fun z:XK=> sPout (j:=j) G F₁ F₂ q u Yw z D x:= Girt.snap (X:=fun z:XK=>(Yw,z)) (pans_PS P G F₁ F₂ q u X D x) (measurable_const.prodMk measurable_id) -- order
    change Envelope fun z:XK=> ((Fintype.card (Forest (ratio G)):ℝ)⁻¹ • ∑ i:Forest (ratio G), sPout (j:=j) G F₁ F₂ q u Yw z i) x; simp_rw [ContinuousLinearMap.smul_apply,ContinuousLinearMap.sum_apply]; exact Girt.pole_w _ (fun i:QY=> (Fintype.card (Forest (ratio G)):ℝ)⁻¹ • i) (continuous_const_smul _) (Env.total _ ht)
 obtain ⟨ℓ,hℓ⟩:=he.cost; obtain ⟨z,v,s⟩:= (isCompact_closedBall (0:SpaceM) b).exists_isMaxOn ⟨0,mem_closedBall_self pQ⟩ (letter_t NQ|>.norm.continuousOn); let D:= ‖scaleW NQ z.val‖; let y:=slice_estimate T t Yw.1; refine ⟨noiseCost T a*(D*ℓ),fun W w β p=>?_⟩ -- order
 have hc:Measurable (fun z:XK=> T.density β z.1 Yw.1):= (y.measurable β).comp measurable_fst; refine ⟨hc.smul ( (Continuous.clm_comp continuous_const (continuous_id (X:=Λ))).measurable.comp he.meas),?_⟩ -- tune
 intro i; let f:=T.density β i.1 Yw.1; change ‖f • (scaleW _ W.val).comp (V i)‖≤ _; rw [norm_smul,Real.norm_of_nonneg (y.nonneg β i.1)]; apply mul_le_mul (y.le p i.1) _ (norm_nonneg _) ((y.nonneg β i.1).trans (y.le p i.1)); exact (ContinuousLinearMap.opNorm_comp_le ..).trans (mul_le_mul (s (mem_closedBall_zero_iff.mpr w)) (hℓ i) (norm_nonneg _) (norm_nonneg _))
lemma color_ps : Continuous (fun z:ℝ × SpaceM=>Fps (j:=j) G F₁ F₂ q u T z.1 z.2 Yw Xw):=by
 unfold Fps; refine Continuous.smul ((density_cont_all _ _).comp (continuous_fst.prodMk continuous_const)) ?_ ; exact Continuous.clm_comp ((letter_t _).comp continuous_snd) continuous_const
end YM.CF.Pyx
