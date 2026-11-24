import SatinPP.Duchess
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 3500
set_option maxHeartbeats 650000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common Ballad Cordial
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
open Germ Alliance Lamour.Bridge.Celeste Designs Twah Prototype
open Lamour.Bridge.Celeste.Morn
namespace Spine
open Aria Casting Six MacroGrid

open TopologicalSpace SatinJets
variable (P:Spine)(x:P.Spectrum0 3)
local notation "ξ"=> P.advocate 3 x 3
local notation "G"=> P.ManyF 3 ξ
local notation "Γ"=> P.cartage 3 ξ
local notation "Θ"=> P.seasons 3 ξ
local notation "E"=> (Θ).E
local notation "κ"=> P.wealth 3 ξ
local notation "D" s:max=>P.lengthP s
local notation "F%" s:max=> P.pointEra s
variable (V:∀ j:Axis,List Axis→ℝ→ P.ColorHil j (P.advocate 3 x j))

local notation "ℒ"=>Lead.Clan

open SatinNucleus
variable {r:ℕ→ℕ}{σ:ℕ→ℝ}{B:ℕ→P.Apron}{f n:ℕ}
variable (W:P.VelvetGlass x V r σ)(R:P.Radiates x B V)
local notation "β" i:max a:max=>P.sprig x V (r i) a (σ i)

abbrev strideHeel(d h:ℝ):=(Θ).E (d*h).toNNReal
abbrev spurHeel(j:Axis)(d h:ℝ):=Γ (d • aglow j h)
lemma aglow_line (j:Axis)(h d:ℝ): d • aglow j h=aglow j (d*h):=by ext i;simp [aglow,Function.update_apply]
def plume (r:ℕ→ℕ)(σ:ℕ→ℝ)(i:ℕ)(a:ℒ):G:= (squire a:ℂ) • (P.sprig x V (r i) (cavalier a) (σ i))

include R
lemma heel_law {t h:ℝ}(p:0<t)(u:0≤h)(i:ℕ):P.strideHeel x (D (r i)) h (β i t)= β i (t+h):=by
 have hx:=P.lengthP_pos (r i)
 unfold sprig
 rw [P.height_pass x 3 V R [] (mul_pos hx p) (mul_le_mul_of_nonneg_left (le_add_of_nonneg_right u) hx.le),mul_add,add_sub_cancel_left,map_smul]

include W
omit R in 
lemma velvet_pay {t u:ℝ}(p:1<t)(q:1<u)(y:Vantage):
 Tendsto (fun i=>inner ℂ (β i t) (Γ ((D (r i)) • y) (β i u))) atTop (𝓝 (gloss (starLane 3 y (t+u)))):=
 W.glass (t:=id) tendsto_id p q tendsto_const_nhds tendsto_const_nhds tendsto_const_nhds
omit R in
lemma velvet_pair {t u:ℝ}(p:1<t)(q:1<u):
 Tendsto (fun i=>inner ℂ (β i t) (β i u)) atTop (𝓝 (gloss (aglow 3 (t+u)))):=
 (P.velvet_pay x V W p q 0).congr fun i=>by rw [smul_zero,P.cart_zero]; rfl

lemma trumpets {h:ℝ} (e:0<h)(q:tBuy h):
  ∀ᶠ i in atTop,∀ a b,dist (inner ℂ
     (toe (P.strideHeel x (D (r i)) h) h (P.plume x V r σ i a))
     (toe (P.strideHeel x (D (r i)) h) h (P.plume x V r σ i b))) (shadowPay 72 a b)<1/100:=by
 refine eventually_all.mpr fun a=>eventually_all.mpr fun b=> ?_
 let t:=cavalier a; let u:=cavalier b
 have p:=cavalry a; have y:=cavalry b
 have p₁:1<t+h:=lt_add_of_lt_of_nonneg p e.le; have q₁:1<u+h:=lt_add_of_lt_of_nonneg y e.le
 have r0:=P.velvet_pair x V W p y; have r1:=P.velvet_pair x V W p₁ y; have r2:=P.velvet_pair x V W p q₁; have r3:=P.velvet_pair x V W p₁ q₁
 have ht:= (((((r0.sub r1).sub r2).add r3).div_const ((h:ℂ)^2)).const_mul ((squire a:ℂ)*squire b)).dist (tendsto_const_nhds (x:=shadowPay 72 a b))

 have z:=ht.eventually (gt_mem_nhds (a:=(1:ℝ)/100) (by
    change dist ((squire a:ℂ)*squire b*((gloss (aglow 3 (t+u))-gloss (aglow 3 (t+h+u))-gloss (aglow 3 (t+(u+h)))+gloss (aglow 3 (t+h+(u+h))))/_)) _ < _
    rw [show t+h+u=t+u+h by abel,show t+(u+h)=t+u+h by abel,show t+h+(u+h)=t+u+h+h by abel];exact q _ _))
 refine z.mono fun i w=>?_
 unfold plume
 rw [map_smul _ _ (β i (cavalier a)),map_smul _ _ (β i (cavalier b)),inner_smul_left, inner_smul_right,Complex.conj_ofReal,←mul_assoc,toe_gram,P.heel_law x V R (zero_lt_one.trans p) e.le,P.heel_law x V R (zero_lt_one.trans y) e.le]
 exact w


omit R
omit W in
lemma heel_ray {j:Axis}{d h:ℝ}(v w:G):
 inner ℂ (toe (P.spurHeel x j d h) h v) (toe (P.spurHeel x j d h) h w)=
  (inner ℂ v w-inner ℂ v (Γ (d • aglow j h) w)-inner ℂ v (Γ (d • -aglow j h) w)+inner ℂ v w)/(h:ℂ)^2:=by
 let y:=d • aglow j h
 have ht(z:G):inner ℂ (Γ y v) z = inner ℂ v (Γ (-y) z):=by
    rw [←ContinuousLinearMap.adjoint_inner_right,P.cart_reverses]
 rw [toe_gram,ht,ht,smul_neg, ←ContinuousLinearMap.comp_apply (Γ (-y)) (Γ y),←P.cart_paves,neg_add_cancel,P.cart_zero]
 change (_- _ - _+inner ℂ v w)/_=_
 unfold y spurHeel;ring

lemma crinoline {h:ℝ} (q:zBuy h):
  ∀ᶠ i in atTop,∀ j:Axis,j≠3→∀ a b,dist (inner ℂ
     (toe (P.spurHeel x j (D (r i)) h) h (P.plume x V r σ i a))
     (toe (P.spurHeel x j (D (r i)) h) h (P.plume x V r σ i b))) (shadowPay (sLeg j) a b)<1/100:=by
 refine eventually_all.mpr fun j=>eventually_all.mpr fun e=>eventually_all.mpr fun a=>eventually_all.mpr fun b=> ?_

 have p:=cavalry a; have y:=cavalry b
 have r0:=P.velvet_pair x V W p y
 have r1:=P.velvet_pay x V W p y (aglow j h)
 have r2:=P.velvet_pay x V W p y (-aglow j h)
 have ht:= (((((r0.sub r1).sub r2).add r0).div_const ((h:ℂ)^2)).const_mul ((squire a:ℂ)*squire b)).dist (tendsto_const_nhds (x:=shadowPay (sLeg j) a b))
 have z:=ht.eventually (gt_mem_nhds (q j e a b))
 refine z.mono fun i w=>?_
 unfold plume
 rw [map_smul _ _ (β i (cavalier a)),map_smul _ _ (β i (cavalier b)),inner_smul_left, inner_smul_right,Complex.conj_ofReal,←mul_assoc,P.heel_ray]
 exact w


lemma velvet_norm {t:ℝ}(p:1<t): Tendsto (fun i=>‖β i t‖) atTop (𝓝 ((t+t)^4)⁻¹):= by
 have z:=P.velvet_pair x V W p p; rw [solo_aglow _ (by linarith)] at z
 have d:= (Complex.continuous_re.tendsto _).comp z |>.sqrt
 rw [Complex.ofReal_re,show ((t+t)^8)⁻¹=(((t+t)^4)⁻¹)^2 from by rw [inv_pow,←pow_mul],Real.sqrt_sq (by positivity)] at d
 refine d.congr fun i=>?_
 exact (norm_eq_sqrt_re_inner (𝕜:=ℂ) _).symm
lemma plume_cap:
 ∃ M> (0:ℝ), ∀ᶠ i in atTop, Snug (P.plume x V r σ i) M:= by
 let y a:= |squire a| * ((cavalier a+cavalier a)^4)⁻¹
 obtain ⟨d,e⟩:= (Set.finite_range y).bddAbove
 refine ⟨max (d+1) 1,zero_lt_one.trans_le (le_max_right _ _),?_⟩
 unfold Snug;refine eventually_all.mpr fun a=>?_
 have t:y a< max (d+1) 1:=(lt_add_of_le_of_pos (e ⟨a,rfl⟩) zero_lt_one).trans_le (le_max_left _ _)
 refine (((P.velvet_norm x V W (cavalry a)).const_mul |squire a|).eventually (ge_mem_nhds t)).mono fun i w=>?_
 unfold plume;rw [norm_smul,Complex.norm_real,Real.norm_eq_abs];exact w

def anklet(d:ℝ)(y:Vantage)(t:ℝ): (G).Op:= (Γ (d • y)).comp (P.strideHeel x d t)
omit W in
lemma anklet_pay (d:ℝ)(y:Vantage)(t:ℝ):‖P.anklet x d y t‖≤1:= by
 exact (ContinuousLinearMap.opNorm_comp_le ..).trans (mul_le_one₀ (P.cart_pay ..) (norm_nonneg _) ((Θ).shrinks _))
local notation "Λ" i:max => P.anklet x (D (r i))
include R
lemma plume_flutter {t:ℝ}(p:1<t)
  {k:ℕ→ℕ}(w:Tendsto k atTop atTop){y:ℕ→Vantage}(q:Tendsto y atTop (𝓝 0)){h:ℕ→ℝ}(u:Tendsto h atTop (𝓝 0))(z:∀ i,0≤ h i):
 Tendsto (fun i=>dist (β (k i) t) ((Λ (k i)) (y i) (h i) (β (k i) t))) atTop (𝓝 0):=by
 let a i:= β (k i) t
 let L i:=(Λ (k i)) (y i) (h i)
 have e: Tendsto (fun i=>t+h i) atTop (𝓝 t):=by simpa only [add_zero] using u.const_add t
 have d:= (P.velvet_pair x V W p p).comp w
 have y0:Tendsto (fun i=>inner ℂ (a i) (L i (a i))) atTop (𝓝 (gloss (starLane 3 0 (t+t)))):=by
    refine (W.glass w p p tendsto_const_nhds e q).congr fun i=>?_

    unfold a L anklet; rw [ContinuousLinearMap.comp_apply,P.heel_law x V R (zero_lt_one.trans p) (z i)]
 have A := ((d.add d).sub (y0.add y0))
 change Tendsto _ _ (𝓝 (gloss (aglow 3 (t+t))+gloss (aglow 3 (t+t))-(gloss (aglow 3 (t+t))+gloss (aglow 3 (t+t))))) at A
 rw [sub_self] at A; have V₁:=(Complex.continuous_re.tendsto 0).comp A |>.sqrt; rw [Complex.zero_re,Real.sqrt_zero] at V₁
 refine squeeze_zero (fun i=>dist_nonneg) (fun i=>?_) V₁
 change dist (a i) (L i (a i)) ≤ √((inner ℂ (a i) (a i)+inner ℂ (a i) (a i)-(inner ℂ (a i) (L i (a i)) +inner ℂ (a i) (L i (a i)))).re)
 apply Real.le_sqrt_of_sq_le
 rw [dist_eq_norm,norm_sub_sq (𝕜:=ℂ),inner_self_eq_norm_sq_to_K]
 simp only [Complex.sub_re,Complex.add_re]
 have b:= (L i).le_opNorm (a i)
 have m:= b.trans (mul_le_of_le_one_left (norm_nonneg _) (P.anklet_pay x ..))
 rw [←RCLike.ofReal_pow,show ∀ k:ℝ, (RCLike.ofReal k:ℂ).re=k from fun _=>rfl]
 nlinarith only [m,norm_nonneg ((L i) (a i)), show RCLike.re (inner ℂ (a i) ((L i) (a i))) = (inner ℂ (a i) ((L i) (a i))).re from rfl]


local notation "X%" => P.plume x V r σ
lemma poised(a:ℒ){m:ℝ}(u:0< m):
 ∀ᶠ δ in 𝓝[>] (0:ℝ),∀ᶠ i in atTop,∀ y:Vantage, ‖y‖≤δ → ∀h:ℝ,0≤h → h≤δ →
 dist ((X%) i a) ((Λ i) y h ((X%) i a))≤ m:= by
 by_contra! q
 obtain ⟨d,h,p⟩:=exists_seq_forall_of_frequently q
 have ht:Tendsto d atTop (𝓝 (0:ℝ)):= h.mono_right nhdsWithin_le_nhds
 have e: ∀n:ℕ,∃ k:ℕ,∃y:Vantage,∃z:ℝ,k≥n ∧ ‖y‖ ≤ d n ∧ 0≤z ∧ z≤d n ∧ m < dist ((X%) k a) ((Λ k) y z ((X%) k a)):=by
    intro n
    obtain ⟨k,ge',y,v,z,r₀,r₁,f⟩:=frequently_atTop.1 (p n) n
    exact ⟨k,y,z,ge',v,r₀,r₁,f⟩
 choose k y z k' y' r₀ r₁ w using e
 have h₁:Tendsto y atTop (𝓝 0):= tendsto_zero_iff_norm_tendsto_zero.2 (squeeze_zero (fun i=>norm_nonneg _) y' ht)
 have z₀:= P.plume_flutter x V W R (cavalry a) (tendsto_atTop_mono k' tendsto_id) h₁ (squeeze_zero r₀ r₁ ht) r₀

 have w': Tendsto (fun n=>dist ((X%) (k n) a) ((Λ (k n)) (y n) (z n) ((X%) (k n) a))) atTop (𝓝 0):=by
    have ws:=z₀.const_mul ‖(squire a:ℂ)‖
    rw [mul_zero] at ws
    refine ws.congr fun i=>?_
    unfold plume
    symm;rw [map_smul,dist_eq_norm,dist_eq_norm,←smul_sub,norm_smul]
 exact (not_lt_of_ge (ge_of_tendsto w' (Eventually.of_forall fun n=>(w n).le))) u

