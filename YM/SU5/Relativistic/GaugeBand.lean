import YM.SU5.Relativistic.Shores
set_option autoImplicit false
set_option quotPrecheck false
set_option synthInstance.maxSize 26000
set_option maxHeartbeats 600000
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.Reconstruction.FermionSlab
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common Fock
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder NNReal ENNReal Classical InnerProductSpace
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin
variable {Λ:Preparation}{l:ℕ}(Y:Course Λ (VolumeCape.Dream.Nimbus l))(H:Real.exp 1≤Λ.x)
local notation "K" => tent Y H
variable {i k:ℕ→ℕ}{I:ℕ→Family (tent Y H)→ℕ→ℂ}{E:ℕ→Family (tent Y H)→ℂ}(V:Universal Y H i k I E)
local notation "W"=>wingspan Λ l

variable {D:ℕ→Family (tent Y H)→Family (tent Y H)}{a b:ℕ→ℕ}(Q:Coherent (i:=i) (k:=k) (E:=E) Y H D a b)(u:ℕ→ℕ)(p: StrictMono u)
local notation "A" r:max=>i (a (u r))
local notation "B" r:max=>k (b (u r))
local notation "L₁" r:max s:max S:max b':max => moveUp Y H s (i (a (u r))) (k (b (u r))) S b'
local notation "Σ₀"=>Bedside Y H (i:=i) (k:=k) (a:=a) (b:=b)

variable (s:ℕ)
-- recover ALL norms via tail calibration.
variable {S:Finset Cover}{b':Bool}
include Q V p
lemma uniformBand (h: ∃ m:Side,Tivoli (wingspan Λ l S) ((K).c m) ∧ Σ₀ s b' S m u): ∃ c:ℝ,∃ F:Family (tent Y H) → Family (tent Y H), 0<c ∧
    (∀ x,InTest K true S b' x → InTest K true (W S) b' (F x)∧ ∀ y:ℝ,pay x y→pay (F x) (c*y))∧
    ∀ e:ℝ,0<e→∀ᶠ j:ℕ in atTop, ∀ x,InTest K true S b' x→∀ y:ℝ,pay x y→pay ((L₁ j s S b') x) (c*y)∧pay ((L₁ j s S b') x-F x) (e*y):=by
 obtain ⟨m,v,x⟩:=h; obtain ⟨c,F,g,f',l'⟩:=shore Y H V Q u p s S m v x
 let G i:= moveUp Y H s (A i) (B i) S b'
 have dates: ∀ᶠ j in atTop, legalAt Y s (A j) (B j) ∧ Tivoli (W S) ((K).c (momentm Y (A j) (s+1))):=
    (p.tendsto_atTop.eventually (Q.finance (s+1))).mono (fun i h=> ⟨h.depth,h.enters⟩) |>.and ((V.pick.grow_i.tendsto_atTop.comp (Q.growsA.tendsto_atTop.comp p.tendsto_atTop)).eventually (turning Y H (s+1) (W S)))
 have ht {f:Family (tent Y H)}{y:ℝ}(a:0<y)(k:pay f y): pay ((y:ℂ)⁻¹ • f) 1:=fun i j=>(pay_scale k (y:ℂ)⁻¹ i j).trans_eq (by simp [abs_of_pos a, inv_mul_cancel₀ a.ne'])
 let X:= {z:Family K // InTest K true S b' z}
 have len(v:X) :∃ k:ℝ,0<k∧ pay v.val k:=by obtain ⟨a,t⟩:= Journey.valuation Y H v.property; exact ⟨max 1 a,lt_max_of_lt_left (by norm_num),fun i V=>(t ..).trans (le_max_right ..)⟩
 let T (v:X)(c:ℝ)(a:0<c)(h:pay v.val c):= (show Rough b' (tent Y H) S from ⟨(c:ℂ)⁻¹ • v.val, InTest.smul _ v.property, ht a h⟩)
 let R (v:X):Family K:=( ( (len v).choose:ℂ) • F (T v (len v).choose (len v).choose_spec.1 (len v).choose_spec.2))
 have costs(v:X)(y:ℝ)(a:0<y)(k:pay v.val y) (z:Side)(x:Fields ((K).c z)): Tendsto (fun i:ℕ=> G i v.val z x) atTop (𝓝 (((y:ℂ) • F (T v y a k)) z x)):=by
    have he:Tendsto (fun i:ℕ=> G i (T v y a k).val z x) atTop (𝓝 (F (T v y a k) z x)):=by
       refine Metric.tendsto_nhds.mpr fun ε p=>?_
       filter_upwards [l' _ (half_pos p)] with i u; rw [dist_eq_norm]; exact ((u (T v y a k)).2 z x).trans_lt (half_lt_self p)
    refine (he.const_smul (y:ℂ)).congr' ?_
    filter_upwards [dates] with i h; change _ • (G _ ((y:ℂ)⁻¹ • v.val)) z x=_
    rw [show G i ((y:ℂ)⁻¹ • v.val)=_ from scaleMove Y H s _ _ h.1 h.2 v.property _, Pi.smul_apply,Pi.smul_apply,smul_smul,mul_inv_cancel₀ (show (y:ℂ)≠0 by exact_mod_cast a.ne'),one_smul]
 have rate(v:X)(y:ℝ)(a:0<y)(k:pay v.val y): R v=(y:ℂ) • F (T v y a k):=funext fun z=> funext fun x=> tendsto_nhds_unique (costs v _ (len v).choose_spec.1 (len v).choose_spec.2 z x) (costs v y a k z x)
 have Rt (v:X) : InTest K true (W S) b' (R v):= InTest.smul _ (f' _).1
 have Θ (v:X): ∀ z:Side,∀ x:Fields ((K).c z), Tendsto (fun i=>G i v.val z x) atTop (𝓝 (R v z x)):=fun z x=>costs v _ (len v).choose_spec.1 (len v).choose_spec.2 z x
 have Hn{v:X} (t:pay v.val 0) : v.val=0:= funext fun i=>funext fun x=> norm_eq_zero.mp (le_antisymm (t i x) (norm_nonneg _))
 have Zr:∀ᶠ j:ℕ in atTop, G j 0=0:=dates.mono fun i h=>by
    simpa only [zero_smul] using scaleMove Y H s (A i) (B i) h.1 (S:=S) h.2 (b:=b') (InTest.zero («K»:=tent Y H)) 0 -- pvar
 have Hr (v:X)(t:pay v.val 0) : R v=0:=by
    funext m z; exact tendsto_nhds_unique_of_eventuallyEq (Θ v m z) (tendsto_const_nhds (x:=(0:FC _))) (Zr.mono fun i k=>by change G i v.val m z=0; rw [Hn t,k]; rfl)
 let R' (f:Family K):= if v:InTest K true S b' f then R (⟨f,v⟩:X) else 0
 refine ⟨c,R',g,fun f p=>⟨?_ ,fun y h=>?_⟩,fun e t=>?_⟩
 · rw [show R' f=R (⟨f,p⟩:X) from dif_pos p]; exact Rt _
 · let f0:X:=⟨f,p⟩; rw [show R' f=R f0 from dif_pos p]
   rcases (pay_nonneg h).eq_or_lt with p'|p'
   · rw [← p', Hr f0 (p'.symm ▸ h)]; intro i x; simp
   rw [rate f0 y p' h]; intro i x; exact ((pay_scale (f' (T f0 y p' h)).2 (y:ℂ)) i x).trans_eq (by rw [Complex.norm_real,Real.norm_eq_abs,abs_of_pos p',mul_comm y])
 filter_upwards [l' _ t,dates,Zr] with j k t' h' f Px y h
 let U:X:=⟨f,Px⟩; rw [show R' f=R U from dif_pos Px]; change pay (G j f) _ ∧ pay (G j f-R U) _
 rcases (pay_nonneg h).eq_or_lt with p'|p'
 · have hz:= Hr U (p'.symm ▸ h); rw [hz, show f=0 from Hn (v:=U) (p'.symm ▸ h),h', ←p',sub_self]; constructor<;> intro i x' <;> simp
 · rw [rate U y p' h]; obtain ⟨g',q'⟩:=k (T U y p' h)
   let d:=T U y p' h
   have s0: G j f=(y:ℂ) • G j d.val:= by
      change G j f=(y:ℂ) • G j ((y:ℂ)⁻¹ • f)
      rw [show G j ((y:ℂ)⁻¹ • f)= _ from scaleMove _ _ _ _ _ t'.1 t'.2 Px _, smul_smul,mul_inv_cancel₀ (show (y:ℂ)≠0 by exact_mod_cast p'.ne'),one_smul]
   change pay (G j f) _ ∧ pay (G j f-(y:ℂ) • F d) _
   rw [s0, ←smul_sub]; constructor
   · intro i x; exact ((pay_scale g' (y:ℂ)) i x).trans_eq (by rw [Complex.norm_real,Real.norm_eq_abs,abs_of_pos p',mul_comm y])
   intro i x; exact ((pay_scale q' (y:ℂ)) i x).trans_eq (by rw [Complex.norm_real,Real.norm_eq_abs,abs_of_pos p',mul_comm y])

end YM.CF.Buffered.Afterglow.Tower.Reconstruction.FermionSlab
