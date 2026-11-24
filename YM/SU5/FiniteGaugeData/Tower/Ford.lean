import YM.SU5.FiniteGaugeData.Tower.Chimes
import YM.SU5.FiniteGaugeData.Tower.Clouds
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 6000
set_option maxHeartbeats 500000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin
variable {Λ:Preparation}{l:ℕ}(Y:Course Λ (VolumeCape.Dream.Nimbus l))(H:Real.exp 1≤Λ.x)
local notation "K" => tent Y H
variable {i k:ℕ→ℕ}{I:ℕ→Family (tent Y H)→ℕ→ℂ}{E:ℕ→Family (tent Y H)→ℂ}(V:Universal Y H i k I E)(s:ℕ)
/-!
# Forward time in the one hierarchy

Initially on the discrete times compatible with the reflection system (step
8B in gauge units at resolution). Cross semigroup contraction needed on more
than individual stencils; here the stencils include the entire linear system
of marked tests. This contraction is of the *Hilbert vectors of the limiting
functional*, not of one-step lifts as matrices on physical links. The key
bound at large t comes from Corr-R (pair of bounded-width stencils regardless
of separation). Not assuming graded norm compactness with t moving.
-/
open scoped InnerProductSpace
open Fock Heat
variable {D:ℕ→Family (tent Y H)→Family (tent Y H)}(Q:Resolution (E:=E) Y H D)
variable (j:Axis)(z:ℤ)(strict:Bool)
local notation "m"=> meshface (Λ:=Λ) z s
variable (C:Arena Y H Q j z strict)
local notation "T" s:max=> Tower.Field Y H s j z strict
local notation "κ" s:max=>actor Y H s Q j z strict C
local notation "A"=> Ark.Ht Y H Q j z strict C
local notation "R" i:max=> mirror K j i
local notation "J" x:max=> gaugeShift Λ.block x


lemma region_flow {S:Finset Cover}(p:region j m (K).ℓ S)(q:ℕ): region j m (K).ℓ (address j (J (q:ℤ)) S):=by
 intro i b; obtain ⟨x,h,rfl⟩:= mem_image.mp b
 simp only [Pi.add_apply,Pi.smul_apply,step_apply]; simp only [ite_true]; specialize p x h; have he:0≤gaugeShift Λ.block q:=by unfold gaugeShift; positivity
 simp; linarith

local notation "Φ" k:max f:max=> chime K j (J k) f
private lemma front{f:T s}(u:ℕ): Φ (u:ℤ) f.val∈purpose K m j strict:=by
 obtain ⟨v,w⟩:= (purpose_ok ..).1 f.property
 obtain ⟨p,h,t⟩:= (v:∃ S:Finset Cover,InTest (tent Y H) true S false _∧ region j m (K).ℓ S)
 exact (purpose_ok ..).2 ⟨⟨address j (J (u:ℤ)) p,flow_port _ _ _ h,region_flow Y H s j z t u⟩,fun a=> chime_cov _ _ _ h (w a)⟩
private lemma freeze_test(f:T s):TestFamily K true f.val:=(exam j _ K ((purpose_ok ..).1 f.property).1).1

/-- One direction semigroup on raw marked vectors. -/
noncomputable def tick (i:ℕ): (Tower.Field Y H s j z strict) →ₗ[ℂ] Tower.Field Y H s j z strict where
 toFun f:= ⟨chime K j (Heat.gaugeShift Λ.block i) f.val, front Y H s j z strict i⟩
 map_add' f g:= Subtype.ext (chime_plus ..)
 map_smul' i x:=Subtype.ext (chime_scale ..)
local notation "Τ"=> tick Y H s j z strict
lemma tick_tock (a b:ℕ)(f:T s): Τ a (Τ b f)= Τ (a+b) f:=by
 apply Subtype.ext
 have he:Heat.gaugeShift Λ.block ((a+b:ℕ):ℤ)= Heat.gaugeShift Λ.block (a:ℤ)+Heat.gaugeShift Λ.block (b:ℤ):=by unfold gaugeShift; push_cast; ring
 change chime K j _ (chime _ _ _ _)=_
 change chime K j _ (chime _ _ _ _)=chime _ _ _ _
 rw [Tower.bumps K j _ _ (freeze_test Y H s j z strict f).paid.choose_spec,he]
lemma tick_seed (f:T s): Τ 0 f=f:=by apply Subtype.ext; change Φ (0:ℤ) f.val=f.val; rw [show (J (0:ℤ))=(0:ℤ) from by unfold Heat.gaugeShift; ring]; exact wake K _ (freeze_test Y H s j z strict f).paid.choose_spec
lemma tick_unit (i): Τ i (unity Y H j z strict s)=unity Y H j z strict s:=Subtype.ext (chime_unit K _ _)
include Q V
lemma tick_up (t:ℕ)(p:s≤t)(f:T s)(x:ℕ): tick Y H t j z strict (Λ.R.L.val^(t-s)*x) (Raise Y H Q j z strict s t p f) = Raise Y H Q j z strict s t p (Τ x f):=by
 apply Subtype.ext
 change chime K j (Heat.gaugeShift Λ.block ((Λ.R.L.val^(t-s)*x:ℕ):ℤ)) (stream Y H D s _ _) = stream Y H D s (t-s) (chime _ _ _ _)
 rw [chime_X Y H V s j x Q (freeze_test Y H s j z strict f)]; push_cast; rfl

include V C
lemma stems(s:ℕ)(x y:T s):inner ℂ ((κ s) x) ((κ s) y) = E s (mirror K j (meshface (Λ:=Λ) z s) x.val*y.val):=by
 rw [contracts Y H V Q j z strict C s s s le_rfl le_rfl,Nat.sub_self]; rfl
lemma shuttle (t:ℕ)(x y:T s): inner ℂ ((κ s) (Τ t x)) ((κ s) y)=inner ℂ ((κ s) x) ((κ s) (Τ t y)):=by
 rw [stems Y H V,stems Y H V]
 let k:= J (t:ℤ); have ht(y:T s):=freeze_test Y H s j z strict y
 let r(f:Family K):= mirror K j m f
 have hf(x:T s):TestFamily (tent Y H) true (r x.val):= (exam j _ K ((purpose_ok ..).mp x.property).1).2
 let g:= y.val; let f:=x.val
 have hp: chime K j k (r (chime K j k f)*g) =r f * chime K j k g:=by
    have x:= (ht x).paid.choose_spec
    rw [chime_product]; unfold r; rw [chime_diag K j k m (flow_port K j k x), Tower.bumps K j (-k) k x, neg_add_cancel,Tower.wake K j x]
 change E s (r (chime K j k f)*g)=E s (r f*chime K j k g)
 rw [←hp]; exact (SWay Y H V s j t ((hf (Τ t x)).mul (ht y))).symm

lemma collector_uniform (f:T s):∃ B:ℝ, ∀ t:ℕ, ‖(κ s) (Τ t f)‖ ≤ B:=by
 have ht:= freeze_test Y H s j z strict f
 obtain ⟨S,w⟩:= ht.paid
 obtain ⟨d,a⟩:=Tower.sizes S
 obtain ⟨X,x⟩:=Journey.valuation Y H w; have hx:pay f.val X:=x
 let B:=closefare K (duetCharge Y s) d*(X*X); refine ⟨B+1,fun t=>?_⟩
 let g:= (Τ t f).val
 let S':= reflectedBox j (J (t:ℤ)) (reflectedBox j 0 S)
 have hg:InTest K true S' false g:=axial K j _ (axial K j 0 w)
 have H':CompactArc S' d:= (a.reflBox S j 0).reflBox _ j _
 have hp:= pair_budget Y H V s d (axial K j m hg) hg (H'.reflBox S' j m) H' X X (pay_flips K (chime_pay K j _ X hx) j m) (chime_pay K j _ X hx)
 let u₀:= (κ s) (Τ t f); have he: ‖inner ℂ u₀ u₀‖ ≤ B:= (stems Y H V Q j z strict C s _ _).symm ▸ hp -- z shadow
 have hr:‖inner ℂ u₀ u₀‖=‖u₀‖^2:=by
    rw [inner_self_eq_norm_sq_to_K,norm_pow]; change ‖((‖u₀‖:ℝ):ℂ)‖^2= _; simp
 change ‖u₀‖≤_; rw [hr] at he; nlinarith [norm_nonneg u₀]

lemma ticks (t:ℕ)(f:T s): ‖(κ s) (Τ t f)‖≤‖(κ s) f‖:= by
 let X(i:ℕ):= (κ s) (Τ i f)
 obtain ⟨d,v⟩:= collector_uniform Y H V s Q j z strict C f
 let S:Set ℝ:= Set.range fun (i:ℕ)=> ‖X i‖
 have hS(x:ℕ): ‖X x‖∈ S:=Set.mem_range_self x
 have p: BddAbove S:= ⟨d, by rintro _ ⟨i,rfl⟩; exact v i⟩
 let B:= sSup S
 have he(i):‖X i‖≤ B:=le_csSup p (hS i)
 have hB:0≤ B:=(norm_nonneg _).trans (he t)
 let c:=‖(κ s) f‖; have hc:0≤c:=norm_nonneg _
 have h(i:ℕ): ‖X i‖^2≤ c*B:=by
    have ht:‖X i‖^2= ‖inner ℂ (X i) (X i)‖:=by rw [inner_self_eq_norm_sq_to_K,norm_pow]; change _=‖((‖X i‖:ℝ):ℂ)‖^2; simp
    change ‖X i‖^2 ≤ c*B; rw [ht, show inner ℂ (X i) (X i)=inner ℂ ((κ s) f) (X (i+i)) from (shuttle Y H V s Q j z strict C i f (Τ i f)).trans (congrArg _ (congrArg (κ s) (tick_tock Y H s j z strict i i f)))]
    exact (norm_inner_le_norm ..).trans (mul_le_mul_of_nonneg_left (he (i+i)) hc)
 refine (he t).trans ?_
 have ht:B ≤ Real.sqrt (c*B):=csSup_le ⟨_,hS t⟩ (by rintro _ ⟨i,rfl⟩; exact Real.le_sqrt_of_sq_le (h i))
 have h':= Real.sq_sqrt (mul_nonneg hc hB); change B ≤ c; nlinarith [Real.sqrt_nonneg (c*B)]

end YM.CF.Buffered.Afterglow.Tower
#print axioms YM.CF.Buffered.Afterglow.Tower.ticks
