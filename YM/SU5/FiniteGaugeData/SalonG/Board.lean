import YM.SU5.FiniteGaugeData.SalonG.Switchyard
set_option autoImplicit false
set_option synthInstance.maxSize 24000
set_option synthInstance.maxHeartbeats 72000
set_option maxHeartbeats 1400000
noncomputable section
namespace YM.CF.Buffered.Afterglow.Hierarchy
open Function Filter NormedSpace SU Lat Lattice Cube Finset MeasureTheory RG Wilson Metric
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Kronecker Topology ComplexOrder
open Rush Scroll Peaks Stencil Tenant Tap Tulip Branch Fir Scree Advance Reflect Window Laurent Next.Free Bloch Drapes Spire Lifted Skye Sound Precision Tree Push.SectorMeasure Next.SectorChange Common Fock Pastry Satin
open Reed (Fine)
attribute [local instance] opCStarAlgebra
namespace SalonG
open Nacre Heat Charm Chrono Journey
section rank
variable (K:Calibration)(m:Side)(a:Axis)(z:ℤ)
local notation "η"=> K.ℓ
local notation "ν"=> K.c m
-- universal finite read calculus. enough for train proof and later adaptive marks
abbrev role (x:W K):Prop:= AtSupport false (band (K.c m) a z K.ℓ) (x.val m)
lemma role_loc {S:Finset Cover}{x:W K}(p:Locator K x S)(u:later z (K.c m) S a K.ℓ): role K m a z x:= ((show InTest _ _ _ _ _ from p).support m).mono u
local notation "B"=> role K m a z
def cantor : Submodule ℂ (W K) where
 carrier:={x|role K m a z x}
 zero_mem' := AtSupport.zeroM
 add_mem' := fun p u=> AtSupport.addM p u
 smul_mem' := fun z x p=> AtSupport.smulM p z
-- expose axioms on W
variable {L:Loom (K.c m)}{D:ℝ}(X: W K→ₗ[ℂ] ℂ){X':Mark (K.c m)→ℂ}
structure Equity (K:Calibration)(m:Side)(L:Loom (K.c m))(X:W K→ₗ[ℂ]ℂ)(D:ℝ):Prop where
 pays : ∃ Y:Mark (K.c m)→ℂ,Metered K m L Y D∧∀ f:W K,Y (f.val m)=X f
 sails i z f: X (clockW K i z f)=X f
variable (E:Equity K m L X D)
set_option quotPrecheck false
local notation "C"=> ↥(cantor K m a z)
local notation "F"=> Fold K a z
def soarBand : (cantor K m a z) →ₗ⋆[ℂ] ((cantor K m a z)→ₗ[ℂ]ℂ) where
 toFun (v:C):={ toFun (w:C):= X (F v.val w.val)
                map_add' (x y:C):=by rw [Submodule.coe_add, Fold, mul_add,map_add]
                map_smul' (c:ℂ)(x:C):=by rw [Submodule.coe_smul, Fold, Algebra.mul_smul_comm,map_smul]; rfl }
 map_add' x y:= LinearMap.ext (fun (w:C)=> by change X (F (x+y).val w.val)= X (F _ _) + X (F _ _); rw [Submodule.coe_add,Fold,ice_more,add_mul,map_add])
 map_smul' c v:= LinearMap.ext (fun (w:C)=> by change X (F (c • v).val w.val) = star c • X (F v.val w.val); rw [Submodule.coe_smul,Fold,ice_paid,Algebra.smul_mul_assoc,map_smul])
abbrev Level (K:Calibration)(z:ℤ): Prop:=∃ s:ℤ,z=gaugeShift K.B s
lemma level_zero : Level K 0:= ⟨0,(by unfold gaugeShift; simp)⟩
variable (p: Level K z)
include p E
lemma Equity.rank {x:W K}(t:role K m a z x): 0 ≤ X (Fold K a z x x):=by
 obtain ⟨s,rfl⟩:=p; obtain ⟨x',g,b⟩:=E.pays; rw [← b]; exact g.fund a s (x.val m) t
lemma Equity.royal {x y: W K}(t:role K m a z x)(q:role K m a z y): ‖X (Fold K a z x y)‖^2 ≤ ‖X (Fold K a z x x)‖*‖X (Fold K a z y y)‖:=by
 obtain ⟨W'⟩:= throne (soarBand K m a z X) (fun (x:C)=> rank K m a z X E p x.property)
 let T (x:C):= W'.paid x; let u:C:= ⟨x,t⟩; let v:C:=⟨y,q⟩; have he(x y:C): X (Fold K a z x.val y.val)=inner ℂ (T x) (T y):= (W'.folding x y).symm
 have hv(x:W'.space): ‖inner ℂ x x‖=‖x‖^2:= by rw [inner_self_eq_norm_sq_to_K]; change ‖(↑‖x‖:ℂ)^2‖=_; rw [←Complex.ofReal_pow,Complex.norm_real]; exact Real.norm_of_nonneg (sq_nonneg _)
 change ‖X (F u.val v.val)‖^2≤ ‖X (F u.val u.val)‖*‖X (F v.val v.val)‖
 rw [he,he u,he v,hv,hv]; exact le_trans (pow_le_pow_left₀ (norm_nonneg _) (norm_inner_le_norm ..) _) (mul_pow ..).le
lemma Equity.separated {x y: W K}{S T:Finset Cover}(t:Locator K x S)(q:Locator K y T) (h:later z (K.c m) (refract a z S) a K.ℓ)(e:later z (K.c m) T a K.ℓ):
    ‖X (x*y)‖^2≤ ‖X (x*fire K a z x)‖*‖X (fire K a z y*y)‖ := by
 have H:= Equity.royal K m a z X E p (role_loc K m a z (locate_cold K _ _ _ t) h) (role_loc K m a z q e); unfold Fold at H; simpa only [burning_ice] using H
-- convert rank to bound linear slope
omit p
local notation "X0" d:max n:max f:max x:max => openQ K a d n f x
variable (d H₁ n:ℕ) (f x:W K)(V:∀ k'≤ H₁,role K m a 0 (openQ K a d k' f x))
include E V
local notation "ω" n:max => X (Fold K a 0 (openQ K a d n f x) (openQ K a d n f x))
lemma Equity.convex (u:n+2≤ H₁): (ω (n+1)).re + (ω (n+1)).re ≤ (ω n).re + (ω (n+2)).re:=by
 let Z:= Fold K a 0
 let v:= openQ K a d n f x; let y:= openQ K a d (n+2) f x
 let t:= soarBand K m a 0 X
 have he (x y:cantor K m a 0):t x y=X (Fold K a 0 x.val y.val):= rfl
 let v':cantor K m a 0:=⟨v,V n (by omega)⟩; let y':cantor K m a 0:=⟨y,V _ u⟩
 have hx (x:cantor K m a 0):0≤t x x:= E.rank K m a 0 X (level_zero _) x.property -- args tune dot
 have hz:=hx (v'-y'); rw [map_sub t,LinearMap.sub_apply,map_sub (t v'),map_sub (t y')] at hz
 have hg:t v' y'=ω (n+1):=by
    rw [he]; unfold y'; change X (Fold K a 0 (openQ K a d n f x) (openQ K a d (n+1+1) f x))= _; rw [operate_succ,adjoint_frame,E.sails,ream_alt,mate_self,← operate_succ]
 have hk:t y' v'=ω (n+1):= by
    rw [(screenshots.{0,0} t hx).1 y' v',hg]; exact (Complex.conj_eq_iff_im.mpr (Complex.le_def.mp (E.rank K m a 0 X (level_zero _) (V (n+1) (by omega)))).2.symm) -- lemma?
 rw [hg,hk] at hz; change 0≤ (ω n) - _ - (_-(ω (n+2))) at hz; replace hz:=(Complex.le_def.mp hz).1; simp only [Complex.zero_re,Complex.sub_re] at hz; linarith
lemma Equity.slope : (H₁:ℝ)*((ω 1).re-(ω 0).re) ≤ (ω H₁).re:= by
 have he(n:ℕ)(t:n+1 ≤ H₁): (ω 1).re-(ω 0).re ≤ (ω (n+1)).re-(ω n).re:=by
    induction n with
    | zero=> rfl
    | succ n ih=> have h:=ih (by omega); have v:=E.convex K m a X d H₁ n f x V t; linarith
 have hg(n:ℕ)(t:n ≤ H₁): (n:ℝ)*((ω 1).re-(ω 0).re) ≤ (ω n).re:=by
    induction n with
    | zero=> rw [Nat.cast_zero,zero_mul]; exact (Complex.le_def.mp (E.rank K m a 0 X (level_zero _) (V 0 t))).1
    | succ n ih=> have h:= ih (by omega); have v:=he n t; rw [Nat.cast_succ]; linarith
 exact hg H₁ le_rfl
#print axioms Equity.slope
end rank
open Py Py.Rate LocalLimit Preparation Journey Fiber Vale VolumeCape FullBill
set_option quotPrecheck false
variable {Λ:Preparation}{l:ℕ}(Y:Course Λ (VolumeCape.Dream.Nimbus l))(h:Real.exp 1≤ Λ.x)
local notation "Kₜ"=> tent Y h
local notation "N₁" i:max s:max=> side Y i s
local notation "Wₐ" i:max s:max => (Y.voyage i).CapeT s
local notation "D₀"=> aliasLaw Λ
local notation "D₁"=> distanceLaw l
local notation "L₁"=> Λ.R.L
local notation "C₀"=> (VolumeCape.Dream.plot l).C
local notation "Xᵣ" i:max k:max=> (Y.voyage i).X (Y.uv k)
local notation "Tᵣ" i:max k:max s:max=> ((Y.voyage i).X (Y.uv k)).gram s
variable (S T: Finset Cover)(s i k:ℕ)
variable {S T} in
-- for heat records
abbrev heatX (p:Ferry Y s i k) : W (tent Y h)→ₗ[ℂ]ℂ where
 toFun x:= hot Y h s i k x.val
 map_add' x y:= hot_add _ _ _ (well_for Kₜ x).1 (well_for Kₜ y).1 p -- `fun` omitted binder OK
 map_smul' c f:= hot_mul (f:=f.val) _ _ _ c p
lemma Equity.record (p:Ferry Y s i k): Equity (tent Y h) (momentm Y i s) (deltaL Y h i s) (heatX Y h s i k p) (duetCharge Y s):=by
 let he := boxprice Y h i k p.depth s p.fire p.enters
 have hv (x:W Kₜ): heatX Y h s i k p x=collector Y h i k p.depth s (x.val (momentm Y i s)):= dif_pos p.depth
 exact ⟨⟨_,he,fun f=>(hv f).symm⟩, fun a z f=>by rw [hv,hv,collector_tick Y h s i k a z p f]⟩
#print axioms Equity.royal
end SalonG
end YM.CF.Buffered.Afterglow.Hierarchy
