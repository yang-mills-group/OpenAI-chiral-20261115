import YM.SU5.FiniteGaugeData.KernelP.Apex
set_option autoImplicit false
set_option synthInstance.maxSize 24000
noncomputable section
namespace YM.CF.Buffered.Afterglow.Hierarchy
open Function Filter NormedSpace SU Lat Lattice Cube Finset MeasureTheory RG Wilson Metric
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Kronecker Topology ComplexOrder
open Rush Scroll Peaks Stencil Tenant Tap Tulip Branch Fir Scree Advance Reflect Window Laurent Next.Free Bloch Drapes Spire Lifted Skye Sound Precision Tree Push.SectorMeasure Next.SectorChange Common Fock Pastry Satin
open Reed (Fine)
attribute [local instance] opCStarAlgebra
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
open Nacre Heat Charm Chrono SalonG Journey Hills Playlist Show
namespace KernelP
variable {u v:ℕ→ℕ}{I:ℕ→Family (tent Y h)→ℕ→ℂ}{E:ℕ→ Family (tent Y h)→ℂ}{P:Call Λ l}{J:Wicket Λ l}
variable (W':Universal Y h u v I E)(R:Rolled Y h u v J P)(A:∀ a:Axis,Repertory Y h W' R a)
variable {Φ:ℕ→ Charm.W (tent Y h)→ₗ[ℂ]ℂ}(S':Sphere Y h W' R A Φ)
variable (a:Axis)(z:ℤ)(d n:ℕ)
local notation "D"=> Decko Y h a
variable (H:Harbor Y h W' R Φ a)(x y:Decko Y h a)
local notation "Λ₀"=> (A a)
local notation "V"=> H.space
local notation "P" i:max=> H.leaf i
variable {f g:W (tent Y h)}(u':Plan Y h a d f)(q:0<d)
local notation "J₁"=> Wedge Y h s a d W' R (A a) u' q
local notation "Σ" i:max=> appointed Y h s a d i W' R u'
include S' H u' q
omit S' H u' q in
private lemma cfa {H:Hilbert}(x y:H)(w:ℝ)(p:0≤w)(h: inner ℂ x x≤ (w:ℂ)^2 • inner ℂ y y): ‖x‖ ≤ w * ‖y‖:=by
 have he: (w:ℂ)^2 • inner ℂ y y= inner ℂ ((w:ℂ) • y) ((w:ℂ) • y):=by rw [inner_smul_left,inner_smul_right, Complex.conj_ofReal,sq, smul_eq_mul,mul_assoc] -- lhs smul
 rw [he] at h; have ht:=(moneyB _ _).1 h; rwa [norm_smul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg p] at ht
private lemma control : Codec Y h s W' R a H (fun i=>appointed Y h s a d (i-s) W' R u') ‖Wedge Y h s a d W' R (A a) u' q‖:= by
 constructor
 · intro n t x; obtain ⟨i,rfl⟩:= Nat.exists_eq_add_of_le t; rw [show s+i+1-s=i+1 from by omega,Nat.add_sub_cancel_left]; exact (appoint_next Y h s a d i W' R x u').symm
 intro i v x; obtain ⟨i,rfl⟩:= Nat.exists_eq_add_of_le v; rw [Nat.add_sub_cancel_left]; refine cfa (H:=V) _ _ _ (norm_nonneg _) ?_; rw [H.measure,H.measure]; have hx:= energy_h Y h a d i W' R (A a) u' q; rw [met_coherent Y h s a d i W' R (A a) u' q]; exact S'.spread (s+i) a _ x _ (Plan.rides Y h s i W' R u') hx

def bitOp : H.space.Op:= criterion Y h s W' R a H _ _ (control Y h s W' R A S' a d H u' q)
local notation "f'" n:max x:max=>bitOp Y h s W' R A S' a n H x
local notation "W₀"=> W Kₜ
lemma operation_le : ‖bitOp Y h s W' R A S' a d H u' q‖≤ ‖J₁‖:= criterion_norm Y h s W' R a H _ _ _ (norm_nonneg J₁) -- budget nonneg
lemma bitPlus : bitOp Y h s W' R A S' a d H u' q (H.leaf (s+n) x) = H.leaf (s+n) (appointed Y h s a d n W' R u' x):= by
 unfold bitOp; rw [criterion_seed Y h s _ W' R a H _ _ _ _ (by omega)]; simp only [Nat.add_sub_cancel_left]
lemma bit_here : bitOp Y h s W' R A S' a d H u' q (H.leaf s x)= H.leaf s (embark Y h a d u' x):= by
 have he:= bitPlus Y h s W' R A S' a d 0 H x u' q; rw [appointing,Nat.add_zero] at he; exact he
lemma bit_sure (e:Plan Y h a n g)(p:0<n): bitOp Y h s W' R A S' a d H u' q*bitOp Y h s W' R A S' a n H e p= bitOp Y h s W' R A S' a (d+n) H (couplePlan Y h a d n u' e) (by omega):=by
 apply leaf_ext Y h s W' R a H (H':=V); intro i v u; obtain ⟨i,rfl⟩:= Nat.exists_eq_add_of_le v; rw [mul_apply_eq_comp,bitPlus,bitPlus,bitPlus]; apply congrArg; apply Subtype.ext; rw [appointed_val,appointed_val,appointed_val,ascend_swing Y h s a d n W' R u' e _]; unfold Swing; rw [clock_mul,clock_add,← mul_assoc, show energyS Λ (d+n) i= energyS Λ d i+energyS Λ n i from mul_add ..,Nat.cast_add]
omit S' u' q in
lemma steer_ext {x y : V}(p:∀ i:ℕ, k≤ i→∀ x':Decko Y h a,inner ℂ x (H.leaf i x')=inner ℂ y (H.leaf i x')): x=y:= by apply ext_inner_right ℂ; apply leaf_lift Y h k W' R a H {v:V | inner ℂ x v=inner ℂ y v} (isClosed_eq (by fun_prop) (by fun_prop)) p
private lemma steer_ab : inner ℂ (H.leaf (s+n) y) (bitOp Y h s W' R A S' a d H u' q (H.leaf (s+n) x)) = inner ℂ (bitOp Y h s W' R A S' a d H (Plan.other Y h u') q (H.leaf (s+n) y)) (H.leaf (s+n) x):=by
 rw [bitPlus,bitPlus,H.measure,H.measure]; let b:= energyS Λ d n; let g:= ascended Y h s W' R n f
 change Φ (s+n) (Fold Kₜ a 0 y.val (Swing Kₜ a b g x.val)) =Φ _ (Fold Kₜ a 0 (Swing Kₜ a b _ y.val) x.val); rw [adjoint_frame,S'.color]; dsimp only [b,g]; rw [iceWing] -- reduction explicit missing metavariable
set_option maxHeartbeats 420000 in
lemma bit_star : star (bitOp Y h s W' R A S' a d H u' q) = bitOp Y h s W' R A S' a d H (Plan.other Y h u') q:=by
 apply leaf_ext Y h s W' R a H (H':=V); intro i v y; apply steer_ext Y h i W' R a H; intro k t x; obtain ⟨y,w⟩:= H.upwards Y h i k W' R a y t; rw [← w]; obtain ⟨k,rfl⟩:= Nat.exists_eq_add_of_le (v.trans t); rw [ContinuousLinearMap.star_eq_adjoint,ContinuousLinearMap.adjoint_inner_left]; exact steer_ab Y h s W' R A S' a d k H x y u' q -- ack relation unfold Fold? inspect
#print axioms bit_star
end KernelP
end YM.CF.Buffered.Afterglow.Hierarchy
