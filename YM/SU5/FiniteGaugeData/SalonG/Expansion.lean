import YM.SU5.FiniteGaugeData.SalonG.Octave
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
namespace SalonG
open Nacre Heat Charm Chrono Journey
variable (a:Axis)(d n:ℕ)
variable {u v:ℕ→ℕ}{I:ℕ→Family (tent Y h)→ℕ→ℂ}{E:ℕ→ Family (tent Y h)→ℂ}{P:Call Λ l}{J:Wicket Λ l}
variable (W':Universal Y h u v I E)(R:Rolled Y h u v J P)
variable (A:Repertory Y h W' R a)
local notation "D"=> Decko Y h a
local notation "X"=> (A.space:Type)
local notation "M" t:max=> store Y h t W' R a A
local notation "π"=>nectar Y h s W' R a
local notation "N" n:max=> energyS Λ d n
variable {f x:W (tent Y h)}(z:Plan Y h a d f)(y:Decko Y h a)(q:0<d)
local notation "Θ"=> appointed Y h s a d
local notation "Ω" z:max n:max => appointed Y h s a d n W' R z
-- scale gallery.Admit bound for ALL using x width scaled.To later get actual sup. no D=0 required.
variable {c:ℂ} (B:ℝ)
local notation "σz"=> z.choose
abbrev venus := drift Kₜ (refract a (Heat.gaugeShift (Kₜ).B d) S) d (duetCharge Y s)
include q A W' R z
lemma tiny_v (t:Locator (tent Y h) f S) (r: SalonG.Width (tent Y h) f (venus Y h S s a d)): ‖store Y h (s+n) W' R a A (appointed Y h s a d n W' R z y)‖ ≤ ‖store Y h (s+n) W' R a A y‖:=by
 -- uses locator ANY. even if studio S not certificate.Chariot? loadSmall doesn't require. mint.
 exact weight Y h s a d n W' R A z y q (admit_low Y h (refract a (Heat.gaugeShift (Kₜ).B d) S) s a d W' (mateW Kₜ a d f) q (locate_cold Kₜ S a _ t) (fun m=> RealWidth.reflected a (r m) _))
lemma total_inv (b:0<B)(t:Locator Kₜ f S)(p:SalonG.Width (tent Y h) f (B*venus Y h S s a d)):
    ‖store Y h (s+n) W' R a A (appointed Y h s a d n W' R z y)‖ ≤ B*‖store Y h (s+n) W' R a A y‖:= by
 let c:ℂ:= ((B:ℂ)⁻¹); let w:=Plan.subsidy Y h z c; have hc:‖c‖=B⁻¹:=by unfold c; rw [norm_inv,Complex.norm_real,Real.norm_eq_abs,abs_of_pos b]
 let V:= venus Y h S s a d; have he:SalonG.Width (tent Y h) (c • f) V:=by intro m; have h:=RealWidth.smule (p m) c; rw [hc,inv_mul_cancel_left₀ b.ne'] at h; exact h
 have ht:=tiny_v Y h S s a d n W' R A w y q (locate_scale _ S _ t) he; rw [appoint_scale Y h s a d n W' R y z w,map_smul,norm_smul,hc] at ht; exact (inv_mul_le_iff₀ b).1 ht
-- default grant
abbrev cortege : ℝ := (duration z.choose * ‖reading Kₜ z.choose f z.choose_spec.2‖+1)/venus Y h z.choose s a d -- accidental q W' etc include!
#check cortege
lemma ceast : ∀ i, s ≤ i→ ‖store Y h i W' R a A (appointed Y h s a d (i-s) W' R z y)‖ ≤ cortege Y h s a d z* ‖store Y h i W' R a A y‖:= by
 let U:=z.choose; let u:=duration U; let x':= u* ‖reading Kₜ z.choose f z.choose_spec.2‖; let V:= venus Y h U s a d; have hv:0<V:= Real.exp_pos _; have ht:0 ≤ x':=mul_nonneg (duration_pos _).le (norm_nonneg _)
 intro i e; obtain ⟨i,rfl⟩:= Nat.exists_eq_add_of_le e; rw [Nat.add_sub_cancel_left]
 refine total_inv Y h U s a d i W' R A z y q ((x'+1)/V) (by positivity) z.choose_spec.2 ?_; intro m v; rw [div_mul_cancel₀ _ hv.ne']; exact (width_read z.choose_spec.2 _ _).trans (by linarith : x' ≤ x'+1)
-- bundle Scale with slack, no chosen plane precision beyond tick.
lemma cap (t:Locator Kₜ f S)(b:0<B)(p:SalonG.Width (tent Y h) f (B*venus Y h S s a d)):
 Robing Y h s W' R a A (fun i=> appointed Y h s a d (i-s) W' R z) B:= by
 constructor
 · intro n t y; obtain ⟨i,rfl⟩:= Nat.exists_eq_add_of_le t; rw [show s+i+1-s=i+1 from by omega,Nat.add_sub_cancel_left]; exact (appoint_next Y h s a d i W' R y z).symm -- args order??
 intro n t₁ y; obtain ⟨i,rfl⟩:= Nat.exists_eq_add_of_le t₁; rw [Nat.add_sub_cancel_left]; exact total_inv Y h S s a d i W' R A z y q B b t p
lemma Dreamrobe : Robing Y h s W' R a A (fun i=>appointed Y h s a d (i-s) W' R z) (cortege Y h s a d z):=by
 constructor
 · intro n v y; obtain ⟨i,rfl⟩:= Nat.exists_eq_add_of_le v; rw [show s+i+1-s=i+1 from by omega,Nat.add_sub_cancel_left]; exact (appoint_next Y h s a d i W' R y z).symm
 intro n t y; exact ceast Y h s a d W' R A z y q n t
/-- A BOUNDED slab Operator on ALL scales of this actual state and its Hilbert completion, width d>0. Cost.Budget and geometry necessary. -/
def Wedge: A.space.Op:= qubit Y h s W' R a A (fun i=> appointed Y h s a d (i-s) W' R z) (cortege Y h s a d z) (Dreamrobe Y h s a d W' R A z q) -- binder p? check using #check
lemma wedge_at (v:s ≤ i):(Wedge Y h s a d W' R A z q) ((M i) y)=(M i) (appointed Y h s a d (i-s) W' R z y):= qubit_seed Y h s i W' R a A y _ _ _ v
lemma wedge_plus : (Wedge Y h s a d W' R A z q) ((M (s+n)) y)=(M (s+n)) (appointed Y h s a d n W' R z y):=by rw [wedge_at Y h s _ a d W' R A z y q (by omega),Nat.add_sub_cancel_left]
lemma wedge_here : (Wedge Y h s a d W' R A z q) ((M s) y)=(M s) (embark Y h a d z y):=by rw [wedge_at Y h s s a d W' R A z y q le_rfl,Nat.sub_self,appointing]
lemma wedge_bound (t:Locator (tent Y h) f S)(b:0<B)(p:SalonG.Width (tent Y h) f (B*venus Y h S s a d)): ‖Wedge Y h s a d W' R A z q‖ ≤ B:=by
 let F(i:ℕ):= appointed Y h s a d (i-s) W' R z; let u:= cap Y h S s a d W' R A z q B t b p
 have he:Wedge Y h s a d W' R A z q=qubit Y h s W' R a A F B u:= lens_ext Y h s W' R a A fun i v x=> (wedge_at Y h s i a d W' R A z x q v).trans (qubit_seed Y h s i W' R a A x F B u v).symm
 rw [he]; exact qubit_norm Y h s W' R a A F B u b.le

lemma wedge_mint (p:Gallery Y h s a d u v f) : ‖Wedge Y h s a d W' R A z q‖ ≤ 1:= by
 let T':= Wedge Y h s a d W' R A z q
 refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one (warm_lift Y h s a d 0 W' R A (fun v:X=> ‖T' v‖≤ 1*‖v‖) (isClosed_le (T'.continuous.norm) (by fun_prop)) fun i _ x=>?_)
 unfold T'; rw [wedge_plus,one_mul]; exact valued Y h s a d i W' R A x z q p
#print axioms Wedge
#print axioms wedge_mint
end SalonG
end YM.CF.Buffered.Afterglow.Hierarchy
