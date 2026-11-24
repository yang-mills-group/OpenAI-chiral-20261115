import YM.SU5.FiniteGaugeData.Chrono.Elara
import YM.Hilbert.Kolmogorov
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
variable {v u:ℕ→ℕ}{I:ℕ→Family (tent Y h)→ℕ→ℂ}{E:ℕ→Family (tent Y h)→ℂ}{P:Call Λ l}{J:Wicket Λ l}
namespace Chrono
open Nacre Heat Charm Playlist Show
variable (R:Universal Y h u v I E)(L:Rolled Y h u v J P)(a j:Axis)
local notation "η"=> reserve Λ l
section
open UniformSpace UniformSpace.Completion
variable {V:Type}[AddCommGroup V][Module ℂ V](f:V →ₗ⋆[ℂ] V→ₗ[ℂ] ℂ)
structure Den (f: V →ₗ⋆[ℂ] V→ₗ[ℂ] ℂ) where
 space : Hilbert
 paid: V→ₗ[ℂ] space
 issued : DenseRange paid
 folding x y: inner ℂ (paid x) (paid y)= f x y

theorem throne (p:∀ x,0≤f x x): Nonempty (Den f):=by
 letI F : PreInnerProductSpace.Core ℂ V := {
    inner x y:= f x y
    conj_inner_symm x y:= (screenshots.{0,0} f p).1 x y|>.symm
    add_left x y z:= by change f (x+y) z = _; rw [map_add]; rfl
    smul_left x y c:=by change f (c•x) y= _; rw [map_smulₛₗ f]; rfl  -- binder order
    re_inner_nonneg x:= (p x).1 }
 letI C : SeminormedAddCommGroup V := InnerProductSpace.Core.toSeminormedAddCommGroup (𝕜:=ℂ)
 letI : InnerProductSpace ℂ V:= InnerProductSpace.ofCore F
 let X:Hilbert:= { space:= Completion V }
 let y: V→ₗ[ℂ] X:= { toFun v:= Completion.coe' v, map_add':=Completion.coe_add, map_smul':=Completion.coe_smul }
 exact ⟨⟨X,y,Completion.denseRange_coe, Completion.inner_coe⟩⟩
end
-- plant and Pulse. V all mixed at plane 0.
abbrev Repertory := Den (beams Y h R L a 0)
def Agora : Repertory Y h R L a:= Classical.choice (throne (beams Y h R L a 0) (gleam Y h R L a 0))
variable (A:Repertory Y h R L a)
local notation "X"=> (A.space)
local notation "V"=> Vect Y h a 0
local notation "U"=> Decko Y h a
variable (w z: Vect Y h a 0)
include A
lemma calcRead (t:Arrive Y h w.val s)(u:Arrive Y h z.val s): inner ℂ (A.paid w) (A.paid z)= E s (helve Kₜ a (days Y h s R L a w).val (days Y h s R L a z).val).val:= (A.folding w z).trans (beams_days Y h s R L a w z t u)
-- hence compression agrees EXACT as Hilb-classes
omit A in
private lemma eqHop {H₁:Hilbert}{x y:H₁}(p:inner ℂ x x=inner ℂ y x)(q:inner ℂ x y=inner ℂ y y):x=y:=sub_eq_zero.mp ((inner_self_eq_zero (𝕜:=ℂ)).mp (by rw [inner_sub_right,inner_sub_left,inner_sub_left,p,q,sub_self,sub_self,sub_zero])) -- omit? order
lemma abode (t:Arrive Y h w.val s): A.paid (seedling Y h s a ((days Y h s R L a) w)) = A.paid w:= by
 let F:= seedling Y h s a ((days Y h s R L a) w); have p:Arrive Y h F.val s:= pulse_arr Y h s ((days Y h s R L a) w).val; have he(x:Vect Y h a 0)(u: Arrive Y h x.val s):inner ℂ (A.paid F) (A.paid x)=inner ℂ (A.paid w) (A.paid x):=by rw [calcRead Y h s R L a A F x p u,calcRead Y h s R L a A w x t u,show (days Y h s R L a) F=(days Y h s R L a) w from fullDay ..]
 exact eqHop (he F p) (he w t)

private abbrev cashier (x:Decko Y h a):=A.paid (seedling Y h s a x)
variable (x y:Decko Y h a)
lemma lawSeed : inner ℂ (cashier Y h s R L a A x) (cashier Y h s R L a A y)= E s (helve Kₜ a x.val y.val).val:=by unfold cashier; rw [calcRead Y h s R L a A,fullDay,fullDay]; all_goals exact pulse_arr Y h s _ -- syntax
private lemma torch (x:W (tent Y h)) : Show.sight Y h s R x=E s x.val:=rfl
private lemma seekSum : cashier Y h s R L a A (x+y)=cashier Y h s R L a A x+cashier Y h s R L a A y:=by
 let B:= cashier Y h s R L a A; let z:=x+y; have he(t: Decko Y h a) : inner ℂ (B z) (B t)= inner ℂ (B x + B y) (B t) := by
    unfold B z; rw [inner_add_left]; simp_rw [lawSeed, ← torch Y h s R L a A]; unfold helve; rw [Subalgebra.coe_add,ice_more,add_mul,map_add]
 apply eqHop; exact he z; rw [inner_add_right,inner_add_right,he x,he y]
private lemma seekScale (c:ℂ):cashier Y h s R L a A (c • x) =c • cashier Y h s R L a A x:=by
 let B:= cashier Y h s R L a A; let z:=c • x; have he(t: Decko Y h a) : inner ℂ (B z) (B t)= inner ℂ (c • B x) (B t):= by
    unfold B z; rw [inner_smul_left]; simp_rw [lawSeed, ← torch Y h s R L a A]; unfold helve; rw [Subalgebra.coe_smul,ice_paid,Algebra.smul_mul_assoc,map_smul]; rfl
 apply eqHop; exact he z; rw [inner_smul_right, inner_smul_right, he x]

def store: Decko Y h a →ₗ[ℂ] A.space where
 toFun:= cashier Y h s R L a A
 map_add' x y:= seekSum ..
 map_smul' c x:= seekScale ..
local notation "F'" s:max=> store Y h s R L a A

lemma clapper : (F' s) x=A.paid (seedling Y h s a x):= rfl
lemma contains (p: Arrive Y h w.val s): (F' s) ((days Y h s R L a) w)= A.paid w := abode Y h s R L a A w p
lemma lawStore : inner ℂ ((F' s) x) ((F' s) y)= E s (helve Kₜ a x.val y.val).val := lawSeed ..
lemma normStore : ‖(F' s) x‖^2= (E s (helve Kₜ a x.val x.val).val).re:=by rw [← lawStore Y h s R L a A x x]; exact InnerProductSpace.norm_sq_eq_re_inner (𝕜:=ℂ) _ -- revisit
omit A in
lemma arriving (p:Arrive Y h w.val s)(v:s ≤ i):Arrive Y h w.val i:= fun t q=> ends_mono _ _ _ _ _ (p t q) v
lemma for_next : (F' (s+1)) (nectar Y h s R L a x) = (F' s) x:= by
 let y:= seedling Y h s a x; let t:Arrive Y h y.val s:= pulse_arr Y h s x.val; rw [clapper Y h s R L a A x]; change _= A.paid y; rw [← contains Y h (s+1) R L a A y (arriving Y h s _ a y t (by omega)), nectar_next Y h s R L a y t, show (days Y h s R L a) y=x from fullDay ..]
-- Operator tests on arbitrarily late inserts. No separability hypotheses.
lemma eventual_table : (fun s=> (store Y h s R L a A) ((days Y h s R L a) w)) =ᶠ[atTop] fun _=> A.paid w:= (arrived Y h w.val).mono fun _=> contains Y h _ R L a A w
lemma lens_ext {M: Type*}[NormedAddCommGroup M][NormedSpace ℂ M] {p q:A.space →L[ℂ] M} (v:∀ k, s≤k → ∀ x:Decko Y h a,p ((F' k) x)=q ((F' k) x)): p=q:=by
 apply DFunLike.coe_injective; apply A.issued.equalizer p.continuous q.continuous
 funext i; obtain ⟨k,V',c⟩:= ((eventual_table Y h R L a A i).and (eventually_ge_atTop s)).exists; change p (A.paid i) =q (A.paid i); simpa only [V'] using v k c (days Y h k R L a i)
#print axioms abode
end Chrono
end YM.CF.Buffered.Afterglow.Hierarchy
