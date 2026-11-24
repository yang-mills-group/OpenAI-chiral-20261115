import Merino.Hem.Weft
import Merino.Hem.Slip
import Merino.Cuff.Tartan
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 600000
set_option synthInstance.maxSize 24000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Merino.Hem
open Function Filter Topology NormedSpace Lattice Wilson Fock Pastry Scree Sault Sour Stax Skye Jet NormedSpace Scroll Finset Palot Cadre Vow
open RG Mew Rive Nor Hake MeasureTheory Bake Rue Salt
open Metric Drapes Tulip Lat Branch Cube Tenant
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Topology Classical
attribute [local instance] opCStarAlgebra
open Rush SU Prism Nacre Laic Tap Levier Thera Moto Oath Font Haro Spire Swell

variable {n:Side}
local notation "I"=> Single n

open Window Buffered StressExchange Dial

open Cuff _root_.Zephyr.Chern


lemma rim_zero (n:Side)(σ:Signed): boxA (rim n σ) 0=0:=by
 rw [sitA]
 change affine σ ((assembly n).root 0) 0=0
 rw [map_zero]; simp [affine]

lemma vblank (s:Sweep n): flashA s 1=1:=by
 funext i; rw [Skye.flash]; simp only [Pi.one_apply, inv_one,ite_self]
 exact map_one (polarT _) -- check

variable {b k:ℕ}{o:Seat n}
lemma space_at (h:separation 0 o≤4)(l:k≤b+12):purse k o⊆Yardlet (More n) (b+16):=by
 intro i r
 obtain ⟨t,w,f⟩:=halo_spec.mp r
 rw [mem_singleton] at w
 exact halo_spec.mpr ⟨0,mem_singleton_self _, (separation_triangle _ t _).trans (w▸by
   subst t; omega)⟩ -- tune

variable {p:BudgetPoint}{d r C a B E L δ:ℝ}{K:Scree.Loom n}{X:SOp n}
/-- Memberwise signed test. The echos can conjugate the trace,
but don't disturb its real part. -/
lemma plumed (σ:Signed) (s:Room d r C)
   (g:Skylit p d K)(h:Trunk o X (p.B/10) a B d)(ha:0<a)
   (u:separation 0 o≤4)(v:4*(lead (p.B/10)+8)+1<n.val)
   (mCost: C*(quota^2*B)*(tow a)^2≤L)(cCost:C*(quota^2*B)≤L)(bCost:B≤L)
   (imag:∀ V, |(traceCost K p o X V).im|≤E)
   (fee:
    let y:=glaze (stream n) (julStep (rim n σ) X)
    Bud y ∧ δ<slash σ * (bud y 2).re):
   ∃ T:InkFace n, δ < slash σ * dripQ T (needle n) (needle n)
    ∧ Flap (p.B+16) p.threshold r L E ((traceCost K p o X) ∘ flashA (rim n σ)) T
         (traceCost K p o X 1).re:=by
 let z:=rim n σ
 let t:=boxA z o
 have a₁:separation 0 t≤4:=by
   have w:=sitT z 0 o; rw [rim_zero] at w; rwa [w]
 obtain ⟨T,D,F,V⟩:= tartan s K g (trunk_move h z) ha a₁ v fee.1
 refine ⟨T,F ▸ fee.2,⟨D.flip,D.rent.trans mCost,fun i j e=>?_⟩,?_,?_,?_,?_,?_⟩
 · have ht:4+lead (p.B/10) ≤ slim (p.B+16):=by unfold lead slim; omega
   exact (D.abode i j e).trans ht
 · intro U; exact (mask_trace g ha.le h _).trans bCost
 · have hm:= mask_meas g h.pay
   have ht: Continuous (Matrix.trace: Op I→ℂ):=by fun_prop
   exact ht.measurable.comp (hm.comp (revM z).measurable)
 · intro U W hy
   unfold Function.comp traceCost
   rw [←mask_move z g ha.le h,←mask_move z g ha.le h]
   rw [mask_local g ha.le (trunk_move h z) _ _ (agrees_mono hy (space_at a₁ le_rfl))]
 · intro x U
   unfold Function.comp traceCost
   rw [revG,mask_gauge g ha.le h, trace_twist]
 intro W Y y w f
 have v₁:W ∈ pass p t:=fun i e=> w i (mt (Disjoint.mono_left (space_at a₁ (by omega:p.B≤p.B+12))) e)
 have f₁:=agrees_mono f (space_at a₁ (by omega:p.B/10≤p.B+12))
 let J:=julStep z X
 have vt:=V W Y y v₁ f₁
 let Q:=dripQ T (cseed Y) (cseed Y)
 have e₁(U:Pane n): (masked K p t J U).trace.re=(traceCost K p o X (flashA z U)).re:=by
    unfold traceCost
    rw [← mask_move z g ha.le h]
    exact (ech_real z _).symm
 have y0:(profile (1:Pane n)) ∈ Openc (More n) d:=
    ⟨1,guard0 g.pos.le,by simpa using g.pos⟩
 have e₀:traceX J 1=(traceCost K p o X 1).re:=by
   have k₀:(1:Pane n) ∈ pass p t:=ping_f p (purse p.B t)
   have h₀:=e₁ 1
   rw [mask_extension g ha.le (trunk_move h z) k₀ y0 (fun _ _ _=>rfl),vblank] at h₀
   exact h₀
 refine (Complex.norm_le_abs_re_add_abs_im _).trans (add_le_add ?_ ?_)
 · rw [e₁,e₀] at vt
   simp only [Function.comp_apply, Complex.sub_re, Complex.add_re,Complex.ofReal_re]
   exact vt.trans (mul_le_mul_of_nonneg_right cCost (by positivity))
 simpa using imag (flashA z W)

def mica:ℝ:=(Fintype.card Signed:ℝ)⁻¹
def ramp (σ:Signed):ℝ:= mica * slash σ

/-- Flavor weight trivial on the pure scalar. This is the *linear*
determinant-type projection, not the RP mirror. -/
def pstar (f:Pane n→ℂ) := purl ramp (fun σ=>f∘flashA (rim n σ))

lemma mica_pos:0 < mica:= by unfold mica; positivity
lemma mica_sum:∑ _:Signed,mica=1:=by
 have h:(Fintype.card Signed:ℝ) ≠0:=by positivity
 simp [mica,h]
lemma ramp_abs:∑ σ,|ramp σ|=1:=by
 simp only [ramp,abs_mul,slash_abs,abs_of_pos mica_pos,mul_one]
 exact mica_sum

lemma ramp_empty : ∑ σ,ramp σ=0:=by
 let t:=Signed.mirror 0
 have h:(∑ σ,ramp σ)= -(∑ σ,ramp σ):=by
   nth_rw 1 [←Equiv.sum_comp (Equiv.mulLeft t)]
   rw [←sum_neg_distrib]
   refine sum_congr rfl fun s _=>?_
   have e:slash t= -1:=by unfold slash t;rw [det_t]; rfl
   simp [ramp,slash_mul,e]
 linarith
lemma rim_mul (n:Side)(σ w: Signed):rim n (σ*w)=rim n σ*rim n w:=by
  unfold rim; rw [det_p]
  change Sweep.mk ..= Sweep.mk (σ*w) (0+σ.act 0) _
  simp

lemma pstar_rule (σ:Signed)(f:Pane n→ℂ)(V:Pane n):
    pstar f (flashA (rim n σ) V)=(slash σ:ℂ)*pstar f V:=by
 let e:=Equiv.mulLeft σ
 unfold pstar purl
 simp_rw [Function.comp_apply,lights,←rim_mul]
 conv_rhs =>
   rw [← Equiv.sum_comp e]
 rw [Finset.mul_sum]
 refine sum_congr rfl fun w _=>?_
 change _=_*((ramp (σ*w):ℂ)*_)
 rw [←mul_assoc,←Complex.ofReal_mul,show e w=σ*w from rfl]
 congr 2
 have h:slash σ * slash σ=1:=by rw [←pow_two,←sq_abs,slash_abs,one_pow]
 unfold ramp; rw [slash_mul]; linear_combination -mica*slash w*h


lemma flocked (s:Room d r C)
   (g:Skylit p d K)(h:Trunk o X (p.B/10) a B d)(ha:0<a)
   (u:separation 0 o≤4)(v:4*(lead (p.B/10)+8)+1<n.val)
   (mCost: C*(quota^2*B)*(tow a)^2≤L)(cCost:C*(quota^2*B)≤L)(bCost:B≤L)
   (imag:∀ V, |(traceCost K p o X V).im|≤E)
   (fee:∀ σ:Signed, 
    let y:=glaze (stream n) (julStep (rim n σ) X)
    Bud y ∧ δ<slash σ * (bud y 2).re):
   ∃ T:InkFace n, δ < dripQ T (needle n) (needle n) ∧ 
     Scar (p.B+16) p.threshold r L E (pstar (traceCost K p o X)) T:=by
 choose T e j using fun σ=>plumed σ s g h ha u v mCost cCost bCost imag (fee σ)
 refine ⟨dart ramp T,?_,pleated ramp ramp_abs j ?_⟩
 · rw [dart_reads]
   calc
     δ = ∑ _:Signed,mica*δ:=by rw [←sum_mul,mica_sum,one_mul]
     _ < _ := sum_lt_sum_of_nonempty univ_nonempty fun i _=>by rw [ramp,mul_assoc]; exact mul_lt_mul_of_pos_left (e i) mica_pos
 rw [←sum_mul,←Complex.ofReal_sum,ramp_empty,Complex.ofReal_zero,zero_mul]
