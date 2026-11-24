import Bay.D.Stalk
import Bay.D.Carol
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 3000
set_option synthInstance.maxSize 24000
set_option quotPrecheck false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Bay
open Function Filter Topology NormedSpace Lattice Wilson Fock Pastry Scree Sault Sour Stax Skye Jet Scroll Finset Palot Cadre Vow
open RG MeasureTheory Rue
open Metric Drapes Tulip Lat Branch Cube Tenant
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Topology Classical
attribute [local instance] opCStarAlgebra
open Rush SU Tap Levier Thera Oath Font Spire Dial Rill
open Kennel Swell

namespace D
open Exterior Precision Nacre
open scoped ContDiff

open Carol Zephyr.Chern
variable {N:Side}{x:Site N}{p:BudgetPoint}{k:ℕ}{d a V r D b:ℝ}{K:Scree.Loom N}{X:SOp N}
abbrev rayX(p:BudgetPoint)(K:Scree.Loom N)(x:Site N)(X:SOp N):Pane N→ℂ:=
   litP K p (node x) X
abbrev gapX(p:BudgetPoint)(K:Scree.Loom N)(x:Site N)(X:SOp N):Pane N→ℂ:=
   hema x (rayX p K x X)
def skies(x:Site N)(X:SOp N)(s:Signed):SOp N:= julStep (room x s) X
lemma highX (s:Signed)(t:Trunk (node x) X k a b d):
    Trunk (node x) (skies x X s) k a (Tenant.quota^2*b) d:=by
 have h:=boxCargo (room x s) t; rw [pole] at h; exact h
lemma tideX (s:Signed)(q:Clearance p K k d)(h:BoxPay X (node x) k b d):
   step x s (rayX p K x X)=cSignX (detX s) ∘ rayX p K x (skies x X s):=by
 funext v; have hg:= trueJul (room x s) v q h
 rw[pole] at hg
 rw[Carol.step,rayX,litP,Function.comp_apply, Function.comp_apply,←hg,ech,singT,trace_twist,win_trace,p_c];rfl

lemma stepV (s:Signed)(q:Clearance p K k d)(t:Trunk (node x) X k a b d)
    (h:Calcite a d D r V)(l:Shallow p k N r):
   let f:=step x s (rayX p K x X)
   let z:=Tenant.quota^2*b
   Vinyl p (node x) k d z f ∧ ∃c A,Skin p (node x) k r (V*z) f c A:=by
 dsimp only;rw[tideX s q (boxSeal t h.age.le)]
 obtain ⟨hv,c,A,H⟩:=dawn h l (highX s t) q
 cases detX s
 · exact ⟨hv,c,A,H⟩
 exact ⟨hv.spin,_,_,H.spin⟩

lemma sonata (q:Clearance p K k d)(t:Trunk (node x) X k a b d)
   (h:Calcite a d D r V)(l:Shallow p k N r):
   Vinyl p (node x) k d (Tenant.quota^2*b) (gapX p K x X) ∧
   ∃A,Skin p (node x) k r (V*(Tenant.quota^2*b)) (gapX p K x X) 0 A:=by
 choose c B g using fun s:Signed=>(stepV s q t h l).2
 have hh:=Skin.fin _ _ _ _ univ fun s _=>(g s).scale (tune s)
 have uu:=Vinyl.fin _ _ univ fun s _=> (stepV s q t h l).1.scale (tune s)
 rw [←sum_mul,tuned_fee,one_mul] at hh uu
 refine ⟨uu,∑s,tune s • B s,?_⟩ -- _ choose A

 have hd:=hh.wakes h.rp
 have he:(gapX p K x X) 1=0:=dead ..
 have ha: (0:ℂ)=∑s,tune s*c s := he.symm.trans hd
 rw [ha]
 exact hh

variable {δ:ℝ}{f:ℝ→ℂ}
lemma gem_star(p:gem f δ):gem (fun t=>star (f t)) δ:=by
 have he:= Bloom.of_der (c:=fun i=>star (bud f i)) (f:=fun t=>star (f t))
    (a:=fun t=>star (deriv f t))
    (p.1.1.mono fun t g=>g.hasDerivAt.star)
    (p.1.2.hasDerivAt.star) rfl rfl (by simp[bud])
 refine ⟨he.1,?_⟩
 rw [he.bud_eq]
 exact p.2

lemma duo (s:Signed) (q:Clearance p K k d)(h:BoxPay X (node x) k b d)
   (y:ℝ→Pane N) -- pull actual σ
   (u:gem (fun t=>σ s * rayX p K x (skies x X s) (y t)) δ):
   gem (fun t=>σ s * step x s (rayX p K x X) (y t)) δ:=by
 rw [tideX s q h]
 cases detX s
 · exact u
 rw [show (fun t=>_) = fun t=>star (σ s*rayX p K x (skies x X s) (y t)) from funext fun t=>by rw[star_mul',sig_re];rfl]
 exact gem_star u

lemma sonataGem(q:Clearance p K k d)(h:BoxPay X (node x) k b d)
    (y:ℝ→Pane N)
    (g:∀s,gem (fun t=>σ s * rayX p K x (skies x X s) (y t)) δ):
    gem (gapX p K x X ∘ y) δ:=by
 let W s t:=σ s * step x s (rayX p K x X) (y t)
 have hp(s):gem (W s) δ:=duo s q h y (g s)
 have hb:=Bloom.sum univ fun s _=> (hp s).1.bloom.scale ((count⁻¹:ℝ):ℂ)
 have he: gapX p K x X ∘ y=fun z=>∑s,((count⁻¹:ℝ):ℂ)* W s z:= by
    funext z
    rw [gapX, Function.comp_apply, hema,Finset.sum_apply]
    simp only [Pi.smul_apply,smul_eq_mul,tune,mul_assoc,W]
 rw[he]
 refine ⟨hb.1,?_⟩
 rw[hb.bud_eq, Finset.sum_apply,Complex.re_sum]
 have t := inv_pos.mpr count_pos
 letI : Nonempty Signed:=⟨1⟩
 calc
   _ = ∑ _:Signed,count⁻¹*δ:=by rw[sum_const,nsmul_eq_mul,card_univ,
         ←mul_assoc, show (Fintype.card Signed:ℝ)*count⁻¹=1 from mul_inv_cancel₀ count_pos.ne',one_mul]
   _ < _:=sum_lt_sum_of_nonempty univ_nonempty (fun i _=>by
      rw [Pi.smul_apply,smul_eq_mul,Complex.mul_re,Complex.ofReal_re,
         Complex.ofReal_im,zero_mul,sub_zero]
      exact mul_lt_mul_of_pos_left (hp i).2 t)
end YM.CF.Bay.D
