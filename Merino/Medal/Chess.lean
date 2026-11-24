import YM.SU5.Thin.Woods.Fabric
import Merino.Medal.Limn
set_option maxHeartbeats 1200000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Merino.Medal
open Filter Topology Lattice Lat Tulip Branch Cube Tenant Vale RG
open scoped Matrix Matrix.Norms.L2Operator Classical InnerProductSpace
attribute [local instance] opCStarAlgebra
open Py.Rate Py.Rate.LocalLimit Preparation
open Skye Scree Buffered Afterglow MeasureTheory
open Yoke Papal Garter Gleam
variable {P:Preparation}{ℓ:ℕ}(Y:Course P (VolumeCape.Dream.Nimbus ℓ))


open Finset Cuff Hem Fock StepIn Lamour.Bridge.Celeste.Clock.Fabric Py.Rate.Pannier
open Lamour.Bridge.Celeste.Clock
open Journey
variable {n:Side}
open CF.Pannier.Chancel
open Reed

@[simp] lemma icon_one (n:Side): icon (1:Pane n→ℂ)=1:=by
  funext x; change (1:ℂ)•(1:FC (Single n))=1; rw [one_smul]
@[simp] lemma icon_mul (f g:Pane n→ℂ): icon (f*g)= icon f*icon g:= by
 funext U; unfold icon; rw [Pi.mul_apply,Pi.mul_apply,Matrix.smul_mul,one_mul,mul_smul]
/-- Complex scalar pure gauge. cf. Aisle/Bare.pure_job. -/
lemma icon_job (f:Pane n→ℂ){s:Support (More n)}(e:Envelope f)(h:LocalOn s f):
 AtSupport false s (icon f):=by
 refine AtSupport.fromEval (fun V=> f V • (1:FC (Single n))) ?_ ?_ (fun _=> Reed.Fine.one.scale _)
 · obtain ⟨C,hC⟩:=e.cost
   exact ⟨e.meas.smul measurable_const,C,fun x=> by rw [norm_smul,norm_one,mul_one]; exact hC x⟩
 exact fun U V T=> by dsimp only; rw [h U V T]


abbrev duet (m:ℕ)(a:Duo (More n)) :=
 baseball m a.1.there ∪ baseball m a.2.there

variable {f:Pane n→ℂ}{r c δ e:ℝ}{m p:ℕ}{T:Bundle SU.group (More n)}
variable (w:Scar m r δ c e f T) (β z:ℝ)(a:Duo (More n))(b:Tint)
lemma polka_bill (u:ℝ)(D:ℝ)(h:‖β‖≤u)(v:∀x,‖f x‖ ≤ D)(x:Pane n):
 ‖polka β a b f x‖≤ (u*D)^2:=by
 have hu:0≤u:=(norm_nonneg β).trans h
 simp only [polka,norm_mul,dart_n,Complex.norm_real,sq]
 exact mul_le_mul (mul_le_mul h (v _) (norm_nonneg _) hu) (mul_le_mul h (v _) (norm_nonneg _) hu)
   (by positivity) (mul_nonneg hu ((norm_nonneg _).trans (v x)))



include w
lemma polka_job :AtSupport false (duet m a) (icon (polka β a b f)):=by
 refine icon_job _ ?_ ?_
 · have h(u:StepIn (More n))(b:Bool): Measurable (fun x:Pane n=>dart b ((β:ℂ)*f (u.cabin x))) :=
    (dartₘ _).measurable.comp <|
        measurable_const.mul <| w.readable.comp (Wilson.continuous_pull ..).measurable
   exact ⟨(h _ _).mul (h _ _),_,polka_bill β a b ‖β‖ c le_rfl w.bound⟩
 intro U V h
 have d(u:StepIn (More n))(H:Agrees (baseball m u.there) U V):
   f (u.cabin U)= f (u.cabin V) :=
      w.region _ _ (u.agrees (u.apply_zero.symm ▸ H))
 unfold polka; rw [d a.1 (agrees_mono h subset_union_left),d a.2 (agrees_mono h subset_union_right)]
omit w
lemma icon_flipper (f:Pane n→ℂ):
 icon (flipper β z a b f)=1+(z:ℂ) • icon (polka β a b f):=by
 funext x; unfold icon flipper; rw [add_smul,one_smul,mul_smul]; rfl
include w in
lemma flipper_job : AtSupport false (duet m a) (icon (flipper β z a b f)):=by
 rw [icon_flipper]; exact (AtSupport.oneM _).addM ((polka_job w β a b).smulM _)


def Patchwork (m:ℕ)(f:Pane n→ℂ)(Y:Fabric n):Prop:=
 ∃ r:StepIn (More n), duet m (r.rotate a)⊆Y.S∧
   ∃ b, Y.x= icon (flipper β z (r.rotate a) b f)
include w in
lemma Patchwork.job (x:Fabric n)(u:Patchwork β z a m f x):AtSupport false x.S x.x:=by
 obtain ⟨r,h,b,u⟩:=u; rw [u]; exact (flipper_job w β z _ _).mono h
lemma deter (d:Bool)(x:ℂ):dart (!d) x= star (dart d x):=by cases d <;> simp [dart]

variable {x:Fabric n}
lemma Patchwork.shift (u:Patchwork β z a m f x)(i:Axis)(s:ℤ):Patchwork β z a m f (x.twistL i s):=by
 obtain ⟨r,h,⟨b,c⟩,u⟩:=u
 let j : StepIn (More n):=⟨Signed.mirror i,wrap (More n) (2 • (s • step i))⟩
 refine ⟨j*r,?_,(!b,!c),?_⟩
 · change _ ⊆ x.S.image j.siteB
   rw [mul_rotate, duet]; simp only [ mul_there]
   rw [j.apply_ball,j.apply_ball,← image_union]
   exact image_subset_image h


 change reflMark i s x.x=_
 rw [mul_rotate,u]
 funext y
 unfold reflMark icon
 rw [theta_smul,theta_one]
 suffices star (flipper β z (r.rotate a) (b,c) f (j.cabin y.1))=flipper β z _ _ f y.1 by
     exact congrArg (· • 1) this
 unfold flipper
 rw [polka_turn]; simp [polka,deter]


lemma list_icon (L:List (Pane n→ℂ)):(L.map icon).prod=icon L.prod :=by induction L with| nil=> simp|cons i L ih=> simp [ih]

lemma layout {L:List (Fabric n)}(h:Sylvan (Patchwork β z a m f) p L){d:ℕ}(e : d ≤ m):
 ∃ j:Fin L.length→StepIn (More n),Pavilion d a j ∧ ∃ c:Fin L.length→Tint,
   buffet L=icon (fun V=>∏ i, flipper β z ((j i).rotate a) (c i) f V):=by
 let F:=Fin L.length
 choose j h₁ h₂ using (fun i:F => (h.core _ (List.get_mem L i)))
 choose c hx using h₂
 have hw :(L.map Fabric.x)=(List.ofFn (fun i:F => flipper β z ((j i).rotate a) (c i) f)).map icon:=by
    conv=> lhs; rw [← List.ofFn_get L,List.map_ofFn]
    rw [List.map_ofFn]
    exact congrArg List.ofFn (funext hx)
 have du : Pairwise (fun i k:F => Disjoint (duet m ((j i).rotate a)) (duet m ((j k).rotate a))):=by
    have u(i k:F)(hi:i<k):Disjoint (duet m ((j i).rotate a)) (duet m ((j k).rotate a)):=by
       apply disjoint_left.mpr; intro x v b
       have e:=List.pairwise_iff_get.mp h.annex i k hi x (h₁ i v) x (h₁ k b)
       rw [separation_self] at e; omega
    intro i k v; exact (lt_or_gt_of_ne v).elim (u i k) (fun t=>(u k i t).symm)


 have sub (y:Seat n):baseball d y⊆baseball m y:=by
   intro x v; obtain ⟨w,u,g⟩:=halo_spec.mp v; exact halo_spec.mpr ⟨w,u,g.trans e⟩
 refine ⟨j,⟨fun i k u => (du u).mono ((sub _).trans subset_union_left) ((sub _).trans subset_union_left),
              fun i k u => (du u).mono ((sub _).trans subset_union_right) ((sub _).trans subset_union_right)⟩,c,?_⟩
 rw [buffet,hw,list_icon,List.prod_ofFn]
 congr
 funext V; rw [prod_apply]


def clasp (u d p:ℝ) := 1+p*(u*d)^2
lemma clasp₀ {p:ℝ}(h:0≤p)(u d:ℝ):1≤clasp u d p:=le_add_of_nonneg_right (mul_nonneg h (sq_nonneg _))

lemma claspPay (V)(u d p:ℝ)(h:‖β‖≤u)(v:∀x,‖f x‖≤d)(q:|z|≤p) :
  ‖flipper β z a b f V‖ ≤ clasp u d p:=by
 unfold flipper; apply le_trans (norm_add_le ..)
 rw [norm_one,norm_mul,Complex.norm_real,Real.norm_eq_abs]
 exact add_le_add le_rfl <|mul_le_mul q (polka_bill β a b u d h v V) (norm_nonneg _) ((abs_nonneg _).trans q)
abbrev flare (m:ℕ)(f:Pane n→ℂ):Fabric n :=
 ⟨icon (flipper β z a b f),duet m a,a.1.there,a.2.there⟩
lemma flare_pay (m)(f:Pane n→ℂ) :
   Patchwork β z a m f (flare β z a b m f):=by
 have h(i:StepIn (More n)):(1:StepIn (More n))*i=i:=by
   change StepIn.mk ((1:Signed)*i.face) (affine 1 0 i.there)=_
   simp [affine]

 have e:(1:StepIn (More n)).rotate a=a:=by simp [rotate,h]
 exact ⟨1,e.symm ▸ (Subset.refl _ : duet m a ⊆ _),b, congrArg (fun t=>icon (flipper β z t b f)) e.symm⟩


/-- Cover metering applies to both readings. -/
lemma iconPay (f:Pane n→ℂ)(D:ℝ)(h:∀x,‖f x‖≤D)(x):
      ‖icon f x‖≤D:=by unfold icon; rw [norm_smul,norm_one,mul_one];exact h _

end YM.CF.Merino.Medal

