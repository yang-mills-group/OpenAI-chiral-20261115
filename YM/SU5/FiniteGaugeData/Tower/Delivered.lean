import YM.SU5.FiniteGaugeData.Tower.Central
import YM.SU5.FiniteGaugeData.Tower.Pass
/-!
# Collapse of the central reading between *literal sharp* finite levels

In particular no rotation of error estimates through particle number. The
shape F_s is lifted per-period exactly, complement fields move along with it.
Here multiplicative resolution of the finite reads extends to any
number of repetitions through one pipeline, no thinning estimates used. Uses
the opportunity that all subproducts lifted separately have a common cover
cut for exclusivity in the lower torus band (either the width split at one
face, midplane, or end seam). No density approximation assumes independences.
Only true on the common regulator (center transport). Plane align not required
for crossing condition alone (only if using RP in Consumer). -/
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 5900
set_option maxHeartbeats 360000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.SlabMark
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Heat Fock
variable {Λ:Preparation}{l:ℕ}(Y:Course Λ (VolumeCape.Dream.Nimbus l))(H:Real.exp 1≤Λ.x)
local notation "K" => tent Y H
variable (s n k:ℕ)(j:Axis)
local notation "L₀"=>Λ.R.L.val
local notation "T₀" v:max=> Journey.side Y n v
structure Delivered (S V:Family (tent Y H)): Prop where
 invoiced: TestFamily (tent Y H) true S
 fresh:TestFamily (tent Y H) true V
 handover: distribute Y H (s+1) n V=aboveD Y H s n k S
local notation "aDv"=>Delivered Y H s n k
variable {x y x' y':Family (tent Y H)}{S V:Finset Cover}(p: legalAt Y s n k)
local notation "U" i:max=> relocate K j i
local notation "R" i:max=> mirror K j i
local notation "γ" i:max=>gaugeT K i
local notation "b₀"=>ruler (K).B
local notation "ℓ"=> (K).ℓ
include p
lemma delivering(d:aDv x y):sharp Y H (s+1) n k y=sharp Y H s n k x:=by
 change Journey.compass Y n k (s+1) (distribute Y H (s+1) n y)=_
 rw [d.handover]; obtain ⟨s',w⟩:=d.invoiced.paid; exact promise Y H s s' n k p w
lemma mail_one :aDv 1 1:=by
 let i:=(Y.voyage n); let v:=i.X (Y.uv k); let g:=(fullness Y n k p.1).cap_grant
 constructor
 · exact aux_test (S:=∅) InTest.one
 · exact aux_test (S:=∅) InTest.one
 rw [(show distribute Y H (s+1) n 1=1 from (distribute_arith Y H _ _ (1:Family K) 1 0).2.2.2.1)]; symm; exact above_unit Y H s n k p
lemma mail_turn (d:aDv x y)(i:ℤ): aDv (mirror K j i x) (mirror K j (L₀*i) y):=by
 let g:=(fullness Y n k p.1).cap_grant
 constructor
 · exact reflect_ok _ _ _ d.invoiced
 · exact reflect_ok _ _ _ d.fresh
 rw [(distribute_arith Y H _ _ y y 0).2.2.2.2,d.handover]
 unfold aboveD
 rw [(distribute_arith Y H _ _ x x 0).2.2.2.2]
 let Z:=((Y.voyage n).X (Y.uv k)).gram; let A:= ((Y.voyage n).X (Y.uv k)).wave
 let M:= steps Λ.V (Y.ir n) Λ.block (Y.uv k); let V:=(Y.voyage n).CapeT; let G:= apt (Y.ir n) Λ.block Λ.R.L s
 obtain ⟨m⟩:=g.grant s p.2; obtain ⟨o,v,f,E,iW⟩:=m.cap
 obtain ⟨u,F⟩:=d.invoiced.paid
 exact (rising G (M s) Λ.K.j ((A s).val) (Z (s+1)).J.M Λ.R.odd_side Chi.canonical Λ.J.d (Z (s+1)).beta (V s) j i (g.aligned s p.2) (stationed Y H s u n F) (g.branch s p.2) E (show Stencil.LaurentRadius _ Λ.R.L (aliasLaw Λ) from Journey.legal Λ) m.legal.1 m.legal.2).symm
lemma mail_move (d:aDv x y)(i:ℤ):aDv ((U i) x) ((U (L₀*i)) y):=by
 unfold relocate chime
 have ht:=mail_turn Y H s n k j p (mail_turn Y H s n k j p d 0) (gaugeT (tent Y H) i)
 rw [mul_zero,show (Λ.R.L.val:ℤ)* gaugeT (tent Y H) i=gaugeT (tent Y H) ((L₀:ℤ)*i) by unfold gaugeT gaugeShift; ring] at ht
 exact ht
-- no pinning restrictions beyond legal and disjoint-at-radius native `side Y n s`. 
lemma mail_mask (dx:aDv x x')(dy:aDv y y')(hx:InTest (tent Y H) true S false x)(hy:InTest (tent Y H) true V false y)
 (w:∀ g∈Satin.region S (T₀ s),∀ v∈Satin.region V (T₀ s), 2*((K).ℓ)≤ separation g v): aDv (x*y) (x'*y'):=by
 let gr:=(fullness Y n k p.1).cap_grant
 constructor
 · exact dx.invoiced.mul dy.invoiced
 · exact dx.fresh.mul dy.fresh
 rw [(distribute_arith Y H _ _ x' y' 0).2.1,dx.handover,dy.handover]; unfold aboveD; rw [(distribute_arith Y H _ _ x y 0).2.1]
 let Z:=((Y.voyage n).X (Y.uv k)).gram; let A:= ((Y.voyage n).X (Y.uv k)).wave
 let M:= steps Λ.V (Y.ir n) Λ.block (Y.uv k); let V0:=(Y.voyage n).CapeT; let G:= apt (Y.ir n) Λ.block Λ.R.L s
 obtain ⟨m⟩:=gr.grant s p.2; obtain ⟨o,v,f,E,iW⟩:=m.cap
 apply (separated_mult G (M s) Λ.K.j ((A s).val) (Z (s+1)).J.M Λ.R.odd_side Chi.canonical Λ.J.d (Z (s+1)).beta (V0 s) (show Stencil.LaurentRadius _ Λ.R.L (aliasLaw Λ) from Journey.legal Λ) E.bill (gr.branch s p.2) m.legal.1 m.legal.2 _ _ (stationed Y H s S n hx) (stationed Y H s _ n hy) (tissue ..) ?_).symm
 intro g v i a
 refine lt_of_lt_of_le ?_ (w g v i a); change 2*(Advance.nearZero (aliasLaw Λ)+distanceLaw l) <2*Journey.reserve Λ l
 unfold Advance.nearZero Journey.reserve r₃ r₁; have h:100*(Λ.R.L.val)*(1+aliasLaw Λ) ≥ 1+aliasLaw Λ:= by have h:0< Λ.R.L.val:= Λ.R.L.property; nlinarith
 omega
omit p
lemma across_seam {a t u:ℤ}
 (α:Between (tent Y H) j t a S)(b:Between (tent Y H) j a u V)(e:a-t≤(T₀ s).val)(d:u-a≤ (T₀ s).val):∀ g∈Satin.region S (T₀ s),∀ v∈Satin.region V (T₀ s),2*((K).ℓ) ≤ separation g v:=by
 let N:=T₀ s
 change _≤ ((N).val:ℤ) at d e
 have he: Satin.region V N⊆ band N j a (K).ℓ:= enters_arc (tent Y H) j (fun i h=>by obtain ⟨h,k⟩:=b i h; constructor <;> omega) rfl
 have hr: Satin.region (reflectedBox j a S) N⊆band N j a (K).ℓ:=by
    apply enters_arc (tent Y H) j (x:=a) _ rfl
    intro x p; obtain ⟨x,m,f⟩:=reflect_stays j a S p; obtain ⟨h,tS⟩:=α x m; rw [f,if_pos rfl]; constructor <;> omega
 have hp:Satin.region S N ⊆ (band N j a (K).ℓ).image ((plane j a).anon N):=by
    rintro x b; obtain ⟨i,t,rfl⟩:=mem_image.mp b
    let v:=plane j a
    refine mem_image.mpr ⟨wrap _ (v.motion i),hr (mem_image.mpr ⟨_,mem_image.mpr ⟨i,t,rfl⟩,rfl⟩),?_⟩
    rw [← Shape.anno, fling_there] -- signature
 intro x m y r; rw [separation_comm]; exact opposite_gap j a (margin_good Λ l) y x (he r) (hp m)
include p
lemma seam_dispatch {b x0 z:ℤ}(u:Between (tent Y H) j b x0 S)(v:Between (tent Y H) j x0 z V)
 (g:x0-b≤(T₀ s).val)(q:z-x0≤(T₀ s).val)(hx:InTest (tent Y H) true S false x)(hy:InTest (tent Y H) true V false y)
 (Dx:aDv x x')(Dy:aDv y y'):aDv (x*y) (x'*y'):=mail_mask Y H s n k p Dx Dy hx hy (across_seam Y H s n j u v g q)

lemma toward_lift {w:ℤ}(Dx:aDv x x')(j':ℕ):aDv (toward (tent Y H) j w x j') (toward (tent Y H) j (L₀*w) x' j'):=by
 induction j' with
 | zero=>exact Dx
 | succ i ih=>rw [toward_step,toward_step,show gaugeT (tent Y H) (L₀*w)=L₀*gaugeT (tent Y H) w by unfold gaugeT gaugeShift; ring]; exact mail_turn Y H s n k j p ih _
lemma lace_lift {w:ℤ}(Dx:aDv x x')(t:ℕ)(hx:InTest (tent Y H) true S false x)(e:Between (tent Y H) j 0 (b₀*w) S)(hv:0≤ w)(he:b₀*w*t≤ (T₀ s).val):
 aDv (lace K j w x 1 t) (lace K j (L₀*w) x' 1 t):=by
 induction t with
 | zero=> exact mail_one Y H s n k p
 | succ t ih=>
    obtain ⟨G,v,u,d⟩:=trans_exists j S
    obtain ⟨F,r,r',_⟩:=orient_room K j hx e d t
    obtain ⟨B,hC,h',_⟩:=mainshape K j hv hx e d t
    rw [lacing,lacing]
    let B':= plow K j w B; let L:=L₀
    have he':Between K j (b₀*w) (b₀*w*(t+1:ℕ)) B':=by
       have g:=h'.relocate K j w; rw [add_zero, ←mul_assoc] at g
       convert g using 1; push_cast; ring
    have hu:b₀*w*t≤ (T₀ s).val:=by
       rw [Nat.cast_add_one] at he; have ht:=ruler_gene (K).B; nlinarith
    apply seam_dispatch Y H s n k j p r' he' (by rw [Nat.cast_add_one] at he; rw [sub_zero]; have he1:=ruler_gene (K).B; nlinarith [mul_nonneg (show 0≤b₀*w from by positivity) (show 0≤(t:ℤ) by positivity)]) (by
       rw [sub_le_iff_le_add]; exact he.trans (by have he':=ruler_gene (K).B; nlinarith)) r (show InTest K true B' false _ from flow_port K j _ hC)
    · exact toward_lift Y H _ _ _ j p Dx _
    exact mail_move Y H s n k j p (ih hu) w

lemma bulk_lift {w:ℤ}(Dx:aDv x x')(t:ℕ)(i:ℤ)(hx:InTest (tent Y H) true S false x)(e:Between (tent Y H) j 0 (b₀*w) S)(hv:0≤ w)(he:2*(b₀*w*t)≤ (T₀ s).val):
 aDv (banner j w i t x) (banner j (L₀*w) (L₀*i) t x'):=by
 obtain ⟨g,A,b,pb⟩:=trans_exists j S
 obtain ⟨T,d,q,q'⟩:=mainshape K j hv hx e pb t
 let F0:=lace K j w x 1 t
 let F1:=lace K j ((L₀:ℤ)*w) x' 1 t
 have hr:0<b₀:=ruler_gene (K).B
 have ht:(0:ℤ)≤t:=by positivity
 have hg:b₀*w*t ≤(T₀ s).val:=by linarith [mul_nonneg (mul_nonneg hr.le hv) ht]
 let u:=lace_lift Y H s n k j p Dx t hx e hv hg
 have v:aDv (chambers j w i x 1 t) (chambers j ((L₀:ℤ)*w) ((L₀:ℤ)*i) x' 1 t):=by
    apply mail_move _ _ s n k j p
    let T':=reflectedBox j 0 T
    rw [←mul_assoc] at q
    have hh:= q.mirror K j 0; simp only [mul_zero,zero_sub,neg_zero] at hh
    exact seam_dispatch Y H s n k j p hh q (by linarith) (by linarith) (axial K j 0 d) d (by have hz:=mail_turn Y H s n k j p u 0; rw [mul_zero] at hz; exact hz) u
 obtain ⟨F,z,a,c⟩:=centerpiece j w i t g A hv hx e pb
 let a0:=gaugeT K (cliff w i t)
 have ho:=a.mirror K j a0
 have h:Between K j (a0-2*(b₀*w*t)) a0 (reflectedBox j a0 F):= by convert ho using 1 <;> ring
 have hp: (L₀:ℤ)*a0=gaugeT K (cliff ((L₀:ℤ)*w) ((L₀:ℤ)*i) t):=by unfold gaugeT Heat.gaugeShift cliff a0; unfold gaugeT Heat.gaugeShift cliff; ring
 exact seam_dispatch Y H s n k j p h a (by linarith) (by change a0+_-a0≤_; linarith) (axial K j a0 z) z (by have hi:=mail_turn Y H s n k j p v a0; rwa [hp] at hi) v -- should be mail_turn v and hp
end YM.CF.Buffered.Afterglow.Tower.SlabMark
#print axioms YM.CF.Buffered.Afterglow.Tower.SlabMark.bulk_lift
