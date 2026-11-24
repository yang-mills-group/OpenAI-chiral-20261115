import Bay.C.Woodbine
import Bay.D.Atlas
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

namespace C
open D hiding quiver
open Exterior Precision Nacre
open scoped ContDiff



open Planned.AtomRegular.Foliage Pressure Forge

variable {N:Side}{t L:ℝ}{k:ℕ}{o:Seat N}{v W:Pane N}{p:BudgetPoint}
lemma shifts (_hb:‖(0:tangD N)‖≤t -- nonnegative
 ) (mt:t≤ D.rule.c)
 (g:Site (More N)→SU.E)
 (z:Finset (Bond (More N))) (x:tangD N)(h:‖x‖≤t)
 (i:Bond (More N)):
 group.chord (Lattice.gauge g (gyrate z v x) i)
    ≤ 2*t + group.chord (Lattice.gauge g v i):=by
 change group.chord (g i.1 * (group.lieExp (wakeB z x i) * v i) * _) ≤ _
 rw[show ∀y, g i.1 * (group.lieExp (wakeB z x i)*v i) * y =
   (g i.1 * group.lieExp (wakeB z x i)*(g i.1)⁻¹)*(g i.1 * v i *y) from fun _=>by group]
 refine (group.chord_triangle _ _).trans (add_le_add ?_ le_rfl)
 rw [group.chord_conj]
 have g:‖wakeB z x i‖≤t:=(wakeLe ..).trans h
 exact (D.rule.light _ (g.trans mt)).trans (mul_le_mul_of_nonneg_left g (by norm_num))
abbrev buoyV(k:ℕ)(t:ℝ):ℝ:=12*(1+(k:ℝ))*t


lemma loft (j:Healthy t (roost (k+1) o) v)(ht:0≤t)
 (w:2*(k+1)< (More N).val)
 (hw:buoyV k t≤D.rule.c)(a:Agrees (roost k o) W v)
 (z:Finset (Bond (More N))) (x:tangD N) (h:‖x‖≤t):
 ∃ g,∃ y:Lag N, ‖y‖≤buoyV k t ∧ Agrees (roost k o) (Lattice.gauge g (gyrate z W x)) (represent y):=by
 obtain ⟨g,c⟩:=Cube.anchored o j ht le_rfl w
 let b:=6*(1+(k:ℝ))*t
 have f:t≤b:=by
   unfold b; rw[mul_comm _ t]; apply le_mul_of_one_le_right ht; linarith only [Nat.cast_nonneg (α:=ℝ) k]
 have h₁:2*b=buoyV k t:=by unfold b buoyV;ring
 have h₂:b≤D.rule.c:=le_trans (le_mul_of_one_le_left (ht.trans f) (by norm_num)) (h₁.symm ▸ hw)
 have j(i:Planned.AtomRegular.Link (More N))(q:i.1∈roost k o):
    group.chord (Lattice.gauge g (gyrate z v x) i)≤ b :=by
   obtain ⟨u,m,p⟩:=halo_spec.mp q; rw[mem_singleton.mp m] at p
   have a:separation o i.1 ≤ k:=p
   apply (shifts (norm_zero.trans_le ht) (f.trans h₂) g z x h i).trans
   apply (add_le_add le_rfl (c i a)).trans
   calc
     _ ≤ 2*t+4*t*(1+(k:ℝ)):=by
         rw[mul_assoc (4:ℝ) t]; gcongr
     _ ≤ b:=by unfold b; nlinarith only [mul_nonneg ht (Nat.cast_nonneg (α:=ℝ) k)]

 obtain ⟨y,e,T⟩:=log_extend j (ht.trans f) h₂
 refine ⟨g,y,h₁ ▸ e,fun i r l=>?_⟩
 rw[←T i r l]
 unfold Lattice.gauge gyrate
 simp only [Function.comp_apply,increment,a i r l]

variable {V:SOp N}{d D' r a b:ℝ}
lemma windshed (A:Trunk o V k a b d)(p:0≤a)
 (T:Twine 3 d D' r)
 {g:Site (More N)→SU.E}{y:Lag N}(h:‖y‖≤r) (W:Pane N)
 (q:profile W∈GateR N d)(u:Agrees (roost k o) (Lattice.gauge g W) (represent y)):
 ‖glazeH d V W-glaze V 1‖ ≤ (D'*b)*‖y‖^2:=by
 have v:profile (1:Pane N)∈GateR N d:= ⟨1,guard0 T.dr.le,by simpa using T.dr⟩
 obtain ⟨F,C,j,f,e,H⟩:=A.home
 rw [glazeH, Jet.equalizer, dif_pos q, glaze,glaze, H ⟨_,q⟩,←profile_trivial, H ⟨_,v⟩, Matrix.trace_sum, Matrix.trace_sum, ←sum_sub_distrib]
 refine (norm_sum_le ..).trans ((sum_le_sum ?_).trans (by
    rw [←sum_mul,←mul_sum]
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left e T.dp.le) (sq_nonneg _)))

 intro S _
 by_cases t:C S≠0
 · have h0:S⊆roost k o:=by
      obtain ⟨ho,hc⟩:=f S t
      exact fun i x => halo_spec.mpr ⟨o,mem_singleton_self _,((f_then (j S) t).lim o ho i x).le.trans hc.le⟩
   apply le_trans _ (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left 
      (le_mul_of_one_le_left (credit_pos (j S)) (rent_one p S)) T.dp.le) (sq_nonneg _))
   have vg:profile (Lattice.gauge g W)∈GateR N d:= by rw [profile_g];exact o_act g _ _ q
   have hp:= pic_eq (j S) vg ((T.pay _ (j S) _ h).2) (agrees_mono u (Finset.coe_subset.mpr h0))
   rw[pic_gauge (j S)] at hp
   have r0:represent (0:Lag N)= (1:Pane N):=by funext i;rw [Work.F03.represent_link];simp
   have h':=((touch T (j S)).step h).2
   unfold picL at h'
   simp only [Function.comp_apply,r0,←hp] at h'
   simp only [picP,equalizer,dif_pos v,dif_pos q] at h'
   exact h'
 have zero:ledgerV (C S)=0:=by rw[not_ne_iff.mp t]; simp [ledgerV]
 have l(i):pic (F S) i=0:=norm_le_zero_iff.mp (((essay_looks (j S)).2.2 i).trans_eq zero)
 change ‖D.pic (F S) _-D.pic (F S) _‖ ≤ _
 simp [l,zero]

variable {K:Scree.Loom N}{L1 r1:ℝ}
abbrev clipped (b D:ℝ)(k:ℕ):= D*b*(12*(1+(k:ℝ)))^2+b
abbrev tide (b D L:ℝ)(k:ℕ):=clipped b D k*2+L*b

open Planned.AtomRegular
-- UNMASKED at lit. update alias.
lemma wool (k:ℕ)(t D b:ℝ): D*b*(buoyV k t)^2 + b*t^2=clipped b D k*t^2:=by unfold clipped buoyV;ring

lemma buoyed (A:Trunk o V k a b d)(s:0≤a)
  (T:Twine 3 d D' r)(P:Luster d L1 r1)
  (h:buoyV k p.threshold ≤ iceR r)
  (c:‖glaze V 1‖≤ b*p.threshold^2)
  (ps:p.threshold ≤ r1)
  (w:2*(k+1)< (More N).val)
  (m:k+1≤p.B)(j:v∈setAwning p o)
  (e:Clearance p K k d)
  (t:Ids N)
  (z:Finset (Bond (More N)))(x:tangD N)(x0:‖x‖≤p.threshold):
 let f:= glazeH d V ∘ gyrate z (K (v,t))
 Allows 6 f x (L1*b) ∧ profile (gyrate z (K (v,t)) x) ∈ GateR N d ∧ ‖f x‖≤
   clipped b D' k*p.threshold^2 :=by
 intro f
 obtain ⟨p1,p2⟩:= P.pay A s _ (e.onD (v,t)) z _ (x0.trans ps)
 refine ⟨p1,p2,?_⟩

 have a:Healthy p.threshold (roost (k+1) o) v:=
   (show Healthy p.threshold (roost p.B o) v from ping_le j).mono_left (roost_expand m)
 obtain ⟨g,y,a,h₀⟩:=loft a p.threshold_pos.le w (h.trans (min_le_right ..))
    (e.light (x:=(v,t)) j) z x x0
 have d:=windshed (y:=y) (g:=g) A s T (a.trans (h.trans (min_le_left ..))) _ p2 h₀
 have vf:=mul_nonneg T.dp.le (soakCostNN A.pay)
 have f0:=d.trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) a 2) vf)
 change ‖glazeH _ V (gyrate z (K (v,t)) x)‖ ≤_
 refine ((norm_le_norm_sub_add _ (glaze V 1)).trans (add_le_add f0 c)).trans_eq ?_
 exact wool _ _ _ _

lemma shore (e:Clearance p K k d) (A:BoxPay V o k b d)
 (q:profile W∈GateR N d)(u:Agrees (roost k o) v W)
 (t:v∈setAwning p o):
   Matrix.trace (bayonet K p o V v)=glazeH d V W:=by
 let r:Orbit N:=(v,Classical.arbitrary _)
 have h:Agrees (roost k o) (K r) W:=fun i h k=>(e.light (x:=r) t i h k).trans (u i h k)
 unfold glazeH; rw [bayonet, Set.indicator_of_mem t, equalizer,dif_pos q]
 apply congrArg Matrix.trace (sub_eq_zero.mp ?_)
 exact popping ((A.sees (doPort e r) ⟨_,q⟩).trans_eq (by
    change b*(fare (roost k o) (profile (K r)) (profile W)/_)=_; rw[fareNil h];simp))

lemma helmPay (A:Trunk o V k a b d)(s:0≤a)
  (T:Twine 3 d D' r)(P:Luster d L1 r1)
  (h:buoyV k p.threshold ≤ iceR r)
  (c:‖glaze V 1‖≤ b*p.threshold^2)
  (ps:p.threshold ≤ r1)
  (w:2*(k+1)< (More N).val)
  (m:k+1≤p.B)(j:v∈setAwning p o)
  (e:Clearance p K k d)
  (t:Ids N)
  (z:Finset (Bond (More N)))(l:p.threshold≤1):
 let f:=fun x=>Matrix.trace (bayonet K p o V (gyrate z v (p.threshold • x)))
 Allows 6 f 0 (tide b D' L1 k *p.threshold^2):=by
 have b0:= soakCostNN A.pay
 have u:=mul_nonneg P.dp.le b0
 have q:0≤clipped b D' k:=add_nonneg (by have hd:=T.dp;positivity) b0
 let Y:=gyrate z (K (v,t))
 let H:=glazeH d V ∘ Y
 let B:=buoyed A s T P h c ps w m j e t z
 have i:Allows 6 (fun x=>H (p.threshold • x)) 0 (tide b D' L1 k *p.threshold^2):=
    candy p.threshold_pos.le l q (by norm_num) (fun _ y=>(B _ y).1) (fun _ y=> (B _ y).2.2) u
 intro f
 refine i.germ ?_
 let X (x:tangD N):=gyrate z v (p.threshold • x)
 have a:Continuous X := (stickU z v).comp (continuous_id.const_smul p.threshold)
 have w0: X 0=v:=by unfold X;rw [smul_zero];exact Forge.born ..

 have hh: IsOpen (setAwning p o):=ping_o

 have h0:X 0∈setAwning p o:=by rw [w0];exact j
 have h1:∀ᶠ x:tangD N in 𝓝 0, X x∈setAwning p o:=a.continuousAt.eventually (hh.mem_nhds h0)
 have hp: Continuous (fun x:tangD N=> ‖p.threshold • x‖):=(continuous_id.const_smul p.threshold).norm
 have h2:∀ᶠ x:tangD N in 𝓝 0, ‖p.threshold • x‖≤p.threshold:=
      hp.continuousAt.eventually (ge_mem_nhds (show ‖p.threshold • (0:tangD N)‖ < p.threshold from by rw[smul_zero,norm_zero];exact p.threshold_pos))
 refine (h1.and h2).mono ?_
 intro x t'
 have n:=t'.2
 have i0:Agrees (roost k o) (X x) (Y (p.threshold • x)):=by
    intro i a b
    have f:K (v,t) i=v i:=e.light (x:=(v,t)) j i a b
    unfold X Y Forge.gyrate; dsimp only [Function.comp_apply,increment];rw[f]
 exact (shore (v:=X x) (W:=Y (p.threshold • x)) e (boxSeal A s) (B _ n).2.1 i0 t'.1).symm
