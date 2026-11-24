import YM.SU5.FiniteGaugeData.Jadot.Apron
import YM.SU5.FiniteGaugeData.CodaT.Niagara
/-! # Auth. closure and content. -/
set_option autoImplicit false
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option maxHeartbeats 410000
set_option linter.unusedVariables false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Hierarchy.LyraBill
open Function Filter NormedSpace SU Lat Lattice Cube Finset MeasureTheory RG Wilson Metric
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Kronecker Topology ComplexOrder
open Rush Scroll Peaks Stencil Tenant Tap Tulip Branch Fir Scree Advance Reflect Window Laurent Next.Free Bloch Drapes Spire Lifted Skye Sound Precision Tree Push.SectorMeasure Next.SectorChange Common Fock Pastry Satin
open Window.Brique
open Reed (Fine)
attribute [local instance] opCStarAlgebra
set_option quotPrecheck false
open Heat Quest Fock.Brique
open Nacre Heat Charm Chrono Journey
open Py Py.Rate LocalLimit Preparation Journey Fiber Vale VolumeCape FullBill
open SalonG
open Quest.Chaperone
open Steam
variable {Λ:Preparation}{l:ℕ}(Y:Course Λ (VolumeCape.Dream.Nimbus l)) {g:ℝ}{u v:ℕ→ℕ}
open Eight YM.SU5.FiniteGaugeData.CodaT YM.SU5.FiniteGaugeData.Cuprite.Spirit YM.SU5.FiniteGaugeData.Cuprite.Spirit.Vapors Fock.Relief Rhythm.Hush Rhythm.CodaT Dial Aria Reduction.Drama.Pack
open Rhythm.Dolores Rhythm.Ergo Hills Gamer Fock.Reduction Turnist Alts Alts.Emblem Window.Presidio.Nigra
namespace Chiffon
open Moorend Rhythm.CodaT
open Reduction.Loyd Reduction.Dijon Reduction.Loyd.Art Reduction.Celeste
variable {N M:Side}{K': Calibration}{n m k w:ℕ}{p h C x y r θ ξ v' u' H μ ε δ e ρ:ℝ}{S T:Finset Cover}{ζ:ℂ}{f f':W K'}{F G:Paint}
namespace Auth
variable (xAuth:Auth K' S f F)
local notation "cre" h:max S:max U:max W:max s:max=> Art h (tickA N) (modesIn N (region S N)) false (U N W) s
lemma unitP(K:Calibration)(p:S.Nonempty): Auth K S 1 1:= ⟨locate_one ..,fun i=>rfl,p,fun n u V=> (map_one (twist (quantU (tradew n u)))).symm,fun H h=> ⟨1,zero_lt_one,fun N _=> Art.lone⟩,fun H h ε v=> ⟨1,zero_lt_one,fun N U t=>by change Art _ _ _ _ ((1:FC (Single N))-1) _; rw [sub_self]; exact (Art.hid _).pump v.le⟩⟩
lemma zeroP(K:Calibration)(p:S.Nonempty): Auth K S 0 0:= ⟨locate_zero ..,fun i=>rfl,p,fun n u V=> (map_zero (twist (quantU (tradew n u)))).symm,fun H h=>⟨1,zero_lt_one,fun N _=> (Art.hid _).pump zero_le_one⟩,fun H h ε v=>⟨1,zero_lt_one,fun N U t=>by change Art _ _ _ _ ((0:FC (Single N))-0) _; rw [sub_self]; exact (Art.hid _).pump v.le⟩⟩
include xAuth
lemma stock_P (p:S⊆T):Auth K' T f F:=by
 have hh(N:Side): region S N⊆ region T N:= image_subset_image p
 refine ⟨locate_sub K' xAuth.place p,xAuth.nameR,xAuth.cell.mono p,xAuth.story,fun H v=>?_,fun H v ε τ=>?_⟩
 · obtain ⟨c,t,p⟩:= xAuth.arts H v; exact ⟨c,t,fun N u=> (p N u).bless (modes_monotone (hh N))⟩
 obtain ⟨t,p,e⟩:= xAuth.warm H v ε τ; exact ⟨t,p,fun N u f=> (e N u (fun i p q=>f i (hh N p) (hh N q))).bless (modes_monotone (hh N))⟩
lemma plusP(h:Auth K' S f' G):Auth K' S (f+f') (F+G):=by
 refine ⟨locate_sum _ _ xAuth.place h.place,fun T=>by rw [Subalgebra.coe_add,Pi.add_apply,xAuth.nameR,h.nameR]; rfl,xAuth.cell,fun N U x=>?_,fun H v=>?_,fun H v ε e=>?_⟩
 · simp only [Pi.add_apply,map_add,xAuth.story,h.story]
 · obtain ⟨a,u,p⟩:=xAuth.arts H v; obtain ⟨b,y,k⟩:=h.arts H v; exact ⟨a+b,add_pos u y,fun N U=> (p N U).sum (k N U)⟩ -- dot notation sum maybe sum of finset ambiguity
 obtain ⟨a,u,p⟩:=xAuth.warm H v (ε/2) (by positivity); obtain ⟨b,g,h⟩:= h.warm H v (ε/2) (by positivity); refine ⟨min a b,lt_min u g,fun N U t=> ?_⟩; let W:=region S N; let A:=p N U fun i x y=>(t i x y).trans (min_le_left ..); let B:=h N U fun i x y=>(t i x y).trans (min_le_right ..); simp only [Pi.add_apply,show ∀ x y z p:FC (Single N),x+y-(z+p)=x-z+(y-p) from (fun _ _ _ _=>by abel)]; exact (A.sum B).pump (add_halves ε).le -- orientation tune
lemma scaleP (v:ℂ): Auth K' S (v • f) (v • F):=by
 refine ⟨locate_scale _ _ _ xAuth.place, fun T=>by rw [Subalgebra.coe_smul,Pi.smul_apply,xAuth.nameR]; rfl,xAuth.cell,fun N U x=>?_,fun H e=>?_,fun H t ε e=>?_⟩
 · simp only [Pi.smul_apply,twist_scalar,xAuth.story]
 · obtain ⟨a,l,p⟩:=xAuth.arts H e; exact ⟨‖v‖*a+1,by positivity,fun N U=> (Art.scale v (p N U)).pump (le_add_of_nonneg_right zero_le_one)⟩
 let p:=‖v‖+1; have hp:0<p:=by unfold p; positivity
 obtain ⟨y,t,p_⟩:=xAuth.warm H t (ε/p) (by positivity); refine ⟨y,t,fun N U h=>?_⟩; simp only [Pi.smul_apply,← smul_sub]; exact (Art.scale v (p_ N U h)).pump ((mul_le_mul_of_nonneg_right (le_add_of_nonneg_right zero_le_one) (by positivity : (0:ℝ) ≤ ε/p)).trans_eq (by change p*_=_; field_simp)) -- binder.K ctx
lemma negP : Auth K' S (-f) (-F):= by simpa using xAuth.scaleP (-1)
lemma subP (q:Auth K' S f' G): Auth K' S (f-f') (F-G):= by rw [_root_.sub_eq_add_neg,_root_.sub_eq_add_neg]; exact xAuth.plusP q.negP
lemma prodP (q:Auth K' S f' G): Auth K' S (f*f') (F*G):=by
 refine ⟨locate_join _ _ xAuth.place q.place,fun T=>by rw [Subalgebra.coe_mul,Pi.mul_apply,xAuth.nameR,q.nameR]; rfl,xAuth.cell,fun N u x=>by simp only [Pi.mul_apply,map_mul,xAuth.story,q.story],fun H t=>?_,fun H t ε v=>?_⟩
 · obtain ⟨v,p,o⟩:=xAuth.arts H t; obtain ⟨u,q,g⟩:= q.arts H t; exact ⟨2*v*u,by positivity,fun N U=> (o N U).work (g N U)⟩ -- book
 obtain ⟨b,p,X⟩:=xAuth.arts H t; obtain ⟨w,l,Y⟩:= q.arts H t; let a:=2*(b+w); let r:= ε/a; have h:0<a:=by unfold a; positivity
 have hx:0<r:= div_pos v h; obtain ⟨u,k,x⟩:=xAuth.warm H t r hx; obtain ⟨g,v,y⟩:=q.warm H t r hx; refine ⟨min u g,lt_min k v,fun N U Hx=>?_⟩
 simp only [Pi.mul_apply]; rw [show F N U*G N U - F N 1*G N 1=(F N U-F N 1)*G N U+ F N 1*(G N U-G N 1) by noncomm_ring]
 let Z := x N U fun i x y=> (Hx i x y).trans (min_le_left ..); let W := y N U fun i x y=> (Hx i x y).trans (min_le_right ..); refine ((Z.work (Y N U)).sum ((X N 1).work W)).pump ?_; exact le_of_eq (by rw [show 2*r*w+2*b*r=r*a by unfold a; ring]; exact div_mul_cancel₀ _ h.ne')
-- mirror & translations; halo user.S. For sign all N. copy.
variable (a:Axis)(z:ℤ)
abbrev turn(X:Paint)(a:Axis)(z:ℤ):Paint:=fun N U=> theta (carR a z N) (X N (fling a z N U))
omit xAuth in
private lemma oneF(N:Side): fling a z N (1:Pane N)=1:=by
 funext i; unfold fling; change Step.read _ _ _= (1:SU.E); simp [Lattice.Step.read] -- tune namespace
local notation "Z"=> refF N a z
local notation "p₀"=> Buffered.plane a z
local notation "Fφ"=> fling a z N
omit xAuth
variable {T₀:Support (More N)}{t:ℝ}
private lemma dryduck {X:Pane N}(h:fieldR (Z T₀) t X): fieldR T₀ t (Fφ X):=by
 let W:=(p₀).anon N
 rintro ⟨x,i⟩ hx hy
 let v:= (Signed.mirror a); let b:Site (More N):=wrap _ (2 • (z • step a))
 let T:=(posDir i).rotate v
 have hb : W x∈ Z T₀ := Finset.mem_image_of_mem W hx
 have he : W (x+step i) ∈ Z T₀ := Finset.mem_image_of_mem W (a:=x+step i) hy
 have hw : W (x+step i)=W x+T.vec := by
    change affine v b (x+step i)=affine v b x+ ((posDir i).rotate v).vec; rw [Lattice.Step.vec_rotate, Lattice.Step.vec_pos, affine,affine,v.act_add, add_right_comm]
 rw [hw] at he
 change SU.group.chord (T.read X (W x))≤t
 cases hq:T with| mk i0 u=>
 rw [hq] at he; cases u
 · exact h (W x,i0) hb he
 change SU.group.chord (X (W x-step i0,i0))⁻¹ ≤ t
 have hx : W x-step i0 ∈ Z T₀ := by simpa only [show (⟨i0,true⟩ : Lattice.Step)=negDir i0 from rfl, Lattice.Step.vec_neg, sub_eq_add_neg] using he
 rw [SU.group.chord_inv]; exact h (W x-step i0,i0) hx (by change W x-step i0+step i0 ∈ _; rw [sub_add_cancel]; exact hb)
private lemma signCode(v:Pane N)(g:Mosquito N): Fφ (Lattice.gauge g v)=Lattice.gauge (g ∘ (p₀).anon N) (Fφ v):= Push.Local.pull_gauge (Signed.mirror a) (wrap _ (2 • (z • step a))) v g
private lemma reflection_t{p h:ℝ}{X:FC (Single N)}(v:Art h (tickA N) (modesIn N (region S N)) false X p) :Art h (tickA N) (modesIn N (region (refract a z S) N)) false (theta (carR a z N) X) p:=by
 rw [refl_region]; refine v.reflectX _ ?_ (refl_modes ..); have h: twist (carR a z N) (1-tickA N)=tickA N:=by rw [touchP,←dim_cut,exchanges_halves]
 rw [map_sub,map_one] at h; nth_rw 2 [←h]; abel
include xAuth
lemma polar : Auth K' (refract a z S) (fire K' a z f) (Auth.turn F a z):=by
 refine ⟨locate_cold _ _ _ _ xAuth.place,fun T=>by rw [ice_print,reflector,xAuth.nameR]; rfl, xAuth.cell.image _,fun T g U=> ?_,fun H t=>?_,fun H t ε h=>?_⟩
 · unfold Auth.turn; rw [signCode,xAuth.story]; obtain ⟨c,-,Y⟩:=xAuth.arts 1 le_rfl; exact theta_twist_right _ _ _ (congrArg Subtype.val (Lifted.gaugeSquare a z T g)) (Art.sameRoom (Y T _))
 · obtain ⟨c,t,o⟩:=xAuth.arts H t; exact ⟨c,t,fun N U=> reflection_t a z (o N _)⟩
 obtain ⟨c,b,v⟩:=xAuth.warm H t ε h; refine ⟨c,b,fun N U k=>?_⟩; unfold Auth.turn; rw [oneF,←theta_sub]; rw [refl_region] at k; exact reflection_t a z (v N _ (dryduck a z k))
-- finite sums
omit xAuth in
lemma sumX (V:Calibration) {ι:Type*}(s:Finset ι)(f:ι→ W V)(F:ι→Paint)(l:S.Nonempty)(p:∀ i∈s,Auth V S (f i) (F i)):Auth V S (∑ i∈s,f i) (∑ i∈s,F i):=by
 classical
 induction s using Finset.induction_on with
 | empty=>rw [sum_empty,sum_empty]; exact zeroP V l
 | @insert a s p' ih=> rw [sum_insert p',sum_insert p']; exact (p a (mem_insert_self ..)).plusP (ih fun i t=> p i (mem_insert_of_mem t))
end Auth
end Chiffon
end YM.CF.Buffered.Afterglow.Hierarchy.LyraBill
