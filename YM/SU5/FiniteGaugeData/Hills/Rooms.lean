import YM.SU5.FiniteGaugeData.SalonG.Knitting
import YM.SU5.FiniteGaugeData.Hills.Terrace
set_option autoImplicit false
set_option maxHeartbeats 390000
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
namespace Hills
open Nacre Heat Charm Chrono Journey SalonG
variable (a i₀:Axis)(d n:ℕ)(f:W (tent Y h))
-- ability to rent any mark into a Slab by one-time origin shift.
-- units clockW: tic. permit Level unaffected. 
lemma plan_larger (e:d ≤ n)(p:Plan Y h a d f): Plan Y h a n f:= ⟨p.choose,p.choose_spec.1.ante le_rfl (Nat.cast_le.mpr (Nat.mul_le_mul_left (tic Kₜ) e)),p.choose_spec.2⟩
lemma plan_stepper {x:ℕ}(z:ℤ)(p:Studio a 0 (yard Kₜ d) (reserve Λ l) S) (t:0≤z)(v: (d:ℤ)+z ≤ x):
 Studio a 0 (yard Kₜ x) (reserve Λ l) (hour Kₜ S a z):=by
 apply (p.hour Kₜ z).ante
 · unfold gaugeW; positivity
 unfold gaugeW; rw [← yard_le,← yard_le,← mul_add]; apply mul_le_mul_of_nonneg_left v (Nat.cast_nonneg' _)
lemma plan_steps {n:ℕ}(p:Plan Y h a d f)(z:ℤ)(u:0≤ z)(e:(d:ℤ)+z≤ n): Plan Y h a n (clockW Kₜ a z f):=⟨_,plan_stepper _ _ _ a d z p.choose_spec.1 u e, loc_tic Kₜ _ _ _ p.choose_spec.2⟩
lemma rent_uniform : ∃ d:ℕ, ∃ z:ℕ,0<d ∧ (Studio a 0 (yard Kₜ d) (reserve Λ l) (hour Kₜ S a z)):=by
 let r:=wall S+reserve Λ l+1; let k:=tic Kₜ; have he:0<k:= tic_pos _
 have hv:0 < r:=by unfold r; positivity
 have hp:r≤ k*r:=Nat.le_mul_of_pos_left r he
 refine ⟨2*r,r,Nat.mul_pos two_pos hv,?_⟩; constructor<;> intro i h'<;> obtain ⟨b,t,rfl⟩:= mem_image.mp h'<;> have hx:= wall_p S a t
 · change beat Kₜ a r b a+_≤ _; rw [beat_same,yard_mul,← Nat.cast_mul]; change _ ≤ (↑(2*(tic Kₜ*r)):ℤ)
   unfold r k at *; omega
 change _ ≤ beat Kₜ a r b a; rw [beat_same,← Nat.cast_mul]; unfold k r at *; omega
lemma rent (v:Locator (tent Y h) f S): ∃ d:ℕ,0<d ∧ ∃ z:ℤ,Plan Y h a d (clockW Kₜ a z f):= by obtain ⟨d,z,p,t⟩:=rent_uniform Y h S a; exact ⟨d,p,z,_, t, loc_tic Kₜ _ _ _ v⟩
lemma resident (p:Ahead a 0 (reserve Λ l) S)(e: Locator (tent Y h) f S):∃ d:ℕ,0<d∧ Plan Y h a d f:=by
 let r:=wall S+reserve Λ l+1; let k:=tic Kₜ; have he:0<k:= tic_pos _; have ht:r≤ k*r:=Nat.le_mul_of_pos_left r he; exact ⟨r, by unfold r; positivity,S,⟨fun i h' => (by have hv:=wall_p S a h'; change _≤(↑(k*r):ℤ); unfold r at *; omega),p⟩, e⟩
lemma plan_un : Plan Y h a d 1:= ⟨∅,Studio.empty,locate_one ..⟩
section tangent
variable (z:ℤ)(p:i₀≠a)
include p
lemma plan_walk (v:Plan Y h a d f): Plan Y h a d (clockW Kₜ i₀ z f):= by
 obtain ⟨S,e,g⟩:=v; refine ⟨_,?_ , loc_tic Kₜ S i₀ z g⟩; constructor; swap; · exact platformL Kₜ S a i₀ 0 z p e.ahead
 intro b t; obtain ⟨x,t',rfl⟩:=mem_image.mp t; change beat Kₜ i₀ z x a+_≤ _; rw [beat_slant Kₜ a i₀ z x p]; exact e.behind x t'
end tangent
variable {u v:ℕ→ℕ}{I:ℕ→Family (tent Y h)→ℕ→ℂ}{E:ℕ→ Family (tent Y h)→ℂ}{P:Call Λ l}{J:Wicket Λ l}
variable (W':Universal Y h u v I E)(R:Rolled Y h u v J P)
variable (A:Repertory Y h W' R a)(F:Plan Y h a d f)(q:0<d)
local notation "T" z:max=> tock Y h s W' R a a A z
local notation "Mₜ" t:max=> store Y h t W' R a A
local notation "S'" s:max a:max k:max P:max p:max => Wedge Y h s a k W' R A P p
local notation "U" => Wedge Y h s a d W' R A F q
include A F q
lemma wicket_pad {m:ℕ}(hL:d+m=n)(p:0<n)(p_:Plan Y h a n f):
    Wedge Y h s a n W' R A p_ p = Wedge Y h s a d W' R A F q * tock Y h s W' R a a A m (fun _=>Nat.cast_nonneg' _):= by
 rcases Nat.eq_zero_or_pos m with rfl|v
 · rw [show (T (↑(0:ℕ):ℤ)) _= _ from tock_zero Y h s W' R a a A, mul_one] -- NatCast zero
   subst n; rfl
 let P':= plan_un Y h a m; let w:=couplePlan Y h a d m F P'
 have he:=wedge_glues Y h s a d m W' R A F q P' w v; rw [wedge_identity Y h s a m W' R A v P'] at he; refine Eq.trans ?_ he.symm
 subst n; exact pc_eq (show f=Swing Kₜ a d f 1 from by unfold Swing; rw [clock_one, mul_one]) (by omega : 0 < d+m)
where pc_eq {d:ℕ}{x y:W (tent Y h)}{v w}(p:x=y)(h_:0<d): Wedge Y h s a d W' R A (f:=x) v h_=Wedge Y h s a d W' R A (f:=y) w h_:= by subst y; rfl
lemma equalWick {y:W (tent Y h)} (p_:Plan Y h a n y) (t:0<n) (e:d=n) (f':f=y): Wedge Y h s a d W' R A F q=Wedge Y h s a n W' R A p_ t:=by subst n y; rfl
lemma wicket_adv (j:ℕ)(v:j+d=n)(t:Plan Y h a n (clockW Kₜ a j f)) : Wedge Y h s a n W' R A t (by omega) = tock Y h s W' R a a A j (fun _=>Nat.cast_nonneg' _) * Wedge Y h s a d W' R A F q := by
 rcases Nat.eq_zero_or_pos j with rfl|p
 · rw [show (T (↑(0:ℕ):ℤ)) _ = _ from tock_zero Y h s W' R a a A]; rw [one_mul]; apply equalWick Y h s a n d (clockW Kₜ a (0:ℕ) f) W' R A t _ F q (by omega); exact tic_zero .. -- args?
 let w:=plan_un Y h a j; let z:=couplePlan Y h a j d w F
 have he:=wedge_glues Y h s a j d W' R A w p F z q; rw [wedge_identity Y h s a j W' R A p w] at he; rw [he]; exact equalWick Y h s a n _ _ W' R A t _ z _ v.symm (by unfold Swing; rw [one_mul])
-- shift y tangent commutes later
variable (z:ℤ)
local notation "Ω"=>tock Y h s W' R a i₀ A
omit A F q in
lemma grow_clock : ascended Y h s W' R n (clockW Kₜ a z f)= clockW Kₜ a ((Λ.R.L.val:ℤ)^n*z) (ascended Y h s W' R n f):=by
 induction n with
 | zero=> rw [pow_zero,one_mul]; rfl
 | succ n ih=> change Charm.next Y h (s+n) W' R _=_; rw [ih,promote_clock,pow_succ',mul_assoc]; rfl
include z
lemma wicket_tangent (α:i₀≠a)(u:Plan Y h a d (clockW Kₜ i₀ z f))(p:Allows a i₀ z): Wedge Y h s a d W' R A u q * tock Y h s W' R a i₀ A z p=tock Y h s W' R a i₀ A z p * Wedge Y h s a d W' R A F q:= by
 apply lens_ext Y h s W' R a A; intro i p' v; obtain ⟨i,rfl⟩:=Nat.exists_eq_add_of_le p'; simp_rw [mul_apply_eq_comp]; rw [earn_seed Y h s _ W' R a i₀ A _ z p (by omega), wedge_plus,wedge_plus,earn_seed Y h s _ W' R a i₀ A _ z p (by omega)]; apply congrArg; apply Subtype.ext; rw [appointed_val,hoist_val,hoist_val,appointed_val,grow_clock, Swing, Swing, clock_mul, clock_cross]; unfold Chrono.scaleR; rw [Nat.add_sub_cancel_left] -- α unused (clock_cross ALL; but need Plan translation.L.disp condition? if i0=a, right formula STILL TRUE both qualify. mention)
#print axioms rent_uniform
#print axioms wicket_pad
#print axioms wicket_adv
#print axioms wicket_tangent
end Hills
end YM.CF.Buffered.Afterglow.Hierarchy
