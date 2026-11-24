import YM.SU5.FiniteGaugeData.SalonG.Expansion
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
local notation "V" z:max=> Wedge Y h s a d W' R A z q
local notation "δ"=> (energyS Λ d n)
include A
lemma innerLens {x y:A.space}(p:∀ n:ℕ, s ≤ n→∀ x': Decko Y h a, inner ℂ ((M n) x') x=inner ℂ ((M n) x') y): x=y:=by
 apply ext_inner_left ℂ; intro z; refine A.issued.induction (P:=fun t=>inner ℂ t x=inner ℂ t y) ?_ (isClosed_eq (by fun_prop) (by fun_prop)) z; rintro _ ⟨v,rfl⟩; obtain ⟨n,e,t⟩:= ((eventual_table Y h W' R a A v).and (eventually_ge_atTop s)).exists; dsimp only at e; rw [←e]; exact p n t _ -- left means inner t or x?
lemma orth_lens {T' U':A.space.Op}(p:∀ n:ℕ, ∀ x y:Decko Y h a, inner ℂ (store Y h (s+n) W' R a A x) (T' (store Y h (s+n) W' R a A y))= inner ℂ (store Y h (s+n) W' R a A x) (U' (store Y h (s+n) W' R a A y))): T'=U':=by
 apply lens_ext Y h s W' R a A; intro i v x; apply innerLens Y h i a W' R A; intro n v' y; have he : ∃ u:D, store Y h n W' R a A u= (M i) x :=by
    induction n,v' using Nat.le_induction with
    | base=> exact ⟨_,rfl⟩
    | succ n _ ih=> obtain ⟨w,g⟩:=ih; exact ⟨nectar Y h n W' R a w,(for_next Y h n W' R a A w).trans g⟩
 obtain ⟨w,U⟩:=he; rw [← U]; obtain ⟨n,rfl⟩:= Nat.exists_eq_add_of_le (v.trans v'); exact p n y w
local notation "Ω"=> goldStar Y h W' R a A
include q z in
lemma wedge_star : star (Wedge Y h s a d W' R A z q)= Wedge Y h s a d W' R A (Plan.other Y h z) q :=by
 apply orth_lens Y h s a W' R A; intro n x y; rw [ContinuousLinearMap.star_eq_adjoint,ContinuousLinearMap.adjoint_inner_right,wedge_plus,wedge_plus]; have hz:= ice_bend Y h s a d n W' R A y x z; nth_rw 1 [← inner_conj_symm]; nth_rw 2 [← inner_conj_symm]; rw [hz] -- tuning
omit A in
lemma appoint_sum (v':Plan Y h a d x)(p:Plan Y h a d (f+x)):
   appointed Y h s a d n W' R p y=appointed Y h s a d n W' R z y + appointed Y h s a d n W' R v' y:=by
 apply Subtype.ext; rw [Subalgebra.coe_add]; simp only [appointed_val,map_add,Swing,add_mul]
lemma wedge_sum (v':Plan Y h a d x)(p: Plan Y h a d (f+x)) : Wedge Y h s a d W' R A p q = Wedge Y h s a d W' R A z q + Wedge Y h s a d W' R A v' q:=by
 apply lens_ext Y h s W' R a A; intro i h' v; simp_rw [_root_.add_apply]; rw [wedge_at ..,wedge_at ..,wedge_at ..,appoint_sum Y h s a d (i-s) W' R z v v' p,map_add]; all_goals exact h'
lemma wedge_scale (c:ℂ)(p:Plan Y h a d (c•f)): V p=c • V z:=by
 apply lens_ext Y h s W' R a A; intro i v x; rw [_root_.smul_apply,wedge_at ..,wedge_at ..,appoint_scale Y h s a d (i-s) W' R x z p,map_smul]; all_goals exact v
omit A in
lemma ascend_together : ascended Y h s W' R (n+1) f=ascended Y h (s+1) W' R n (Charm.next Y h s W' R f):=by induction n with
 | zero=> rfl
 | succ n ih=> let i:= s+(n+1); rw [ascended,LinearMap.comp_apply, ih]; change _=companion Y h (s+1+n) W' R _; rw [show s+1+n=s+(n+1) from by omega]
lemma wedge_step (p:Plan Y h a (Λ.R.L.val*d) (Charm.next Y h s W' R f))(w:0 < Λ.R.L.val*d):
    V z=Wedge Y h (s+1) a (Λ.R.L.val*d) W' R A p w:=by
 apply lens_ext Y h (s+1) W' R a A; intro i v t; rw [wedge_at Y h s i a d W' R A z t q (by omega), wedge_at Y h (s+1) i a (Λ.R.L.val*d) W' R A p t w v]; apply congrArg; apply Subtype.ext; rw [appointed_val,appointed_val,show i-s=i-(s+1)+1 from by omega, ascend_together,energy_step]; unfold energyS Swing; ring_nf
-- unit / vacuum, tick-price
omit A in
lemma ascend_one : ascended Y h s W' R n 1=1:=by induction n with
 | zero=> rfl
 | succ n ih=> rw [ascended,LinearMap.comp_apply,ih]; exact next_unit Y h (s+n) W' R
lemma wedge_identity (p:Plan Y h a d 1) : V p=tock Y h s W' R a a A d (fun _=>Nat.cast_nonneg' _):=by
 apply lens_ext Y h s W' R a A; intro i v t; rw [wedge_at Y h s i a d W' R A p t q v, earn_seed Y h s i W' R a a A t d _ v]; apply congrArg; apply Subtype.ext; rw [appointed_val,hoist_val,ascend_one,Swing,one_mul]; unfold energyS Chrono.scaleR; push_cast; rfl -- push_cast closes?
-- action on Ω EXACT F vector no matter future
abbrev pocket : Decko Y h a:= ⟨f, scoreP Y h a d z⟩
lemma wink : Wedge Y h s a d W' R A z q (goldStar Y h W' R a A)= store Y h s W' R a A (pocket Y h a d z):=by
 rw [← seed_gold Y h s W' R a A,wedge_here]; apply congrArg; apply Subtype.ext; rw [embarks]; unfold Swing; rw [show (1:D).val=1 from rfl, clock_one, mul_one]
lemma pocketT : inner ℂ (goldStar Y h W' R a A) (Wedge Y h s a d W' R A z q (goldStar Y h W' R a A))= E s f.val:=by rw [wink, ← seed_gold Y h s W' R a A,lawStore]; unfold helve; rw [show (1:D).val=(1:W Kₜ) from rfl, ice_central,one_mul]
-- Compose slab within ONE level using time-shift embedding thence across P. Use separated even-level-only. No contact optimization
local notation "U" p:max n:max => Wedge Y h s a n W' R A p
omit A
include z
variable (v':Plan Y h a n x)
include v' in
lemma couplePlan : Plan Y h a (d+n) (Swing Kₜ a d f x):=by
 have he:=(v'.choose_spec.1.hour Kₜ (d:ℤ)); rw [gauge_cast,zero_add] at he;
 exact ⟨_, (z.choose_spec.1.ante le_rfl (by rw [yard_sum]; omega)).union (he.ante (by omega) (by rw [yard_sum]; omega)), locate_join _ _ (locate_sub _ z.choose_spec.2 subset_union_left) (locate_sub _ (loc_tic _ _ _ _ v'.choose_spec.2) subset_union_right)⟩
include v' W' R
lemma ascend_swing (i':ℕ) : ascended Y h s W' R i' (Swing Kₜ a d f x)= Swing Kₜ a (energyS Λ d i') (ascended Y h s W' R i' f) (ascended Y h s W' R i' x):=by
 induction i' with
 | zero=> rw [energy_zero]; rfl
 | succ i ih=>
    rw [energy_step]; let U0:= energyS Λ d i
    let v₀:= ascended Y h s W' R i f; let x₀:=ascended Y h s W' R i x; have ht:= (Plan.rides Y h s i W' R z); have hp:= (Plan.rides Y h s i W' R v');
    change Charm.next Y h (s+i) W' R (ascended Y h s W' R i _)= Swing Kₜ a (Λ.R.L.val*U0) (Charm.next Y h (s+i) W' R v₀) (Charm.next Y h (s+i) W' R x₀); rw [ih]; unfold Swing; let T:= hour Kₜ hp.choose a U0
    have hv:=flightW Kₜ hp.choose a 0 (U0:ℤ) hp.choose_spec.1.ahead; rw [yard_le, zero_add] at hv
    rw [Charm.separate Y h ht.choose T (s+i) W' R ht.choose_spec.2 (loc_tic _ _ _ _ hp.choose_spec.2) (cover_separate a ht.choose_spec.1.behind hv), promote_clock,Nat.cast_mul (Λ.R.L.val) U0]
include A q
lemma wedge_glues (w: Plan Y h a (d+n) (Swing Kₜ a d f x))(t:0<n) : Wedge Y h s a d W' R A z q * Wedge Y h s a n W' R A v' t = Wedge Y h s a (d+n) W' R A w (by omega):=by
 apply lens_ext Y h s W' R a A; intro i₁ q u; obtain ⟨i,rfl⟩:= Nat.exists_eq_add_of_le q; rw [ContinuousLinearMap.mul_apply,wedge_plus,wedge_plus,wedge_plus]; apply congrArg; apply Subtype.ext; rw [appointed_val,appointed_val,appointed_val,ascend_swing Y h s a d n W' R z v' _]; unfold Swing; rw [clock_mul,clock_add,← mul_assoc, show energyS Λ (d+n) i= energyS Λ d i + energyS Λ n i from mul_add .., Nat.cast_add]
#print axioms wedge_glues
#print axioms wink
end SalonG
end YM.CF.Buffered.Afterglow.Hierarchy
