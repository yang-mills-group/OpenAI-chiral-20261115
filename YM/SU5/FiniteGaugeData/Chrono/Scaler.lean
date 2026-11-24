import YM.SU5.FiniteGaugeData.Chrono.Haven
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
variable (A:Repertory Y h R L a) (x:Decko Y h a)(w: Vect Y h a 0)
local notation "G" s:max => store Y h s R L a A
local notation "D"=> Decko Y h a
local notation "H"=> A.space
local notation "N" s:max=> nectar Y h s R L a
local notation "V"=> Vect Y h a 0
variable (F:ℕ→ Decko Y h a →ₗ[ℂ] Decko Y h a)(B:ℝ)
structure Robing : Prop where
  tall(n:ℕ)(t:s ≤ n)(x:Decko Y h a) : F (n+1) (nectar Y h n R L a x) = nectar Y h n R L a (F n x)
  fit(n:ℕ)(t:s ≤ n)(x:Decko Y h a): ‖(store Y h n R L a A) (F n x)‖ ≤ B*‖store Y h n R L a A x‖
local notation "Λ0"=> Robing Y h s R L a A F B
private abbrev dressing (n:ℕ) := (store Y h n R L a A).comp ((F n).comp (days Y h n R L a))
local notation "δ" n:max => dressing Y h R L a A F n
variable (P':Robing Y h s R L a A F B)
include P'
lemma looking (p:s ≤ i)(t:i ≤ k)(c:Arrive Y h w.val i) : (δ k) w=(δ i) w:=by
 induction k,t using Nat.le_induction with
 | base=> rfl
 | succ k t ih=> rw [← ih]; change store Y h (k+1) R L a A (F _ (days Y h (k+1) R L a w))= _; rw [nectar_next Y h k R L a w (arriving Y h i k a w c t), P'.tall k (p.trans t), for_next]; rfl
private lemma habit : ∃ y:A.space, ∀ᶠ i:ℕ in atTop,(δ i) w=y:=by obtain ⟨n,t,v⟩:= ((eventually_ge_atTop s).and (arrived Y h w.val)).exists; exact ⟨_,(eventually_ge_atTop n).mono fun i p=> looking Y h s n i R L a A w F B P' t p v⟩
private abbrev look :A.space:= (habit Y h s R L a A w F B P').choose
local notation "Φ" w:max=> look Y h s R L a A w F B P'
private lemma hairpin (p:s ≤ i)(t:Arrive Y h w.val i): (δ i) w= Φ w:=by
 obtain ⟨k,g,q⟩:= ((eventually_ge_atTop i).and ((habit Y h s R L a A w F B P').choose_spec)).exists; exact (looking Y h s i k R L a A w F B P' p g t).symm.trans q
private def quip : Vect Y h a 0 →ₗ[ℂ] A.space where
 toFun w:= look Y h s R L a A w F B P'
 map_add' u v:= by
    obtain ⟨n,p,q,g,t⟩:= ((eventually_ge_atTop s).and (((arrived Y h u.val).and ((arrived Y h v.val).and (arrived Y h (u+v).val))))).exists
    rw [←hairpin Y h s n R L a A _ F B P' p t,←hairpin Y h s n R L a A _ F B P' p q,←hairpin Y h s n R L a A _ F B P' p g,map_add]
 map_smul' c v:=by
    obtain ⟨n,p,g,t⟩:= ((eventually_ge_atTop s).and ((arrived Y h v.val).and (arrived Y h (c • v).val))).exists
    rw [←hairpin Y h s n R L a A _ F B P' p t,←hairpin Y h s n R L a A _ F B P' p g,map_smul]; rfl
lemma quip_norm : ‖(quip Y h s R L a A F B P') w‖ ≤ B*‖A.paid w‖:=by
 obtain ⟨n,t,c⟩:= ((eventually_ge_atTop s).and (arrived Y h w.val)).exists
 rw [←contains Y h n R L a A w c, show (quip Y h s R L a A F B P') w =_ from (hairpin Y h s n R L a A w F B P' t c).symm]; exact P'.fit n t _

def qubit : A.space.Op:= (quip Y h s R L a A F B P').extendOfNorm A.paid
lemma qubit_norm (p:0≤B): ‖qubit Y h s R L a A F B P'‖ ≤ B:= LinearMap.opNorm_extendOfNorm_le A.issued p fun x=>quip_norm Y h s R L a A x F B P'
lemma qubit_seed (p:s ≤ i): qubit Y h s R L a A F B P' ((G i) x)=(G i) (F i x):=by
 have h': Arrive Y h (seedling Y h i a x).val i:= pulse_arr Y h i x.val
 rw [clapper Y h i R L a A x]; unfold qubit; rw [LinearMap.extendOfNorm_eq A.issued ⟨B,fun i=>quip_norm Y h s R L a A i F B P'⟩]
 refine (hairpin Y h s i R L a A (seedling Y h i a x) F B P' p h').symm.trans ?_; unfold dressing; simp_rw [LinearMap.comp_apply,fullDay]
omit P'
-- powers representation, space or positive time binder
variable (z:ℤ)
private lemma react (p:j=a→0≤z): Canaan Y h a (clockW Kₜ j z x.val) 0:=by
 by_cases h':j=a; · subst j; apply Canaan.subh Y h a _ _ (Canaan.flight Y h a x.val z x.property); have he:= p rfl; positivity
 exact Canaan.over Y h a j x.val z x.property h'
private abbrev tickR (p:j=a→0≤z) : Decko Y h a := ⟨clockW Kₜ j z x.val,react Y h a j x z p⟩ -- binder x before shadowed a problematic
variable (p:j=a→0≤z)
def hoist : Decko Y h a →ₗ[ℂ] Decko Y h a where
 toFun x:= tickR Y h a j x z p
 map_add' x y:= Subtype.ext (clock_sum ..)
 map_smul' c x:= Subtype.ext (clock_scale ..)

lemma hoist_val : (hoist Y h a j z p x).val=clockW Kₜ j z x.val:=rfl
lemma hoist_zero : hoist Y h a j 0 (fun _=>le_rfl) x=x:= Subtype.ext (tic_zero ..)
lemma hoist_sum (z' z₁:ℤ)(p':j=a→0≤z')(p₁:j=a→0≤z₁)(c:z+z'=z₁): hoist Y h a j z p (hoist Y h a j z' p' x)=hoist Y h a j z₁ p₁ x:=by
 apply Subtype.ext; rw [hoist_val,hoist_val,hoist_val, clock_add,c]
lemma hoist_cross (t:Axis)(f:ℤ)(u:t=a→0≤f):
    hoist Y h a j z p (hoist Y h a t f u x) = hoist Y h a t f u (hoist Y h a j z p x):= Subtype.ext (clock_cross ..)
lemma hoist_up : nectar Y h s R L a (hoist Y h a j z p x)=hoist Y h a j (Λ.R.L.val*z) (fun i=>mul_nonneg (by positivity) (p i)) (nectar Y h s R L a x):= Subtype.ext (promote_clock Y h s R L j z x.val)
-- all Proofs for space/time with same P aids
abbrev tickT (x: W (tent Y h))(t:ℕ):= clockW (tent Y h) a t x
abbrev vectorT (x:Decko Y h a)(t:ℕ):=hoist Y h a a t (fun _=> Nat.cast_nonneg' _) x
include A in
lemma time_contr (n:ℕ) : ‖store Y h s R L a A (vectorT Y h a x n)‖ ≤ ‖store Y h s R L a A x‖:= by
 induction n with
 | zero=> rw [show vectorT Y h a x 0=x from hoist_zero Y h a a x]
 | succ n ih =>
   refine le_trans ?_ ih; let v':= vectorT Y h a x n
   obtain ⟨S,u,v⟩:=v'.property
   refine (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp ?_; simp_rw [normStore]; rw [show vectorT Y h a x (n+1)=hoist Y h a a 1 (fun _=> zero_le_one) v' from ?_,hoist_val]; exact contraction a Y h S s v'.val v u R -- order
   exact (hoist_sum Y h a a x _ _ _ _ _ _ (by omega)).symm
include A in
lemma space_safe (t:j≠a) : ‖(G s) (hoist Y h a j z p x)‖ = ‖(G s) x‖:=by
 let f:= clockW Kₜ j z
 apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp; rw [normStore,normStore,hoist_val,helve, clock_normal Kₜ j a 0 z x.val (Ne.symm t),← clock_mul,invariantW Y h s j z R]
private lemma hoist_cost : ‖(G s) (hoist Y h a j z p x)‖ ≤ ‖(G s) x‖:=by
 by_cases e:j=a; swap; · exact (space_safe Y h s R L a j A x z p e).le
 subst j; obtain ⟨n,rfl⟩:= Int.eq_ofNat_of_zero_le (p rfl) -- lemma form?
 exact time_contr Y h s R L a A x _
-- measure in units of tic Kₜ gauge = matter/2, `(L.val ^ -(s+1))` if matter base normal.No shrink factor here, debate next files. `tick scale`
abbrev scaleR (Λ:Preparation)(s i:ℕ)(z:ℤ):ℤ:= (Λ.R.L.val:ℤ)^(i-s)*z
lemma scale_step(t:s ≤ i): scaleR Λ s (i+1) z=(Λ.R.L.val:ℤ)*scaleR Λ s i z:=by unfold scaleR; rw [show i+1-s=i-s+1 from by omega, pow_succ']; ring
abbrev positive_scale (L:Side)(i:ℕ){a j:Axis}(p:j=a→0≤z)(e:j=a) : 0 ≤ (L.val:ℤ)^i*z := mul_nonneg (by positivity) (p e) -- not needed
private abbrev fScale(i:ℕ):Decko Y h a→ₗ[ℂ] Decko Y h a := hoist Y h a j (scaleR Λ s i z) (positive_scale z Λ.R.L (i-s) p)
private lemma scales : Robing Y h s R L a A (fScale Y h s a j z p) 1:=by
 constructor; swap; · intro n t x; rw [one_mul]; exact hoist_cost Y h n R L a j A x (scaleR Λ s n z) _
 intro n t x; unfold fScale; rw [hoist_up Y h n R L a j x _]; apply Subtype.ext; rw [hoist_val, hoist_val,scale_step _ _ _ t] -- dependent rw? after hoist_val
def tock: A.space.Op:= qubit Y h s R L a A (fScale Y h s a j z p) 1 (scales Y h s R L a j A z p)
lemma earn_seed (v:s ≤ i): tock Y h s R L a j A z p ((G i) x)= store Y h i R L a A (hoist Y h a j (scaleR Λ s i z) (positive_scale z Λ.R.L (i-s) p) x) := qubit_seed Y h s i R L a A x _ 1 _ v
lemma toll_bound : ‖tock Y h s R L a j A z p‖ ≤ 1:= qubit_norm Y h s R L a A _ 1 _ zero_le_one
#print axioms toll_bound
end Chrono
end YM.CF.Buffered.Afterglow.Hierarchy
