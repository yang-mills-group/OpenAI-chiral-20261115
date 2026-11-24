import YM.SU5.FiniteGaugeData.Hierarchy.Scorebook
/-! # prefix-reading at ALL resolutions of each stream -/
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
local notation "W₀" => GridStep Λ l S
variable {u v:ℕ→ℕ}{I:ℕ→Family (tent Y h)→ℕ→ℂ}{E:ℕ→Family (tent Y h)→ℂ}
variable {P:Call Λ l}{J:Wicket Λ l}
variable (K:Universal Y h u v I E)(R:Rolled Y h u v J P)
open Charm
namespace Playlist
namespace Show
local notation "M"=> Motif Kₜ
local notation "T"=> Theater Kₜ
local notation "W₁"=> W Kₜ
include K R

def preRoll (m:Motif (tent Y h)) : ℕ→ W (tent Y h)
 | 0=> m.val 0
 | s+1=> Charm.next Y h s K R (preRoll m s) * m.val (s+1)

omit K R in
lemma ends_mono (m:M) (v:Ends Kₜ m s)(a: s ≤ i) : Ends Kₜ m i:= fun _ t=> v _ (a.trans_lt t)

variable (m:Motif (tent Y h))
lemma stays (p:Ends Kₜ m s)(w: s ≤ i): E i (preRoll Y h K R m i).val=E s (preRoll Y h K R m s).val:=by
  obtain ⟨i,rfl⟩:=Nat.exists_eq_add_of_le w; clear w; induction i with
  | zero=> rfl
  | succ i ih=>change E (s+i+1) (preRoll Y h K R m (s+i+1)).val= _; rw [preRoll,p _ (by omega),mul_one,foundation Y h (s+i) K R,ih]

def total (m:Motif (tent Y h)) := let i:= (ends_exists Kₜ m).choose; E i (preRoll Y h K R m i).val
lemma total_score (p: Ends Kₜ m s): total Y h K R m=E s (preRoll Y h K R m s).val := by
  let i:= (ends_exists Kₜ m).choose; unfold total; exact (stays Y h i (s+i) K R m (ends_exists Kₜ m).choose_spec (by omega)).symm.trans (stays Y h s (s+i) K R m p (by omega))

/-- Euclidean expectation of the mixed-resolution recipes. -/
def chorusRead : Theater (tent Y h) →ₗ[ℂ] ℂ := fill Kₜ (total Y h K R)

lemma octavian : chorusRead Y h K R 1=1:= by
  rw [chorusRead,MonoidAlgebra.one_def,fill_mode,one_smul,total_score Y h 0 K R 1 (fun _ _=>rfl)]; exact (K.gaugeMatter 0).1

variable (a:Axis)(z:ℤ) -- origin plane=z=multiple of 4B on gauge grid. at each step mirror all marked products on both arguments using scaled plane.
-- for advanced bands allow general aligned or at sufficiently fine *starting* level for this algebra, here aligned at 0
abbrev frameQ (Λ:Preparation)(z:ℤ)(s:ℕ):ℤ:= planeAt (Heat.gaugeShift Λ.block z) Λ.R.L s
omit R K in
lemma frame_step : frameQ Λ z (s+1)=(Λ.R.L.val:ℤ)*frameQ Λ z s:= (step_plane ..).symm
local notation "Z"=> frameQ Λ z
omit R K in
lemma frame_cash : frameQ Λ z s= Heat.gaugeShift Λ.block ((Λ.R.L.val:ℤ)^s*z):=by unfold frameQ planeAt Heat.gaugeShift; ring
abbrev Alone (x:Motif (tent Y h)) :Prop:= x∈ indoor Kₜ a (frameQ Λ z) (fun _=> reserve Λ l)
lemma located (p:Alone Y h a z m) : ∃ S:Finset Cover,Ahead a (frameQ Λ z s) (reserve Λ l) S∧ Locator Kₜ (preRoll Y h K R m s) S:=by
  induction s with
  | zero=> exact p 0
  | succ s ih=>
    obtain ⟨S',a',U⟩:=ih; obtain ⟨t,q,w⟩:=p (s+1)
    have h':= ahead_grid (Λ:=Λ) _ _ _ a'
    let D:= GridStep Λ l S'; rw [←frame_step] at h'
    exact ⟨D∪t,ahead_union _ _ _ _ h' q,locate_join Kₜ _ (locate_sub _ (Charm.locate_next _ _ _ _ K R _ U) subset_union_left) (locate_sub _ w subset_union_right)⟩

lemma replay (u:Motif (tent Y h))(e:Alone Y h a z u)(p:Alone Y h a z m):
    preRoll Y h K R ((opus Kₜ a (Z) u)*m) s= fire Kₜ a (Z s) (preRoll Y h K R u s)*preRoll Y h K R m s:=by
  induction s with
  | zero=> rfl
  | succ s ih=>
    rw [preRoll,steps_mult,ih]; obtain ⟨S',q,x⟩:=located Y h s K R u a z e; obtain ⟨T',r,y⟩:= located Y h s K R m a z p
    rw [Charm.separate Y h (refract a ((Z) s) S') T' s K R (locate_cold Kₜ S' a _ x) y (ahead_split S' T' a _ q r), next_mir Y h s K R,←frame_step, preRoll,preRoll, ice_join];
    exact Commute.mul_mul_mul_comm (b:=preRoll Y h K R m s|>Charm.next Y h s K R) (commW _ _ _) _ _
#print axioms replay

-- horizon common for THIS finite list/general Theater element only
omit K R in
abbrev Arrive (x:Theater (tent Y h))(s:ℕ):Prop:= ∀ m∈x.coeff.support, Ends Kₜ m s
omit K R in
lemma arrived (x:T) : ∀ᶠ s:ℕ in atTop, Arrive Y h x s:=by
  refine (eventually_all_finset x.coeff.support).mpr fun i p=>?_ ; obtain ⟨z,t⟩:= ends_exists Kₜ i; exact (eventually_ge_atTop z).mono fun i=> ends_mono Y h z i _ t
-- linear Seam after fixing wood
omit R in
def sight : W (tent Y h) →ₗ[ℂ] ℂ where
 toFun f:= E s f.val
 map_add' x y:=by
  rw [Subalgebra.coe_add,← mood_eq Y h s K _ ((well_for Kₜ x).1.add (well_for Kₜ y).1), K.pick.addA Y h s (well_for Kₜ x).1 (well_for Kₜ y).1, mood_eq Y h s K _ (well_for Kₜ x).1,mood_eq Y h s K _ (well_for Kₜ y).1]
 map_smul' c x:= by
  rw [Subalgebra.coe_smul,RingHom.id_apply,smul_eq_mul,← mood_eq Y h s K _ ((well_for Kₜ x).1.scale c), K.pick.smulA Y h s c (well_for Kₜ x).1,mood_eq Y h s K _ (well_for Kₜ x).1]

omit K R in
def freezing : W (tent Y h) →ₗ⋆[ℂ] W (tent Y h) := { toFun:= fire Kₜ a z, map_add':= ice_more Kₜ a z,map_smul':= fun c x=> ice_paid Kₜ a z x c }

def collapse : Theater (tent Y h) →ₗ[ℂ] W (tent Y h):= fill Kₜ fun i=> preRoll Y h K R i s
lemma ties (x:T)(p:Arrive Y h x s): chorusRead Y h K R x= E s (collapse Y h s K R x).val:=by
  change _= sight Y h s K (collapse Y h s K R x); unfold chorusRead collapse; rw [fills,fills,map_sum]; simp_rw [map_smul]; exact sum_congr rfl fun i t=> congrArg (x.coeff i • ·) (total_score Y h s K R i (p i t))

abbrev Half := active Kₜ (indoor Kₜ a (frameQ Λ z) (fun _=> reserve Λ l))
lemma foyer (x y:T)(p:x∈ Half Y h a z)(v:y∈Half Y h a z)(b:Arrive Y h x s)(t: Arrive Y h y s):
    let f:= collapse Y h s K R x; let g:= collapse Y h s K R y
    chorusRead Y h K R (intermezzo Kₜ a (Z) x*y)= E s (fire Kₜ a (Z s) f * g).val:=by
  intro f g; let C:= intermezzo Kₜ a (Z); let B:= freezing Y h a ((Z) s); let D(i:M):= preRoll Y h K R i s
  change chorusRead Y h K R (C x*y)=sight Y h s K (B f*g)
  let T':= chorusRead Y h K R
  have hx (i k:M)(m:i∈ x.coeff.support)(z':k∈ y.coeff.support)(c d:ℂ) :
      T' (C (MonoidAlgebra.single i c) * MonoidAlgebra.single k d) = sight Y h s K ((B (c • D i)) *(d • D k)):=by
    have V:Alone Y h a z i:= (active_iff ..).mp p _ m
    have H:Alone Y h a z k:= (active_iff ..).mp v _ z'
    have he:Ends Kₜ ((opus Kₜ a (Z) i)*k) s:= ends_mul Kₜ (ends_cold Kₜ a _ _ (b i m)) (t k z'); unfold T' C chorusRead; rw [moment_one,MonoidAlgebra.single_mul_single,fill_mode, total_score Y h s K R _ he,replay Y h s K R k a z i V H]
    change ((star c)*d) • ((sight Y h s K) (B (D i)* D k))= _; rw [map_smulₛₗ (f:=B),Algebra.smul_mul_assoc,Algebra.mul_smul_comm,map_smul,map_smul,smul_smul]; rfl
  unfold f g collapse; rw [fills,fills,map_sum,sum_mul]
  conv_lhs=> rw [←pick_all Kₜ x,←pick_all Kₜ y,map_sum,sum_mul]
  simp_rw [mul_sum,map_sum]; exact sum_congr rfl fun i h=> sum_congr rfl fun k t=> hx i k h t _ _

omit K R in
lemma port_union {t:ℤ} {I:Type*}(x: I→ W₁)(c:I→ℂ)(F:Finset I) (p:∀ i∈ F,∃ S:Finset Cover,Ahead a t (reserve Λ l) S∧ Locator Kₜ (x i) S): ∃ S:Finset Cover,Ahead a t (reserve Λ l) S∧ Locator Kₜ (∑ i∈ F,c i • x i) S:=by
 classical
 induction F using Finset.induction_on with
 | empty=> exact ⟨∅,by simp [Ahead],(by rw [sum_empty]; exact locate_zero Kₜ _)⟩
 | @insert i F b H=>
   obtain ⟨T',e,w⟩:= p i (mem_insert_self ..); obtain ⟨S,v,z⟩:= H fun j h=>p j (mem_insert_of_mem h)
   exact ⟨T'∪S,ahead_union _ _ a t e v,(by rw [sum_insert b]; exact locate_sum _ _ (locate_sub _ (locate_scale _ T' _ w) subset_union_left) (locate_sub _ z subset_union_right))⟩

-- any horizon with all insertions included gives this positive form
lemma ovation (x:T)(p:x∈ Half Y h a z):0 ≤ chorusRead Y h K R (intermezzo Kₜ a (Z) x*x):=by
  obtain ⟨i,e⟩:= (arrived Y h x).exists; rw [foyer Y h i K R a z x x p p e e]
  let b:= (Z) i; let y:=collapse Y h i K R x
  have hx: ∃ S, Ahead a b (reserve Λ l) S ∧ Locator Kₜ y S:= by
    unfold y collapse; rw [fills]; exact port_union Y h a _ _ _ fun j h'=> located Y h i K R j a z ((active_iff ..).mp p _ h')
  obtain ⟨S,v,H⟩:=hx; change 0 ≤ E i (reflector a ((Z) i) y.val*y.val)
  unfold b at v; rw [frame_cash] at v ⊢; exact ahead_positive Y h S i K a _ y.val H v -- unfold b first

-- reconstruction ABI (sesquilinear full local form on padded domain)
def roi (x y : Theater (tent Y h)): ℂ := chorusRead Y h K R (intermezzo Kₜ a (frameQ Λ z) x * y)
private lemma more₂ (x y z': Theater Kₜ): roi Y h K R a z x (y+z')=roi Y h K R a z x y+roi Y h K R a z x z':=by unfold roi; rw [mul_add,map_add]
private lemma more₁ (x y z': Theater Kₜ):roi Y h K R a z (x+y) z'=roi Y h K R a z x z'+roi Y h K R a z y z':=by unfold roi; rw [map_add,add_mul,map_add]
private lemma worth₂ (c:ℂ)(x y:T):roi Y h K R a z x (c•y)=c • roi Y h K R a z x y:=by unfold roi; rw [Algebra.mul_smul_comm,map_smul]
private lemma worth₁ (c:ℂ)(x y:T):roi Y h K R a z (c•x) y=star c • roi Y h K R a z x y:=by unfold roi; rw [inter_scale,Algebra.smul_mul_assoc,map_smul]

abbrev Vect (a:Axis)(z:ℤ) := (Half Y h a z:Type)

set_option linter.unusedVariables false in
def beams : Vect Y h a z →ₗ⋆[ℂ] (Vect Y h a z →ₗ[ℂ] ℂ) where
 toFun x := { toFun y:= roi Y h K R a z x.val y.val, map_add' f g:= more₂ .., map_smul' c f:=worth₂ .. }
 map_add' f g:= LinearMap.ext fun z'=> more₁ Y h K R a z ..
 map_smul' c f:=LinearMap.ext fun z'=> worth₁ Y h K R a z ..

lemma gleam (x: Vect Y h a z): 0≤beams Y h K R a z x x:=ovation Y h K R a z x.val x.property -- s unused
lemma together {I:Type*}[Fintype I](x:I→ Vect Y h a z):
    chorusRead Y h K R 1=1 ∧  Matrix.PosSemidef (Matrix.of fun i j=> chorusRead Y h K R (intermezzo Kₜ a (frameQ Λ z) (x i).val * (x j).val)) :=
  ⟨octavian Y h K R,(screenshots (beams Y h K R a z) (gleam Y h K R a z)).2 _ x⟩
#print axioms together
end Show
end Playlist
end YM.CF.Buffered.Afterglow.Hierarchy
