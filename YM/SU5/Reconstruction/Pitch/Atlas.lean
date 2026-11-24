import YM.SU5.Reconstruction.Pitch.Coupling
set_option autoImplicit false
set_option synthInstance.maxSize 30000
set_option maxRecDepth 5000
set_option maxHeartbeats 300000
noncomputable section

namespace YM.CF.Buffered.Afterglow.Tower.FirstWindows
open Function Set Filter NormedSpace Lattice Wilson Cube MeasureTheory Reflect Advance
  Scroll Skye Window Journey Satin Tapestry
open Vacancy Selected SatinVerification Py Py.Rate LocalLimit Preparation
open scoped Topology BigOperators ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra

variable {Λ : Preparation} {l : ℕ} (Y : Course Λ (VolumeCape.Dream.Nimbus l))
  (H : Real.exp 1 ≤ Λ.x)
local notation "K" => tent Y H
variable {i k : ℕ → ℕ} {I : ℕ → Family (tent Y H) → ℕ → ℂ}
  {E : ℕ → Family (tent Y H) → ℂ} (V : Universal Y H i k I E)
  (G : GroundExtension (i := i) (k := k) (E := E) Y H)
namespace Pitch
open Nymph
open SlabMark MeshClock PhaseChoice Chambers Germ
variable {J : Calibration} {y w : Set RSpace} {q : Bool}
local notation "L" => Λ.R.L
local notation "D" => Domain Y H G
set_option quotPrecheck false

local notation "τ"=> marks (loomD Λ)
abbrev Atlas (Λ:Preparation):= Axis → (marks (loomD Λ))
local notation "Ω"=> Atlas Λ
open Schedule Fixture Compose
variable (p:Atlas Λ) (t:List Axis) (f:Sky J)
noncomputable def promenade (J:Calibration): Sky J →ₗ[ℂ] Sky J:= t.foldr (fun i g=> (trek J i (p i)).comp g) LinearMap.id
local notation "Pm" t:max p:max=>promenade p t
lemma promenade_step (j:Axis): (promenade p (j::t) J) f=trek J j (p j) ((promenade p t J) f):= rfl
private def dwell (u:List Axis) : RSpace:= (u.map fun i=> eject i ((p i):ℝ)).sum
lemma addresses_bought (i:Axis)(h:t.Nodup): dwell p t i= if i∈ t then (p i:ℝ) else 0:=by induction t with
 | nil=> simp [dwell]
 | cons j t ih=>
   rw [show dwell p (j::t)=_ from (show dwell p (j::t)= eject j (p j:ℝ)+dwell p t from rfl), Pi.add_apply,ih (List.nodup_cons.mp h).2] -- may show rhs bug as earlier
   by_cases q:i=j; · subst i; simp [(List.nodup_cons.mp h).1]
   simp [q]
-- linear map all displacements
noncomputable def constellation (p:Atlas Λ) (J:Calibration) : Sky J →ₗ[ℂ] Sky J:= promenade p ordinate J
local notation "Φ" p:max=> constellation p
-- physical translation used by these tests. ordinal supports shift at `coverPoint`.
noncomputable def coverPoint (p:Atlas Λ) : RSpace := fun i=>p i
private lemma promenade_inside (f: Sky (tent Y H))(u:f∈ D q y): promenade p t K f ∈ D q (slides (dwell p t) y):=by
 induction t with
 | nil=> change f∈ D q (slides 0 y); rwa [slides_zero]
 | cons i t ih=> rw [promenade_step,show dwell p (i::t)=eject i (p i:ℝ)+dwell p t from rfl,←slides_comp]; exact trek_region Y H G i _ _ ih
lemma coverPoint_inside (f:Sky (tent Y H))(u:f∈D q y): constellation p (tent Y H) f∈D q (slides (coverPoint p) y):=by
 rw [constellation,show coverPoint p=dwell p ordinate from (funext fun i=> (addresses_bought p _ i ordinate_one).trans (if_pos (ordinates i))).symm]; exact promenade_inside Y H G p _ f u
lemma promenade_nil (t:List Axis) : promenade (0:Ω) t J f=f:=by induction t with
 | nil=>rfl
 | cons i t ih=>rw [promenade_step,ih]; exact trek_zero ..
@[simp] lemma constell_zero (Λ:Preparation) (f:Sky J): constellation (0:Atlas Λ) J f=f:=promenade_nil ..
lemma promenade_pass (v:τ)(x:Axis) : trek J x v ((Pm t p) J f)=(Pm t p) J (trek J x v f):=by induction t with
 | nil=>rfl
 | cons i t ih=>rw [promenade_step,trek_cross,promenade_step,ih]
private lemma promenade_add (q:Ω): promenade p t J (promenade q t J f)= promenade (p+q) t J f:=by induction t with
 | nil=>rfl
 | cons i t ih=>
     rw [promenade_step,promenade_step,promenade_step,←promenade_pass] -- tune
     rw [ih,trek_add]; rfl
lemma cover_plus (q:Ω) : constellation p J (constellation q J f)=constellation (p+q) J f:= promenade_add p ordinate f q
lemma cover_times (x:Sky J): constellation p J (x*f)= constellation p J x*constellation p J f:=by
 unfold constellation; generalize ordinate=t; induction t with
 | nil=> rfl
 | cons i t ih=> rw [promenade_step,promenade_step,promenade_step,ih,trek_mul]
lemma cover_id (J:Calibration): constellation p J 1=1 := by
 unfold constellation; generalize ordinate=t; induction t with
 | nil=> rfl
 | cons i t ih=> rw [promenade_step,ih,trek_vac]

variable (a:Axis) (c : ∀ j:Axis,Arena Y H G.history.circuit j 0 false)
lemma cover_solo (j:Axis)(v:τ) : constellation (eject j v) J f= trek J j v f :=by
 suffices p:∀ t:List Axis, t.Nodup → promenade (eject j v) t J f= if j∈ t then trek J j v f else f from (p ordinate ordinate_one).trans (if_pos (ordinates j))
 intro t; induction t with
 | nil=> simp; rfl
 | cons i t ih=>
   intro h; have p:=List.nodup_cons.mp h; rw [promenade_step,ih p.2]; by_cases u:i=j; · subst i; simp [p.1]
   simp [u, Ne.symm u]
-- discrepancy coset for reflection j, needed branch
noncomputable def opposite (p:Atlas Λ)(j:Axis) := p - (eject j (p j+p j))
lemma twist_axis (j:Axis): opposite p j j= -p j:=by unfold opposite; rw [Pi.sub_apply,eject_at]; abel
lemma twist_other (j k:Axis)(p':k≠j): opposite p j k= p k:=by unfold opposite; simp [p']
lemma flip_star (j:Axis): constellation (opposite p j) J (flipMark j J f)= flipMark j J (constellation p J f):=by
 unfold constellation; generalize ordinate=t; induction t with
 | nil=>rfl
 | cons i t ih=>
     rw [promenade_step,promenade_step,ih]; by_cases e:i=j; · subst i; rw [twist_axis,trek_flip,neg_neg]
     rw [twist_other p _ _ e, trek_other (p i) i j e]
section character
local notation "A"=> Warden Y H V G a c
local notation "NF"=>Domain Y H G false Set.univ
local notation "E₀" x:max=> osValue Y H V G a (c a) x
variable (x: Warden Y H V G a c)
-- induced at registration sphere. folds operators testing $Π$. equality by generator.
private lemma here_U (t:List Axis)(p:Ω)(f: NF): promenade p t (tent Y H) f.val∈ Domain Y H G false Set.univ:=by
 simpa only [slides_univ] using (promenade_inside Y H G p t f.val f.property)
lemma all_U (f: NF): constellation p K f.val∈ Domain Y H G false Set.univ:= here_U Y H G ordinate p f
noncomputable def horner (p:Atlas Λ) : (Domain Y H G false Set.univ)→ₗ[ℂ] Domain Y H G false Set.univ := ((constellation p (tent Y H)).comp (Domain Y H G false Set.univ).subtype).codRestrict NF (all_U Y H G p)
-- no continuity application: truly exact relation in one character
noncomputable def meritStyle (χ₁: Warden Y H V G a c) : Warden Y H V G a c:= t.foldl (fun x i=> wagerUp Y H V G a c i (p i) x) χ₁
local notation "Yt" p:max t:max x:max=> meritStyle Y H V G p t a c x
lemma march_mean (t:List Axis) (f:NF): (E₀ (Yt p t x)) f=(E₀ x) ⟨promenade p t K f.val,here_U Y H G t p f⟩:=by
 induction t generalizing x with
 | nil=>rfl
 | cons i t ih=>
   let z:= wagerUp Y H V G a c i (p i) x; change (E₀ (Yt p t z)) _ = _
   rw [ih z, show osValue Y H V G a (c a) z=(E₀ x).comp (plusLaw Y H G i (p i)) from neighbor_wager .. ]; rfl
noncomputable def leader (p:Atlas Λ) (χ : Warden Y H V G a c):= meritStyle Y H V G p ordinate a c χ -- args order? c vs p. implicit order first used
local notation "W" q:max=> leader Y H V G a c q
lemma leadership (p:Atlas Λ): osValue Y H V G a (c a) (leader Y H V G a c p x)=(E₀ x).comp (horner Y H G p) := LinearMap.ext fun f=> march_mean Y H V G p a c x ordinate f
lemma reflects_price (p:Atlas Λ) (ξ:NF): (E₀ x) (horner Y H G p ξ) = (E₀ ((W p) x)) ξ := (DFunLike.congr_fun (leadership Y H V G a c x p) ξ).symm -- order of p
lemma leadership_unique (p:Ω) (y:A) (h:osValue Y H V G a (c a) y=(E₀ x).comp (horner Y H G p)) : (W p) x=y:=ward_unique Y H V G a c _ y (h.trans (leadership Y H V G a c x p).symm)
@[simp] lemma leading_zero (x: Warden Y H V G a c) : leader Y H V G a c 0 x=x:= leadership_unique Y H V G a c x _ _ <| LinearMap.ext fun f=> congrArg (osValue Y H V G a (c a) x) (Subtype.ext (constell_zero Λ f.val)|>.symm) -- tune
lemma leading_plus (p q:Ω): (W q) ((W p) x)=(W (p+q)) x:= Eq.symm (leadership_unique Y H V G a c x (p+q) _ (by rw [leadership,leadership]; ext1 f; simp only [LinearMap.comp_apply]; exact congrArg (E₀ x) (Subtype.ext (cover_plus ..))))
lemma star_leading (j:Axis)(v:τ): leader Y H V G a c (eject j v) x=wagerUp Y H V G a c j v x:=by
 refine leadership_unique Y H V G a c x (eject j v) _ ?_; ext1 f; rw [show (osValue Y H V G a (c a) _) = _ from (show osValue Y H V G a (c a) (wagerUp Y H V G a c j v x)= (E₀ x).comp (plusLaw Y H G j v) from neighbor_wager ..)]; apply congrArg (E₀ x); exact Subtype.ext (cover_solo ..|>.symm)
-- only depends on Frontier parity sector; itinerary. finite indexing table.
local notation "Bv" => (marks (dainty Λ))
noncomputable def grown (q: Axis→marks (dainty Λ)):Atlas Λ:=fun i=> accept Λ (q i)
lemma even_lead (q:Axis → marks (dainty Λ)): (W (grown q)) x=x:=by unfold leader; generalize ordinate=y; induction y generalizing x with
 | nil=> rfl
 | cons i t ih=> change meritStyle Y H V G _ t a c (wagerUp Y H V G a c i (accept Λ (q i)) x)=_; rw [no_even]; exact ih x -- noEven order
lemma double_lead : (W p) ((W p) x)=x:=by
 choose q h using fun i=> duo (p i); rw [leading_plus,show p+p=grown q from funext fun i=> (h i).symm]; exact even_lead ..
lemma inverse_lead : (W (-p)) x=(W p) x:= by nth_rw 1 [←double_lead Y H V G p a c x]; rw [leading_plus,add_neg_cancel,leading_zero]
lemma leading_turn (j:Axis): (W (opposite p j)) x=(W p) x:=by
 unfold opposite; rw [sub_eq_add_neg,←leading_plus,inverse_lead,star_leading]; obtain ⟨q,h⟩:= duo (p j); rw [←h,no_even]
noncomputable def bits (Λ: Preparation)(t:Axis→Bool):Atlas Λ:= fun i=>if t i then eyeD Λ else 0
lemma choose_beacon : ∃ t : Axis → Bool, ∃ q:Axis→marks (dainty Λ), p=bits Λ t + grown q:=by
 choose q h using fun i=> couple (p i)
 refine ⟨fun i=> if p i=accept Λ (q i) then false else true, q, funext fun i=>?_⟩; by_cases v:p i=accept Λ (q i) <;> simp only [bits,v,↓reduceIte,Bool.false_eq_true, Pi.add_apply, zero_add] <;> try rfl
 exact (h i).resolve_left v
lemma basin_size (p:Ω): ∃ t:Axis→Bool, (W p) x=(W (bits Λ t)) x:=by obtain ⟨t,q,rfl⟩:=choose_beacon p; exact ⟨t,(leading_plus ..|>.symm).trans (even_lead ..)⟩ -- compile
end character
end Pitch
end YM.CF.Buffered.Afterglow.Tower.FirstWindows
