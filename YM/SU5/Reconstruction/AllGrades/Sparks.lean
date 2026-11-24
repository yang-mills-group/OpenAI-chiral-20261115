import YM.SU5.Reconstruction.AllGrades.AuroraWheel
/-! # Unconditional procurement at the chosen character. Takes leads on even ROOT only, costs on both grades. -/
-- Header
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option maxRecDepth 5000
set_option synthInstance.maxSize 32000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.FirstWindows.QuantaFields
open Function Set Filter NormedSpace Lattice Wilson Cube MeasureTheory Reflect Advance
  Scroll Skye Window Journey Satin Tapestry
open Vacancy Selected SatinVerification Py Py.Rate LocalLimit Preparation
open scoped Topology BigOperators ComplexOrder InnerProductSpace NNReal ENNReal Classical

attribute [local instance] opCStarAlgebra
open SlabMark MeshClock Tilted
variable {Λ : Preparation} {l : ℕ} (Y : Course Λ (VolumeCape.Dream.Nimbus l))
  (H : Real.exp 1 ≤ Λ.x)
local notation "K" => tent Y H
variable {i k : ℕ → ℕ} {I : ℕ → Family (tent Y H) → ℕ → ℂ}
  {E : ℕ → Family (tent Y H) → ℂ} (V : Universal Y H i k I E)
  (G : GroundExtension (i := i) (k := k) (E := E) Y H)
open Garret NorthTapes
open _root_.YM.Hilbert.Freight
variable (D:Invitation Y H G)
local notation "l₀" b:max s:max t:max F:max => launch Y H G D b s t F
variable (a:Axis)(b:Bool)(s:ℕ)
local notation "Sc"=>studio (tent Y H) a 0 b
variable (P: Inspector Y H G)
local notation "Ω"=> P.pulse
local notation "Bp" s:max => badge Y H V G D a b s P
local notation "hP" p:max f:max=> homePlane Y H V G D a b _ _ p f
local notation "W"=> poleForm (tent Y H) a 0 b
local notation "C₀"=> chime (tent Y H)
local notation "Θ"=> mirror (tent Y H)
local notation "L"=> Λ.R.L.val
open Heat
open Germ SelectionAnalysis
open Nymph Chambers
local notation "K₀"=> Works Y H V G D a b P
local notation "Wq" n:max=> walkC Y H a b n
local notation "R"=>carrier Y H V G D a b P
-- notation about Binder. 
local notation "Ξ"=>dainty Λ
variable (j:Trans a) (n:ℤ)
noncomputable def turnLane : Sc→ₗ[ℂ] Sc:= cart Y H a b j.val (2*n) (fun v=>False.elim (j.property v.symm))
local notation "jlΔ"=> turnLane Y H a b
lemma turn_lane_pass (x:Sc): inner ℂ ((Bp s) (jlΔ j n x)) ((Bp s) (jlΔ j n x)) = inner ℂ ((Bp s) x) ((Bp s) x):= rune_shift Y H V G D a b s P j.val n x x j.property.symm
lemma laneIso (x:Sc):‖(Bp s) (jlΔ j n x)‖= ‖(Bp s) x‖:= by nth_rw 1 [@norm_eq_sqrt_re_inner ℂ]; nth_rw 1 [@norm_eq_sqrt_re_inner ℂ]; rw [turn_lane_pass]
local notation "ρ" r:max=> castor Ξ s r n
lemma lane_up (t:ℕ)(i:s≤ t)(x:Sc): hP i (jlΔ j n x) = jlΔ j (ρ t) (hP i x):=by
 unfold turnLane; rw [cart_up]; apply DFunLike.congr_fun (cart_eq _ _ _ _ ?_) _; unfold castor; change (L:ℤ)^_ * _=2*((L:ℤ)^_* _); ring
lemma convenient (i t u:ℕ) (z:ℤ)(p:i≤ t)(v:t≤u) : castor Ξ t u (castor Ξ i t z)=castor Ξ i u z:=by unfold castor; rw [←mul_assoc,← pow_add,show u-t+(t-i)=u-i by omega]
lemma career : ∃ A:(Works Y H V G D a b P)→L[ℂ] (Works Y H V G D a b P), ‖A‖≤1∧∀ t≥s,∀ x:Sc, A ((Bp t) x)=(Bp t) (jlΔ j (ρ t) x):=by
 let f(t:ℕ)(_p:t≥s):Sc→ₗ[ℂ] K₀:=(Bp t).comp (jlΔ j (ρ t))
 refine (R).bound s f (fun {t u} i k x=>?_) _ zero_le_one (fun t u x=> (laneIso Y H V G D a b t P j (ρ t) x).trans_le (one_mul _).ge)
 change (Bp u) (jlΔ j (ρ u) (hP k x))=(Bp t) (jlΔ j (ρ t) x); rw [badges_join Y H V G D a b P k,lane_up,convenient (Λ:=Λ) s t u n i k]
noncomputable def jolt:=(career Y H V G D a b s P j n).choose
local notation "J" s:max j:max n:max=> jolt Y H V G D a b s P j n
lemma joltQ : ‖J s j n‖ ≤ 1:= (career Y H V G D a b s P j n).choose_spec.1
lemma atTopLane (t:ℕ)(i:s≤ t)(x:Sc) : (J s j n) ((Bp t) x)=(Bp t) (jlΔ j (ρ t) x):=(career Y H V G D a b s P j n).choose_spec.2 t i x
lemma atLane (x:Sc) : (J s j n) ((Bp s) x)=(Bp s) (jlΔ j n x):=by rw [atTopLane Y H V G D a b s P _ _ s le_rfl]; simp only [castor,Nat.sub_self,pow_zero,one_mul]
lemma shift_sums (l':ℤ)(x:Sc): jlΔ j l' (jlΔ j n x)= jlΔ j (l'+n) x:=Subtype.ext (by change chime K _ _ (chime K _ _ _) = chime K _ _ _; rw [march_sums j.val b ((atSouth Y H a b x).choose_spec.1),mul_add])
lemma jolt0:J s j 0 = ContinuousLinearMap.id ℂ K₀:=by
 apply badges_ext Y H V G D a b s P; intro i v x; rw [atTopLane Y H V G D a b s P _ _ i v,show jlΔ j (castor (dainty Λ) s i 0) x=x from ?_]; rfl
 exact Subtype.ext (by change chime (tent Y H) _ _ _= _; unfold castor; rw [mul_zero,mul_zero,march_zero j.val b ((atSouth Y H a b x).choose_spec.1)])
lemma jolts_grow(t:ℕ)(p:s≤ t): J s j n= J t j (ρ t):=by apply badges_ext Y H V G D a b t P; intro i v x; rw [atTopLane Y H V G D a b s P _ _ i (p.trans v),atTopLane Y H V G D a b t P _ _ _ v,convenient s t i n p v]
lemma jolts_add (k':ℤ): (J s j n).comp (J s j k')=J s j (n+k'):=by
 apply badges_ext Y H V G D a b s P; intro i v x; rw [ContinuousLinearMap.comp_apply,atTopLane Y H V G D a b s P _ _ i v,atTopLane Y H V G D a b s P _ _ i v,atTopLane Y H V G D a b s P _ _ i v,shift_sums]; unfold castor; rw [mul_add]
lemma jolts_eachother (k':Trans a)(l':ℤ)(t:ℕ): Commute (J s j n) (J t k' l'):=by
 apply badges_ext Y H V G D a b (max s t) P; intro i v x; let p:=(le_max_left s t).trans v; let p':=(le_max_right s t).trans v; change (J s j n) ((J t k' l') ((Bp i) x))= (J t k' l') ((J s j n) ((Bp i) x)); simp_rw [atTopLane Y H V G D a b t P k' l' i p', atTopLane Y H V G D a b s P j n i p,atTopLane Y H V G D a b t P k' l' i p']; unfold turnLane; rw [cart_comm]
noncomputable def wider : Lunation (dainty Λ) K₀ where
 nav s l':=J s j l'
 zero s:= jolt0 ..
 sums s v t:= jolts_add ..
 changeover s t p v:= jolts_grow Y H V G D a b s P j v t p
 limited s i:= joltQ ..
local notation "¿J" p:max=> wider Y H V G D a b P p
noncomputable def regime : Germ.Alliance (Trans a) (marks (dainty Λ)) (Works Y H V G D a b P) where
 crew j:= (¿J j).plays
 cCom x y i j:= by obtain ⟨t,v,rfl⟩:=notch_exists Ξ i; obtain ⟨z,w,rfl⟩:=notch_exists Ξ j; change ((¿J x).ship _).comp ((¿J y).ship _) = ((¿J y).ship _).comp ((¿J x).ship _); rw [Lunation.navZ,Lunation.navZ]; exact jolts_eachother Y H V G D a b t P x v y w z
local notation "C" o:max=> (regime Y H V G D a b P).crew o
lemma regime_value : (C j).play (notch Ξ s n)= J s j n:= (¿J j).navZ _ _
-- uncond purchase commute with these translation invariants and all heat
variable (A:Impetus Y H V G D a b P)
include A
local notation "E★" t:max u:max=> older Y H V G D a b t P A u
local notation "σ"=> wheelTimes Y H V G D a b P A
lemma aside_jolt (v:ℕ)(t:ℕ): Commute (J s j n) (E★ t v):=by
 apply badges_ext Y H V G D a b (max s t) P; intro i u x; let p:=(le_max_left s t).trans u; let p':=(le_max_right s t).trans u; change (J s j n) ((E★ t v) ((Bp i) x))= (E★ t v) ((J s j n) ((Bp i) x)); simp_rw [old_pays Y H V G D a b t P A v p', atTopLane Y H V G D a b s P j n i p,old_pays Y H V G D a b t P A v p']; unfold turnLane walkC; rw [cart_comm]
variable (p : marks (dainty Λ))
lemma commutes_heat (u:ℝ≥0) : ((C j).play p).comp ((σ).E u)= ((σ).E u).comp ((C j).play p):=by
 obtain ⟨s,v,rfl⟩:= notch_exists (dainty Λ) p
 rw [regime_value]; let p:=J s j v; let F:=σ; ext1 x
 have ht(t:ℕ)(w:ℕ): p (F.E (whenly Ξ t w) x)= F.E (whenly Ξ t w) (p x):=by
    unfold F; rw [ages_track]; exact DFunLike.congr_fun (aside_jolt Y H V G D a b s P j v A w t).eq x
 apply closure_minimal (s:=times Ξ) (t:={u:ℝ≥0|p (F.E u x)=F.E u (p x)}) ?_ (isClosed_eq (p.continuous.comp (F.continuousE x)) (F.continuousE (p x))) (fills Ξ u)
 rintro i ⟨q,w,rfl⟩; exact ht q w

end YM.CF.Buffered.Afterglow.Tower.FirstWindows.QuantaFields
#print axioms YM.CF.Buffered.Afterglow.Tower.FirstWindows.QuantaFields.regime_value
#print axioms YM.CF.Buffered.Afterglow.Tower.FirstWindows.QuantaFields.atTopLane
#print axioms YM.CF.Buffered.Afterglow.Tower.FirstWindows.QuantaFields.commutes_heat
