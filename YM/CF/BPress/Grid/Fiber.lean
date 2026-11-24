import YM.CF.BPress.Grid.Axial
import YM.CF.BPress.Selector
/-!
The extension step on a mesh entity, using the scaled extensions on cubes and parallel price.
Handles frames, and later the sphere-valued X field also. No changing scales in the extension
constants. Step-indexed parallel data W (may have been extracted at a long stride).
-/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BPress.Grid
open Function Finset Lattice MeasureTheory Filter
open scoped BigOperators Topology NNReal Classical
variable {G:Gauge} {d : ℕ} {s : Side}
variable (G) (d) (F : Type) [MetricSpace F] [Nonempty F]
structure Delivery where
  ship : F → G.El → F
  one x : ship x 1=x
  after (x g h) : ship (ship x g) h=ship x (g*h)
  iso g x y : dist (ship x g) (ship y g)=dist x y
  κ : ℝ≥0
  track f x y : dist (ship f x) (ship f y)≤ κ * chord x y
  cont : Continuous (fun x : F × G.El => ship x.1 x.2)
  buy (K:ℝ≥0): ∃ C:ℝ≥0, ∀ s ⊆ rim d, ∀ f:Desk d→ F,LipschitzOnWith K f s → ∃ g:Desk d→ F, LipschitzOnWith C g (table d) ∧ Set.EqOn f g s
variable {G d F}
abbrev Fabric (d:ℕ)(s:Side)(F:Type) := Space d s → F
namespace Delivery
variable [CompactSpace F] (D : Delivery G d F){k:Tiling s}
variable (J : Entity k d)(W : GaugeField G d s)
def speed (f:Fabric d s F)(a:Coord d)(i:Fin d):=dist (D.ship (f (J.heart a)) (J.along W a i)) (f (J.heart (tick a i)))
def Speed (f:Fabric d s F)(L:ℝ) : Prop:= ∀ a i,J.Valid (tick a i)→ D.speed J W f a i≤L / k.b.val
def Before (f:Fabric d s F)(L:ℝ) : Prop:= ∀ a i,J.Valid (tick a i)→ ∀ j t,J.OnFace a j t → J.OnFace (tick a i) j t → D.speed J W f a i≤ L / k.b.val
variable (f:Fabric d s F)
abbrev coords (a:Coord d) := D.ship (f (J.heart a)) (J.carry W a)⁻¹
lemma carry_budget {m : ℝ} (h:J.flat W m) (p:0≤m) (a:Coord d)(i:Fin d) (e:J.Valid (tick a i)) :
    |D.speed J W f a i-dist (D.coords J W f a) (D.coords J W f (tick a i))| ≤ (D.κ:ℝ) * (d*k.b.val*m):= by
  let b:= tick a i; let A:=J.carry W a; let B:=J.carry W b; let x:=D.coords J W f a
  have he:Entity.weight a ≤ d*k.b.val:= (sum_le_sum (s:=univ) (f:=a) (g:=fun _=>k.b.val) (fun j _=>J.dim_max (J.valid_tick e) j)).trans_eq (by simp)
  have hl:chord (J.carry W a*J.along W a i) B ≤ _ := (chord.comm ..).le.trans (J.carry_defect W h p a i e)
  have hc:=D.iso B x (D.coords J W f b); rw [show D.ship (D.coords J W f b) B=f (J.heart b) by unfold coords B; rw [D.after, inv_mul_cancel,D.one]] at hc
  have hx : f (J.heart a)= D.ship x A:= by unfold x coords A; rw [D.after, inv_mul_cancel,D.one]
  change |dist (D.ship (f (J.heart a)) _) (f (J.heart b))-dist x (D.coords J W f b)| ≤ _; rw [←hc,hx,D.after]
  refine le_trans (abs_dist_sub_le ..) ((D.track x ..).trans (mul_le_mul_of_nonneg_left (hl.trans (mul_le_mul_of_nonneg_right ?_ p)) D.κ.property))
  exact_mod_cast he

def keep (f g:Fabric d s F):Prop:=∀ a, J.Valid a→ J.Boundary a→ g (J.heart a)=f (J.heart a)

section fill
open Entity
-- estimate form with m b² ≤ 1. View fill with L≥0 paid independent of stride b.
theorem grant_entity (L:ℝ)(t:0≤L) : ∃ K:ℝ, L≤K ∧ ∀ (s:Side)(k:Tiling s) (J:Entity k d)(W: GaugeField G d s), J.flat W ((k.b.val:ℝ)^2)⁻¹ → ∀ f, D.Before J W f L → ∃ g, keep J f g ∧ D.Speed J W g K := by
  let N:=(D.κ:ℝ)*(d:ℝ); have hh:0≤N:=by unfold N; positivity
  let a:= Metric.diam (Set.univ : Set F); have v:0≤a:=Metric.diam_nonneg
  let R:=L+N; have hR:0≤R:=by unfold R; positivity
  let M:ℝ≥0:=⟨2*(d:ℝ)*R+a, by positivity⟩; obtain ⟨C,X⟩:= D.buy M
  refine ⟨L+(C+N), le_add_of_nonneg_right (by positivity), fun s k J W p f h=>?_ ⟩
  let g:=D.coords J W f; let r:ℝ:=k.b.val; have hr:0<r:=by unfold r; positivity
  have P(w:Fabric d s F)(i : Fin d) (b:Coord d)(e:J.Valid (tick b i)) : |D.speed J W w b i - dist (D.coords J W w b) (D.coords J W w (tick b i))| ≤ N/r:= by
    apply (D.carry_budget J W w p (by positivity) b i e).trans_eq; change _ * (_ * r * (r^2)⁻¹) =_; unfold N; field_simp
  have hs:J.edgeBudget g R:= by
    intro a i _ z j t v l; change dist _ _ ≤ R/r; have hp:= (abs_le.mp (P f i a z)).1; have he : D.speed J W f a i ≤ L/r:=h a i z j t v l; unfold g R; rw [add_div]; linarith only [hp,he]
  let S:= {x : Coord d| J.Valid x∧ J.Boundary x}
  let u:=ration (k:=k) (d:=d); let A:=u '' S; let g' := g ∘ invFun u
  have h' : LeftInverse (invFun u) u:=leftInverse_invFun (ration_inj k)
  obtain ⟨g'',Y,v⟩:= X A (by rintro _ ⟨i,p,rfl⟩; exact J.rim_mem p.1 p.2) g' (by
      apply LipschitzOnWith.of_dist_le_mul; rintro _ ⟨x,p,rfl⟩ _ ⟨y,q,rfl⟩; unfold g'; rw [comp_apply,comp_apply,h' x,h' y]; exact J.across_price g R a hR v hs (Metric.dist_le_diam_of_mem (isCompact_univ.isBounded) (Set.mem_univ _) (Set.mem_univ _)) p.1 q.1 p.2 q.2)
  have hk (x):∃ u: F,J.contains x →∀ a:Coord d,J.Valid a→ J.heart a=x → u=D.ship (g'' (ration (k:=k) a)) (J.carry W a) := by
     by_cases e:J.contains x
     · obtain ⟨a,t,v⟩:=e; exact ⟨_,fun _ b f p=> congrArg (fun a=> D.ship (g'' (ration (k:=k) a)) (J.carry W a)) (J.inject t f (v.trans p.symm))⟩
     exact ⟨Classical.arbitrary _,fun p=>(e p).elim⟩
  choose w hw using hk
  have hg (a) (p:J.Valid a) : D.coords J W w a=g'' (ration (k:=k) a):=by unfold coords; rw [hw _ ⟨a,p,rfl⟩ a p rfl, D.after,mul_inv_cancel,D.one]
  refine ⟨w,fun a t g=> ?_,fun a i p'=>?_⟩
  · rw [hw _ ⟨a,t,rfl⟩ a t rfl,← v (show u a∈A from Set.mem_image_of_mem _ (show a∈S from ⟨t,g⟩)),show g' (ration (k:=k) a)=D.coords J W f a from congrArg (D.coords J W f) (h' a),coords,D.after,inv_mul_cancel,D.one]
  have he:= (abs_le.mp (P w i a p')).2; have hx:=Y.dist_le_mul _ (J.ration_mem (J.valid_tick p')) _ (J.ration_mem p'); rw [hg a (J.valid_tick p'),hg _ p'] at he; replace hx:= hx.trans (mul_le_mul_of_nonneg_left (ration_tick k a i) C.property); change _ ≤ (L+(C+N))/r; rw [add_div,add_div]; apply le_trans _ (le_add_of_nonneg_left (div_nonneg t hr.le)); change _ ≤ (C:ℝ)* _ at hx; change D.speed J W w a i ≤ _; simp only [← div_eq_mul_inv] at hx; change _≤ (C:ℝ)/r at hx; linarith only [hx,he]
end fill
end Delivery
end YM.CF.BPress.Grid
