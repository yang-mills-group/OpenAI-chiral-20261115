import GaugeFieldConstruction.Auburn
/-!
# U2 stress result (95)-(96), under (81) pair-statement
-/
set_option autoImplicit false
set_option synthInstance.maxSize 6800
noncomputable section
namespace YM.GaugeFieldConstruction.Ember
open Calibration Raw Cauchy LabelAction Empire Fathom Payroll Function Filter Set TopologicalSpace Analysis MeasureTheory Points Bulb Palace
open scoped Topology BigOperators ContDiff
open Floor Wick Invoice Gap Sailing Module
attribute [local instance] iG iF iX iU iT2 iW2 iV iS
variable {X : Type*} {ℱ : Filter X} {S : City} {P : Axis→Across} {q : X→Carat} (L:Sheds S P) (Y: Views S ℱ q)
local notation "l4"=>Calibration.lift Floor.four
-- free quadratic comparison minus budget

def tight (K : UV five→ UV five→ₗ[ℂ] Bond 2) (F : Across) (i : Axis): SymT→ₗ[ℂ] Probe×Raw.Sym→ℂ:= LinearMap.pi fun p=> survey p.1.1 ∘ₗ paid front i ∘ₗ K p.1.2 ∘ₗ F ∘ₗ LinearMap.proj p.2 ∘ₗ SymT.subtype
lemma tip (K F i) (v : Probe) (j) (t:SymT): tight K F i t (v,j)=paid front i (K v.2 (F (t.val j))) v.1.p:= rfl
lemma secure (i:Axis): Injective (tight silky (Calibration.deriv i) i):=by
  apply (detect _).mpr; intro t h; apply duo_d; intro v; apply nullB; intro s g
  rw [← clear_l]; exact (h ((g,s),v))
include L Y in
lemma receipt (i): Scores ℂ ℱ (tight silky (Calibration.deriv i) i) (fun k=> tight (lunar S (q k)) (levelP P (q k) i) i):= by
  intro p x; change Tendsto (fun k=>paid front i (lunar S (q k) p.1.2 (levelP P (q k) i (x.val p.2))) p.1.1.p) _ (𝓝 (paid front i (silky p.1.2 (Calibration.deriv i (x.val p.2))) p.1.1.p)); simp_rw [surveyed L, ← clear_point (x.val p.2) p.1.2 i,pays]; exact ((Y.pair ..).neg).neg
private instance : Module.Finite ℂ ↥SymT:=finiteInvariant ..
private instance : Module.Finite ℂ ↥BothV:=finiteInvariant ..
private instance : Module.Finite ℂ ↥OneW:=finiteInvariant ..

-- particular rescaled
lemma color (Q:Carat) (x : SymT) (w : UV five) (f : Foil) (j i) :
    tight (lunar S Q) (levelP P Q i) i x ((f,w),j)=Q.κ^2 • paid front i (S.spot (other ((Q.G five).c w)) front (P i ((Q.t x).val j))) (Q.u.rolled f).p:= by
  let h:=P i ((Q.t x).val j); let s:= S.spot (other ((Q.G five).c w)) front h
  rw [tip]
  have e : lunar S Q w (levelP P Q i (x.val j))=Q.κ • (s ∘ₗ Q.u.roll) := by
    ext1 p; rw [lucid,vert]; simp only [map_smul,LinearMap.smul_apply]; congr 2; unfold s h; rw [Q.t_pay] -- adjust
  change paid front i (lunar S Q w _) _=_; rw [e,map_smul,LinearMap.smul_apply,← Q.u.roll_price, LinearMap.smul_apply,smul_smul,pow_two]; rfl
include L Y
lemma secondly [ℱ.NeBot] (k : Axis) (t : SymT) (h:∀ i v (f:Foil), paid front k (S.spot (other v) front (P k (t.val i))) f.p=0): t=0 := by
  obtain ⟨f,H⟩:= (insight (secure k) (receipt L Y k)).1.exists
  let Q:= q f
  apply Q.t.symm.injective; rw [map_zero]; refine (detect _).1 H (Q.t.symm t) ?_; intro i
  obtain ⟨⟨j,w⟩,a⟩:= i; rw [color (q f) (Q.t.symm t) w j a k]; rw [show (q f).t _=t from Q.t.apply_symm_apply t,h]; simp
omit L in
lemma prism [ℱ.NeBot] (x: UV five) (h:∀ v (f:Foil), S.spot (other v) front x f.p=0):x=0 := by
  obtain ⟨k,v⟩:=(insight etaF₀ (send Y)).1.exists
  let Q:= q k; apply (Q.G five).c.symm.injective; rw [map_zero]
  refine (detect _).1 v _ (fun i=> ?_)
  change lunar _ _ i.2 _ _=_; rw [lucid, show ((q k).G five).c _=x from (Q.G five).c.apply_symm_apply x]; exact h _ ((q k).u.rolled i.1)

theorem supply_status [ℱ.NeBot] : Scope L where -- def include shadows?
  first k t T:=secondly L Y k t (fun i s f=>by rw [T,map_zero,map_zero]; rfl)
  second k t:= secondly L Y k t
  short x:=prism Y x
  rank:=by
    obtain ⟨k,h⟩:=(ranks (watch Y)).exists
    rw [own] at h; exact Nat.le_trans h (news _)
  diverg:=acquired L Y
end YM.GaugeFieldConstruction.Ember
