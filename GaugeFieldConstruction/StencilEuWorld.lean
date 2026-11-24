/- This file incorporates modified third-party source. See the source attributions in notices/. -/ import YM.SU5.Registration.Ink.WavePort
import YM.Work.C15
/-! Recover positive-lag Ink from W moments. No locality, spectrum shape, full-body or further
    angular continuations at these Carton labels assumed. On THIS word. Terminal branch F & stamps
    can consequently be independently chosen at same registered letters to compare.
    Uses C15 Fourier argument (inverts lifts directly on compact frequency tests). -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.SatinWFixed.Euro
open Function Set Filter Distribution MeasureTheory Mink Poincare Boundary
open _root_.YM.Boundary.Probe
open scoped Topology BigOperators ContDiff InnerProductSpace
variable {V V':Type*} [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V'] {W:WView V} {n:ℕ}
open YM.Work.C15 (east_broad lifts_cancel restricted_continuous eq_of_tests)
private theorem temperedY_st {F:InkWaves V}(b:F.Breathes)(h:F.Bounds)(v:Fin n→V){y:Heights n}(hy:y∈east n):∃ u:Distn (Points n), ∀ f:Joint n,u f=F.psi v y f:=by
 obtain ⟨m,C,_,p⟩:= b n v; obtain ⟨k,hk,t⟩:= east_broad hy
 let U: Joint n→ₗ[ℂ]ℂ:=
    { toFun := F.psi v y
      map_add' := by
        intro f g
        unfold InkWaves.psi
        rw [← integral_add (h n v y hy f) (h n v y hy g)]
        apply integral_congr_ae; filter_upwards with x; simp [mul_add]
      map_smul' := by
        intro c f
        change (∫ x, F.restricted v y x * (c • f) x) = c * F.psi v y f
        rw [InkWaves.psi, ← integral_const_mul]; apply integral_congr_ae
        filter_upwards with x; simp; ring }
 have hu : Continuous U := sways (fun f => C*k⁻¹^m* weight f) (weight_cont.const_mul _) (by simp) (fun f => compromise f _ _ (p y k hk t))
 exact ⟨⟨U,hu⟩,fun _=>rfl⟩

lemma relative_integrals_st {F:InkWaves V}{G:InkWaves V'}{Y:WView V'}(b:F.Breathes)(h:F.Bounds)(d:F.during W)(a:G.Breathes)(l:G.Bounds)(e:G.during Y) (v:Fin n→V)(u:Fin n→V')(Z:W.W n v=Y.W n u)(y:Heights n)(Y':y∈east n)(f:Joint n):F.psi v y f=G.psi u y f :=by
 obtain ⟨U,t⟩:= temperedY_st b h v Y'; obtain ⟨V,p⟩:= temperedY_st a l u Y'
 have he (g:Joint n)(k:HasCompactSupport (g:Points n→ℂ)): Distn.fourier U g= Distn.fourier V g:=by
    let T:=lifts (-(dawn y)) g k; have ht':HasCompactSupport ⇑T := remains (-(dawn y)) g k
    have hz: Distn.fourier (W.W n v) T= Distn.fourier (Y.W n u) T:= Z ▸ rfl
    have hv: lifts (dawn y) T ht'=g:=lifts_cancel ..
    rw [d n v y Y' T ht',e n u y Y' T ht',hv,← t,← p] at hz;exact hz
 have hEq : Distn.fourier U = Distn.fourier V := by
    ext1 g
    exact tendsto_nhds_unique_of_eventuallyEq (((Distn.fourier U).continuous.tendsto g).comp (persistent g))
       (((Distn.fourier V).continuous.tendsto g).comp (persistent g))
       (Eventually.of_forall fun k=> he (cap k g) (finite_cap k))
 rw [← t,← p, ← Distn.one U, hEq, Distn.one]

private theorem inkContinuous_st {F : InkWaves V} (r : F.Region) (v : Fin n → V)
    {y : Heights n} (hy : y ∈ east n) : Continuous (F.restricted v y) := by
  have hc : Continuous (fun x : Points n => (shift x y, Boundary.trace x)) := by
    unfold shift Boundary.trace; fun_prop
  apply continuousOn_univ.mp ((r.together n v).comp hc.continuousOn (fun x _ => ?_))
  refine ⟨?_,mem_univ _⟩
  change (fun i => (shift x y i).im) ∈ east n
  simpa [shift] using hy

lemma relative_ink_st {F:InkWaves V}{G:InkWaves V'}{Y:WView V'}(b:F.Breathes)(h:F.Bounds)(d:F.during W)(a:G.Breathes)(l:G.Bounds)(e:G.during Y)(p:F.Region)(hp:G.Region) (v:Fin n→V)(u:Fin n→V')(Z:W.W n v=Y.W n u)(z:Times n)(x:SpacePoints n)(r:z∈strict n): F.F n z x v = G.F n z x u :=by
 let y:Heights n:= fun i=>(z i).im; let t:Points n:= place x (fun i=>(z i).re); have hz:y∈east n:=r; have he:F.restricted v y = G.restricted u y:= eq_of_tests _ _ (inkContinuous_st p v hz) (inkContinuous_st hp u hz) (relative_integrals_st b h d a l e v u Z y hz)
 have ht:=congr_fun he t; unfold InkWaves.restricted at ht; rwa [show Boundary.trace t=x from ?_,show shift t y = z from ?_] at ht
 · funext i; apply Complex.ext <;> simp [shift,t,place,y]
 change trace (place _ _)= _; ext1 i; simp [Boundary.trace,place]
#print axioms relative_ink_st
end YM.SatinWFixed.Euro
end
