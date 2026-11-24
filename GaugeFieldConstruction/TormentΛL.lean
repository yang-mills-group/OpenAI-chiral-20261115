import GaugeFieldConstruction.VegaΛL
/-!
 # Locally determining. Use W all contour prices, compare inside same determining system. Restrict Eu costs to one nonempty box. Can take all points ordered in ALL axes still in that box. Uniqueness via totally-real tube. Gives W determined THERE and all Eu Conf prices too. Conversely from W distributions. drape fixed, keep comparison even if registration reuses D.
-/
set_option autoImplicit false
set_option synthInstance.maxSize 15000
set_option maxHeartbeats 300000
noncomputable section
namespace YM.NSF.Boundary
open YM.Boundary Function Filter Set Finset Mink MeasureTheory Analysis Kernel Complex
open scoped BigOperators Topology ContDiff InnerProductSpace
open NSF.Work.C20
variable {n:ℕ}
-- every nonempty open admits configurations plenum inside. Use strict monotone along all coordinates, not just plenum.comparison meaningful for frames with all readings.
variable (U:Set E4)
def HeldΛL (n:ℕ):Set (Points n):= ⋂ i:Fin n,(fun p:Points n=>p i)⁻¹' U
def RipenΛL (n:ℕ):Set (Points n):=⋂ a:Axis,(fun p:Points n=>(fun i=> p i a))⁻¹' east n
def RibΛL (n:ℕ):= HeldΛL U n ∩ RipenΛL n
lemma OΛRibL (h:IsOpen U): IsOpen (RibΛL U n):= IsOpen.inter (isOpen_iInter_of_finite (fun i:Fin n=> h.preimage (by fun_prop))) (isOpen_iInter_of_finite (fun a:Axis=> (open_east n).preimage (by fun_prop)))
lemma WΛOrderL: RibΛL U n⊆ordered n:=fun x h=> mem_iInter.mp h.2 timeAxis
lemma ΨΛRibL (h:IsOpen U)(p:U.Nonempty) : (RibΛL U n).Nonempty :=by
 obtain ⟨i,k⟩:=p; let f:E4:=WithLp.toLp 2 fun _=>1; let Y(r:ℝ):Points n:=points fun j=>i+((j.val:ℝ)*r) • f
 have he:∀ᶠ r in 𝓝[>] (0:ℝ), Y r∈HeldΛL U n:=by
    have hc:Continuous Y:=by unfold Y points; fun_prop
    have hp:Y 0∈HeldΛL U n:=by simp [Y,HeldΛL,k]
    exact (hc.continuousWithinAt (s:=Ioi (0:ℝ))) ((show IsOpen _ from isOpen_iInter_of_finite (fun i:Fin n=> h.preimage (show Continuous (fun p:Points n=>p i) from by fun_prop))).mem_nhds hp)
 have hl(r:ℝ)(e:0<r):Y r∈RipenΛL n:=by
    apply mem_iInter.mpr; intro a l m h
    change (i+((l.val:ℝ)*r) • f) a<(i+((m.val:ℝ)*r) • f) a; simp [f,mul_lt_mul_iff_of_pos_right e,show l.val<m.val from h]
 obtain ⟨u,e,a⟩:= (he.and self_mem_nhdsWithin).exists; exact ⟨_,e,hl u a⟩
variable {G:Gauge}{L:Register G}{S:Table L}{Y X:Surface S}{F K:Waves S}{D:∀ n,Blanket n}{V: X.Aurora D}{W:Y.Aurora D}
variable (q: F.NonTangentialFree X)(p: K.NonTangentialFree Y)(h: V.FullBody F)(e: W.FullBody K)
variable (x: Fin n→ S.Union)
include h e
lemma ΘBoxΛL (c:IsOpen U)(t:U.Nonempty)(hv: Set.EqOn (V.emit x ∘ wickSlice n) (W.emit x ∘ wickSlice n) (RibΛL U n)): Set.EqOn (V.emit x) (W.emit x) (tube n) := by
 obtain ⟨a,hp⟩ := ΨΛRibL (n:=n) U c t; let z:= wickSlice n a; have hξ:z∈tube n:= wick_tube (WΛOrderL U hp)
 apply (h.hol n x).eqOn_of_preconnected_of_eventuallyEq (e.hol n x) (ΛStockL n) hξ; have he:= (OΛRibL U c).mem_nhds hp
 apply complex_germ (h.hol n x z hξ) (e.hol n x z hξ) (wick_span n)
 intro m; exact (((show V.emit x ∘ wickSlice n =ᶠ[𝓝 a] W.emit x ∘ wickSlice n from by filter_upwards [he] with p tp; exact hv tp).iteratedFDeriv ℝ m)).eq_of_nhds
include q p
lemma ΘΛEarthL (hv: Set.EqOn (V.emit x) (W.emit x) (tube n)): X.W n x= Y.W n x:=by
 have he(y:Heights n)(v:y∈east n)(j:Points n): F.restricted x y j=K.restricted x y j:=by rw[← h.pure n x j y v,← e.pure n x j y v,hv (roseΛ (etched v) j)]
 ext1 i; haveI:= awaits (light n); exact tendsto_nhds_unique_of_eventuallyEq (q.corner _ x i) (p.corner _ x i) (by filter_upwards [self_mem_nhdsWithin] with k hk; simp_rw [he k hk])
omit q p h e
lemma ΘΛSureL (u:X.W n x=Y.W n x): Set.EqOn (V.emit x) (W.emit x) (tube n):=by
 intro v hv; unfold Surface.Aurora.emit; rw [u, show V.lens n v=W.lens n v from ?_]; ext1 k; rw [V.shape n _ hv,W.shape n _ hv] -- tune
lemma ΘOfferΛL {v:Points n} (hp: readings v∈ sunrise n)(u: Set.EqOn (V.emit x) (W.emit x) (tube n)):{f | Tendsto (V.emit x ∘ wickSlice n) (𝓝[ordered n] v) (𝓝 f)}={f | Tendsto (W.emit x ∘ wickSlice n) (𝓝[ordered n] v) (𝓝 f)}:=by
 ext f; apply tendsto_congr'; filter_upwards [self_mem_nhdsWithin] with y hy; exact u (wick_tube hy)
#print axioms ΘΛEarthL
#print axioms ΘΛSureL
end YM.NSF.Boundary
namespace YM.GaugeFieldConstruction.Ember.Volumetric
open Calibration Raw Cauchy Phys Apit Stage Fathom Function Set Filter Module Empire Hulse Salam Palace
open Floor Carat Dawn Sailing Angles Points Bulb Analysis MeasureTheory Complex Finset
open scoped Topology BigOperators Matrix.Norms.Frobenius ComplexConjugate ContDiff Kronecker InnerProductSpace
attribute [local instance] iG iF iX iU iT2 iW2 iV iS
variable {S:City}{P:Axis→Across}{L:Sheds S P}{C:Supplies L}{u:ℕ→Carat}
namespace FirstPackMars
open Loft Cell NSF.Boundary NSF.Work.C20
attribute [local instance] floatA floatY
attribute [local instance 30000] topx topg
variable {A Z B:CloudsL}(H:SurfCheckL A)(G:SurfCheckL Z)(M:SurfCheckL B)
local notation "Ν_λ"=> SurfRimL A
variable {Y X:NSF.Boundary.Surface (SurfRimL A)}{D:∀ i, Blanket i}{F K:NSF.Boundary.Waves (SurfRimL A)}{N:Y.Aurora D}{E:X.Aurora D}
variable (hz:F.Region (SurfRimL Z))(hu:F.NonTangentialFree Y)(hv:N.FullBody F)
variable (hq: K.Region (SurfRimL B))(ht:K.NonTangentialFree X)(hp:E.FullBody K)
variable {n:ℕ}(V:Fin n→ΧiMars)
local notation "M_ν" => H.TinCanL
variable (U:Set E4)(c:IsOpen U)(t:U.Nonempty)
include G M hz hv hq hp H
lemma ΓDawnΛL (h:X.W n (M_ν∘ V)= Y.W n (M_ν∘ V)) (Astar: ∀ (a:Equiv.Perm (Fin n)), X.W n (M_ν∘ V ∘ a)= Y.W n (M_ν∘ V ∘ a)) : ∀ x∈conf n,B n x V=Z n x V:=by
 intro x y; let a:= PluckΛL x; have e:EastTΛL x a:= pluckRiseΛL x
 have hv':= EastPorousΛL H M hq hp V x a y e (B n x V); have hW:= EastPorousΛL H G hz hv V x a y e (B n x V)
 apply hW.1; apply Tendsto.congr' _ (hv'.2 rfl)
 filter_upwards [self_mem_nhdsWithin] with p u; exact ΘΛSureL (W:=N) (V:=E) _ (Astar a) (wick_tube u)
include U c t hu ht
lemma ΓRibbonΛL (v:∀ n (V:Fin n→ΧiMars)x, x∈RibΛL U n→ B n x V=Z n x V): X=Y:= by
 apply WordsWillΛL; intro b
 have he(n:ℕ)(x:Fin n→ (SurfRimL A).Union): X.W n x=Y.W n x:=by
    let i:= H.TinCanL.symm∘ x; rw [show x=M_ν ∘ i from (funext fun k=> (H.TinCanL.apply_symm_apply (x k)).symm)]
    refine ΘΛEarthL ht hu hp hv _ (ΘBoxΛL U hp hv _ c t ?_) -- tune
    intro y hy; change ΑΛL H (N:=E) i _= ΑΛL H (N:=N) i _; rw[ΥLiveΛL H M hq hp _ (WΛOrderL _ hy), ΥLiveΛL H G hz hv _ (WΛOrderL _ hy)]; exact v n i y hy
 change X.W _ _ _=Y.W _ _ _; rw [he]
#print axioms ΓRibbonΛL
end FirstPackMars
end YM.GaugeFieldConstruction.Ember.Volumetric
end
