import YM.SU5.Assay.FlashGain
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 4500
set_option maxHeartbeats 500000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Heat Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry

open TopologicalSpace
open CF.Velvet CF.Pannier.Chancel
open Spine TopologicalSpace
namespace Prototype
open Ballad Twah CF.Lamour.Bridge.Celeste Altitude
open YM.Stationary (Gaia)
/-! Uprise pays the outing even along any sufficiently accelerated r. -/
variable {e v:ℝ} {P:Spine}{K:P.Register}{X:Supplier}
lemma outward (H:uniform P K X e v)(ε:ℕ→ℝ)(p:∀ n,0<ε n):∃ z:ℕ→ℕ, ∀r:ℕ→ℕ,z≤r→StrictMono r→ ∃ f:ℕ→ℕ,∀ c:ℕ→ℕ, StrictMono c→ f≤ c → Launch P c r ∧ roughUV P c r ε ∧ ∀ᵐ x∂P.pillars 3, readyUV P c r x ε:=by
 let δ(n:ℕ):=ε n/2; have ht(i:ℕ):0<δ i:=half_pos (p i)
 choose s hs using fun n=> eventually_atTop.1 ((aroused n (δ n) (ht n)).and (eventually_gt_atTop 0))
 refine ⟨s,fun r hR gR=>?_⟩;  have hu (i:ℕ):= hs i (r i) (hR i);
 let f(i)(u:Twah.Parts i (r i)):= u.craft
 obtain ⟨p',hp⟩:= exhibitionChance H f _ _ (fun i v=>v.song) (fun i v=> hu i|>.1 v) ht
 choose y hy using fun n=> eventually_atTop.1 ((rent_unit (P:=P) (r n) (keyV n) (keyV_positive n)).and (Filter.eventually_all.mpr fun L:Parts n (r n)=>building P.par P.width L.sites (keyV n) (keyV_positive n)))
 refine ⟨fun n=>max (p' n) (y n),fun c h q=>?_⟩;
 have hv (n:ℕ):= hy n (c n) ((le_max_right ..).trans (q n)); obtain ⟨P,hP⟩:= hp c (fun n=> (le_max_left ..).trans (q n)); refine ⟨⟨gR,h,fun i=>(hu i).2,fun n=>(hv n).1,fun i=>(hv i).2⟩,?_,?_⟩
 · intro n S; exact (P n S).trans_eq (add_halves _)
 exact hP.mono fun x p=> p.mono fun i u k z=> (u k z).trans_eq (add_halves _)
end Prototype
open Prototype
open Ballad Twah Lamour.Bridge.Celeste
namespace Spine
variable {e v:ℝ} {P:Spine}{K:P.Register}{X:Supplier}
variable {Z:Lead.Clan}

private lemma ardent {s:ℕ→ℕ}{q:ℕ→Prop}(f:∀i:ℕ,∃ n ≥i,q n):
 ∃ r≥s, StrictMono r∧∀i,q (r i):=by
 choose y p t using f
 let r:ℕ→ℕ:= Nat.rec (y (s 0)) (fun n a=>y (max (a+1) (s (n+1))))
 refine ⟨r,fun n=>?_,strictMono_nat_of_lt_succ ?_,fun i=>?_⟩
 · cases n; exact p _; exact (le_max_right ..).trans (p _)
 · exact fun i=>(Nat.lt_succ_self _).trans_le ((le_max_left ..).trans (p _))
 cases i <;> exact t _

/-- All large n support the mass-one convention (*after* purePrice division), up to
 a factor tending to one. No new simultaneity hypothesis on `c` or `r`; for
 instance this permits any old experiment on the Taste-qualified uniform P, if
 its n on the trajectory is taken sufficiently late. -/
lemma Taste.fledged (h:uniform P K X e v) {g:ℕ→ℂ}
 (u:∀n,P.Taste (P.defaultR Z n) (P.flash n).patio (g n)): Tendsto g atTop (𝓝 1):=by
 by_contra H
 simp only [Metric.tendsto_atTop] at H
 push Not at H
 obtain ⟨a,t,f⟩:=H
 obtain ⟨z,e⟩:=Prototype.outward h keyV keyV_positive
 obtain ⟨r,t₀,t₁,t₂⟩:= ardent (s:=z) f
 obtain ⟨s,w⟩:= e r t₀ t₁
 choose m p using fun i=> eventually_atTop.1 (Taste.watch (defaultBay P Z _) (defaultColor P Z _) (u (r i)) 3 _ (half_pos t))
 obtain ⟨c,H,H₁,_⟩:= ardent (s:=fun i=>max (s i) (m i)) (q:=fun _=>True) (fun i=>⟨i,le_rfl,trivial⟩)
 obtain ⟨B,_,x⟩:=w c H₁ fun i=>(le_max_left ..).trans (H i)
 obtain ⟨x,h⟩:=x.exists
 obtain ⟨N,v⟩:=Metric.tendsto_atTop.1 (aboutOne Z B h keyV_go) _ (half_pos t)
 let y:=P.otherSpectrum 3 3 x
 let d:=P.singleState 3 (c N) y (P.defaultR Z (r N))
 have hp:dist d (g (r N))≤a/2:= by rw [dist_eq_norm]; exact p N _ ((le_max_right ..).trans (H N)) y
 exact (not_lt_of_ge (t₂ N)) ((dist_triangle_left _ _ d).trans_lt (by
    linarith only [hp,(v N le_rfl:dist d (1:ℂ)<a/2)]))

variable (P) in
/-- Choice of flash appraisals. -/
def Plume (g:ℕ→Lead.Clan→ℂ):Prop:=∀(n:ℕ)Z,P.Taste (P.defaultR Z n) (P.flash n).patio (g n Z)
variable {g:ℕ→Lead.Clan→ℂ}
lemma Tasting.Paid.quill (p:Tasting.Paid P.par):∃g,P.Plume g:=by
 choose g h using fun n Z=>P.flashTaste Z p n
 exact ⟨g,h⟩
lemma Plume.large (u:P.Plume g)(h:uniform P K X e v):Tendsto g atTop (𝓝 1):=
 tendsto_pi_nhds.mpr fun Z=>Taste.fledged h (fun i=>u i Z)
lemma Plume.letter (u:P.Plume g)(h:uniform P K X e v){a:ℝ}(t:0<a):
 ∀ᶠ n in atTop,P.calibration.ℓ<n ∧∀ Z,g n Z ≠0∧‖g n Z-1‖<a∧‖(g n Z)⁻¹-1‖<a:=by
 refine (eventually_gt_atTop _).and (eventually_all.mpr fun Z=>?_)
 let p:=Taste.fledged h (fun i=>u i Z)
 have w:=p.eventually (isOpen_ne.mem_nhds (one_ne_zero : (1:ℂ)≠0))
 have v:Tendsto (fun i=>(g i Z)⁻¹) atTop (𝓝 1):=by simpa using p.inv₀ one_ne_zero
 simp_rw [←dist_eq_norm]
 exact w.and ((p.eventually (Metric.ball_mem_nhds _ t)).and (v.eventually (Metric.ball_mem_nhds _ t)))
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
