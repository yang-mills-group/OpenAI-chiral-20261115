import YM.SU5.Diva.Balm
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
variable {e v:ℝ} {P:Spine}{K:P.Register}{X:Supplier}
private lemma strictLift(p:ℕ→ℕ):∃ f:ℕ→ℕ,p≤f∧StrictMono f:=by
 let f : ℕ→ℕ:= Nat.rec (p 0) (fun i v=>max (p (i+1)) (v+1)); exact ⟨f,fun i=> by cases i; exact le_rfl; exact le_max_left .., strictMono_nat_of_lt_succ (fun i=> show f i < max _ (f i + 1) from (Nat.lt_succ_self _).trans_le (le_max_right ..)) ⟩
lemma building (Λ:Preparation)(l:ℕ)(S:Finset Cover)(b:ℝ)(p:0<b):∀ᶠ s in atTop, printedHere Λ l s S (cabin b):=by
 let f(i:ℕ):= (precisionAt Λ i); have hp: 1<(Λ.R.L.val:ℝ):=by exact_mod_cast (show 1 < Λ.R.L.val by have he:=Λ.V.tallX; omega)
 have he:Tendsto f atTop atTop:= tendsto_pow_atTop_atTop_of_one_lt hp
 let Z:ℝ:=reserve Λ l; refine (Finset.eventually_all ..).2 (fun x hx=>?_)
 filter_upwards [Filter.eventually_all.mpr (fun i:Axis=> (he.atTop_mul_const p).eventually_ge_atTop (Z+ |(x i:ℝ)|))] with s hs y u i
 have h:= u i; have ht: |f s| * |y i| ≤ f s*b:=by rw [← abs_mul]; apply le_trans (b:= Z+|(x i:ℝ)|) _ (hs i); rw [← sub_add_cancel (f s*y i) (x i:ℝ)]; -- tune rw may rewrite RHS
                                                              apply (abs_add_le ..).trans; gcongr
 change |y i|≤ b; rw [abs_of_nonneg (positiveScale Λ s).le] at ht; exact le_of_mul_le_mul_left ht (positiveScale Λ s)
def inchR (Λ:Preparation)(s R:ℕ):ℝ:= 2*(R:ℝ)/precisionAt Λ s
lemma rent_unit(s:ℕ)(V:ℝ)(v:0<V):∀ᶠ i:ℕ in atTop, inchR P.par i s≤V:=by
 let g:=P.par; have hp: 1 < (g.R.L.val:ℝ):= by exact_mod_cast (show 1 < g.R.L.val by have he:=g.V.tallX; omega);
 have he:= tendsto_const_nhds.div_atTop (f:=fun i:ℕ=>2*(s:ℝ)) (tendsto_pow_atTop_atTop_of_one_lt hp); exact he.eventually (ge_mem_nhds v)
variable {w n:ℕ}
lemma birthday (X: Fin w→Twah)(n:Cellz (Fin w))(R s:ℕ)(p:0<R):
    addressG P.par s (nodeC (sitesX X n))= (inchR P.par s R) • (nearPoints R X n).ofLp + addressG P.par s (1:Cover):=by
  ext i; change markZ _ _ _=inchR P.par s R* ((sitesX X n i:ℝ)/(R:ℝ)) + (1:ℤ)/(precisionAt P.par s); rw [nodePrint]; unfold inchR; push_cast; have he:=positiveScale P.par s; have ht:0<(R:ℝ):=by exact_mod_cast p
  field_simp
abbrev warmRay (P:Spine)(s R:ℕ):ℝ≥0:= ⟨inchR P.par s R,by unfold inchR; positivity⟩
variable (P)(c:ℕ→ℕ)(r:ℕ→ℕ)
local notation "η" => Tapestry.cabin
-- geometry: each unit position in germ-scale= r fermion ticks. Windows determined by UV scales before f. Need not assert any continuum rotation on P.
structure Launch : Prop where
 eager : StrictMono r
 smaller : StrictMono c
 unitSize :∀ n,0<r n
 clearing :∀ n, inchR P.par (c n) (r n) ≤ keyV n
 labelSupports :∀ n (L:Parts n (r n)), printedHere P.par P.width (c n) L.sites (cabin (keyV n))
lemma locateFund :∀ n (L:Parts n (r n))(s:ℕ), printedHere P.par P.width s L.sites (cabin (keyV n)) → pinhole P.Test s (P.tuneK L.song)∈well P.par P.calibration P.width false (cabin (keyV n)) Set.univ:=by
 intro n L s V; apply oneSlotWell P.par P.calibration P.width false _ _ _ (Set.mem_univ _); swap; · exact P.celebrity L.song
 exact ⟨_,(Tapestry.locates ..).2 (L.song.1.narrow _),V⟩
def eState (L:Parts n (r n)) (s:ℕ):ℂ:= P.E s (Papal.household P.calibration L.craft)
def readyUV (x:P.Spectrum0 3)(ε:ℕ→ℝ):Prop :=∀ᶠ n in atTop,∀ (k:Axis)(S:Parts n (r n)), ‖P.singleState k (c n) (P.otherSpectrum 3 k x) (P.tuneK S.song) - S.depiction‖≤ε n
abbrev roughUV (ε:ℕ→ℝ):Prop:=∀ n (S:Parts n (r n)), ‖eState P r S (c n)-S.depiction‖≤ ε n
variable {P c r}
variable (H:uniform P K X e v)
include H
/-- arbitrarily increasing r vs precision and with corresponding requested costs. Ask UV height after fixing r, keep ref law. -/
theorem outing (ε:ℕ→ℝ)(p:∀ n,0<ε n)(z:ℕ→ℕ): ∃ (r:ℕ→ℕ), z≤r ∧ ∃ f:ℕ→ℕ,∀ c:ℕ→ℕ, StrictMono c→ f≤ c → Launch P c r ∧ roughUV P c r ε ∧ ∀ᵐ x∂P.pillars 3, readyUV P c r x ε:=by
 let δ(n:ℕ):=ε n/2; have ht(i:ℕ):0<δ i:=half_pos (p i)
 choose s hs using fun n=> eventually_atTop.1 ((aroused n (δ n) (ht n)).and (eventually_gt_atTop 0))
 obtain ⟨r,hR,gR⟩:=strictLift (fun i=>max (s i) (z i)); have hu (i:ℕ):= hs i (r i) ((le_max_left ..).trans (hR i));
 let f(i)(u:Twah.Parts i (r i)):= u.craft
 obtain ⟨p',hp⟩:= exhibitionChance H f _ _ (fun i v=>v.song) (fun i v=> hu i|>.1 v) ht
 choose y hy using fun n=> eventually_atTop.1 ((rent_unit (P:=P) (r n) (keyV n) (keyV_positive n)).and (Filter.eventually_all.mpr fun L:Parts n (r n)=>building P.par P.width L.sites (keyV n) (keyV_positive n)))
 refine ⟨r,fun n=>(le_max_right ..).trans (hR n), fun n=>max (p' n) (y n),fun c h q=>?_⟩;
 have hv (n:ℕ):= hy n (c n) ((le_max_right ..).trans (q n)); obtain ⟨P,hP⟩:= hp c (fun n=> (le_max_left ..).trans (q n)); refine ⟨⟨gR,h,fun i=>(hu i).2,fun n=>(hv n).1,fun i=>(hv i).2⟩,?_,?_⟩
 · intro n S; exact (P n S).trans_eq (add_halves _)
 exact hP.mono fun x p=> p.mono fun i u k z=> (u k z).trans_eq (add_halves _)
omit H
-- apply to arbitrary continuous placement. Even allowing contact set values (use EXACT clause from plateau; not claiming Wightman contact sense).
variable (S:Launch P c r) {α:ℕ→ℝ} {x:P.Spectrum0 3}
include S in
lemma shrank : Tendsto (fun i=> inchR P.par (c i) (r i)) atTop (𝓝 0):=by
  apply squeeze_zero (fun _ => NNReal.coe_nonneg (warmRay ..)) S.clearing keyV_go -- tune include fail
include S
lemma rightRide (f:Fin w→ Lead.Clan)(D:Cellz (Fin w)→ Gaia)(A:ℕ→ Fin w→ Twah)(V:Fin w→DirSpin)(v:∀ᶠ i:ℕ in atTop, bodyF (A i)= V) (p:riseUp A r D) (e: plateau A D) (u:∀ᶠ i in atTop,∀ j, (A i j).traceV.length ≤ 32*((i+2)*r i))
 (hx:readyUV P c r x α)(hA:Tendsto α atTop (𝓝 0))(j:Axis):
 Tendsto (fun i:ℕ=> P.singleState j (c i) (P.otherSpectrum 3 j x) (P.tuneK (lovely (A i) f (Twah.letters w) (r i)))) atTop (𝓝 (Twah.witness f (Twah.letters w) D V)):=by
 let P'(i):= nearPoints (r i) (A i); let g(i):= P.singleState j (c i) (P.otherSpectrum 3 j x) (P.tuneK (lovely (A i) f (Twah.letters w) (r i))); let l:= Twah.letters w; let k(i):= Twah.witness f l (P' i) V
 have he: Tendsto (fun i=> g i-k i) atTop (𝓝 0):= by
    rw [tendsto_zero_iff_norm_tendsto_zero]; apply squeeze_zero' (Eventually.of_forall fun i=> norm_nonneg _) ?_ hA
    filter_upwards [cape_given r D A p e S.eager u,v,hx,eventually_ge_atTop w] with i h v H h'
    let y:Twah.Parts i (r i):=⟨⟨w,by omega⟩,⟨A i,h⟩,f⟩; let d:=y.depiction; unfold k; rw [←v]; exact H j y
 have h:= he.add (witnessFlows f A (Twah.letters w) r D V p e); change Tendsto _ _ (𝓝 (0+Twah.witness f l D V)) at h; rw [zero_add] at h; exact h.congr fun i=> sub_add_cancel _ _
lemma homed {α:ℕ→ℝ} (A:readyUV P c r x α)(h:Tendsto α atTop (𝓝 0))(w:ℕ)(f:Fin w→Lead.Clan) (D:Cellz (Fin w)→ Gaia) (V:Fin w→ DirSpin)(j:Axis):
    Tendsto (fun i:ℕ=> P.singleState j (c i) (P.otherSpectrum 3 j x) (P.tuneK (lovely (fun l=> homestead D (r i) l V) f (Twah.letters w) (r i)))) atTop (𝓝 (Twah.witness f (Twah.letters w) D V)) := by
 let Y(n:ℕ)(l:Fin w):=homestead D (r n) l V; let e:=cottage r D S.eager V
 exact rightRide S f D Y V (Eventually.of_forall (fun i=>rfl)) (riseHome r D S.eager V) (homeHave r D V) (e.mono (fun i p j=>(p.2 j).2.2)) A h j
open Lamour Bridge.Celeste Glimpse Morn Spine.RadiusF
omit S
-- application receipt
/-! A co-trajectory extremal with interaction witness in ALL families & precise UV tangent limits.
    Not all global spacetime symmetries, no claim of S matrix. -/
-- decoration preserve finances; cubic arity grows unbounded
theorem satin_tangent (e v D:ℝ)(X:Supplier)(hx:0<v)(u:0<D)(z:ℕ→ℕ)(A:ℕ→ℝ)(w:∀ i,0<A i): ∃ (P:Spine)(K:P.Register),uniform P K X e v ∧ ∃ (r:ℕ→ℕ), z≤ r ∧
 ∃ (c:ℕ→ℕ), Launch P c r ∧ roughUV P c r A ∧ ∃ (α t:ℝ),0<α∧ 0<t∧t<D ∧ ∃ Y: Glimpse.Voyage P.par.block P.calibration.ℓ 4 α (RadiusF.next P.calibration.ℓ),
     ∀ᶠ i:ℕ in atTop, ∃ x:P.Spectrum0 3, P.party 3 K x ∧ readyUV P c r x A ∧ P.funds i (P.otherSpectrum 3 3 x) Y t ∧
       ∀ z:SU.Slot, P.Intact K i Y.toGaze x z t∧ P.Royal i (P.otherSpectrum 3 3 x) Y (Window.family z) t :=by
 obtain ⟨P,K,T⟩:=installation X e v hx; obtain ⟨r,g,f,R⟩:= outing T A w z; obtain ⟨c,p,h⟩:= strictLift f; obtain ⟨Y,e,F⟩:= R c h p; obtain ⟨α,t,H,v,b,S,Z,U⟩:= violet_simultaneous T u
 refine ⟨P,K,T,r,g,c,Y,e,α,t,H,v,b,S,U.mono fun i G=>?_⟩; obtain ⟨x,f,B,C,L⟩:= G _ F; exact ⟨x,B,f,C,L⟩
end Prototype
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
#check @YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Prototype.outing
#print axioms YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Prototype.outing
#print axioms YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Prototype.locateFund
#print axioms YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Prototype.shrank
#print axioms YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Prototype.birthday
#print axioms YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Prototype.homed
#check @YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Prototype.homed
#check @YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Prototype.satin_tangent
#print axioms YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Prototype.satin_tangent
