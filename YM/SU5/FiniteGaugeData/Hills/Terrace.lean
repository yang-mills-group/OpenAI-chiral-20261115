import YM.SU5.FiniteGaugeData.Hills.Mass
import YM.SU5.FiniteGaugeData.Chrono.Strobel
set_option autoImplicit false
set_option synthInstance.maxSize 24000
noncomputable section
namespace YM.CF.Buffered.Afterglow.Hierarchy
open Function Filter NormedSpace SU Lat Lattice Cube Finset MeasureTheory RG Wilson Metric
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Kronecker Topology ComplexOrder
open Rush Scroll Peaks Stencil Tenant Tap Tulip Branch Fir Scree Advance Reflect Window Laurent Next.Free Bloch Drapes Spire Lifted Skye Sound Precision Tree Push.SectorMeasure Next.SectorChange Common Fock Pastry Satin
open Reed (Fine)
attribute [local instance] opCStarAlgebra
open Heat Nacre Charm Chrono
namespace Hills
-- space tick domain, including possible h-kHierarchy in L.Index matter ratio etc. independent of selected state.Presented properties needed for ergodic component assembly.
abbrev Allows (a j:Axis)(z:ℤ):Prop:= j=a→0≤z
structure Terrace (H:Hilbert)(L:Side)(a:Axis) where
 stepT (s:ℕ)(j:Axis)(z:ℤ)(u:Allows a j z): H.Op
 size_ (s j z u):‖stepT s j z u‖≤1
 ident (s j): stepT s j 0 (fun _=>le_rfl)=1
 via (s j z t v) u p q: z+t=v→stepT s j z u*stepT s j t p= stepT s j v q
 cool (s i j z n w p u): Commute (stepT s i z p) (stepT n j w u)
 repeats (s j z p u): stepT s j z p= stepT (s+1) j (L.val*z) u
namespace Terrace
variable {H:Hilbert}{L:Side}{a:Axis}(P:Terrace H L a)
variable (s t k:ℕ)(j i:Axis)(z:ℤ)
abbrev onceL := P.stepT s j 1 (fun _=>zero_le_one)
local notation "T" s:max j:max=> P.onceL s j
abbrev GalleryH : ℕ→ ClosedSubmodule ℂ H:= fun s=> ⨅ j,domQ (P.onceL s j)
abbrev Unity := ⨅ s, P.GalleryH s
local notation "G" s:max => P.GalleryH s
local notation "P'"=> P.Unity
lemma mem_level (x:H): x∈P.GalleryH s ↔ ∀ j:Axis, P.onceL s j x=x:= ClosedSubmodule.mem_iInf
lemma ascent (q:Allows a j z):P.stepT s j z q=P.stepT (s+1) j (L.val*z) (fun i=>mul_nonneg (by positivity) (q i)):= P.repeats ..
lemma atom_pows : P.stepT s j k (fun _=>Nat.cast_nonneg' _)= (P.onceL s j)^k := by
 induction k with
 | zero=> rw [pow_zero]; exact P.ident s j
 | succ n ih=> rw [pow_succ,←ih]; exact (P.via s j n 1 (n+1:ℕ) _ _ _ (by omega)).symm
lemma mem_anti : Antitone P.GalleryH:= antitone_nat_of_succ_le fun n x p=>by
 rw [P.mem_level] at p ⊢; intro i; unfold onceL; rw [P.ascent, show P.stepT (n+1) i (L.val*(1:ℤ)) _= (T (n+1) i)^(L.val) from ?_]; swap
 · refine Eq.trans (level_of _ ?_) (P.atom_pows ..); rw [mul_one] -- lemma local where
 exact fixed_p (T (n+1) i) x (p i) _
where
 fixed_p(f:H.Op)(x:H)(p:f x=x)(n:ℕ): (f^n) x=x:= by induction n with
                                                                           | zero=> rfl
                                                                           | succ n ih=>rw [pow_succ',mul_apply_eq_comp,ih,p]
 level_of {i:Axis}{z y:ℤ}(f:ℕ){p v}(e:z=y):P.stepT f i z p=P.stepT f i y v:= by subst z; rfl

lemma account {w:H}(p:Allows a j z)(t:w∈domQ (P.onceL s j)): P.stepT s j z p w=w:= by
 cases z with
 | ofNat b=>
    have hx:= (domQ_mem ..).1 t; exact (congrArg (fun f:H.Op=> f w) (P.atom_pows s b j)).trans (mem_anti.fixed_p (T s j) w hx _)
 | negSucc v=>
    let V:= P.stepT s j (Int.negSucc v) p; have h:= (domQ_mem ..).1 t; have hp:= mem_anti.fixed_p (T s j) _ h (v+1)
    have hz: P.stepT s j (v+1:ℕ) (fun _=>Nat.cast_nonneg' _) w=w:=by rw [atom_pows]; exact hp
    have he:= P.via s j (Int.negSucc v) ↑(v+1) 0 p (fun _=>Nat.cast_nonneg' _) (fun _=>le_rfl) (by omega); rw [P.ident] at he
    nth_rw 1 [← hz]; exact DFunLike.congr_fun he w -- maybe.avoid recursive offsets
lemma unityH (x:H): x∈ P.Unity ↔ ∀ s:ℕ,∀ j z u, P.stepT s j z u x=x:=by
 rw [Unity,ClosedSubmodule.mem_iInf]; constructor
 · intro p s j z u; exact P.account s j z u ((domQ_mem ..).2 ((P.mem_level s x).1 (p s) j))
 intro p s; exact ClosedSubmodule.mem_iInf.mpr (fun i=> (domQ_mem ..).2 (p s i 1 (fun _=>zero_le_one)))
lemma retreat : strong (fun s:ℕ=> planeP (P.GalleryH s)) (planeP P.Unity):= descender P.GalleryH P.mem_anti

-- order-independent composition of projections on all four axes. Use list-coded
abbrev bloom (s:ℕ)(j:Axis) := planeP (domQ (P.onceL s j))
abbrev norms' (s j): ‖P.onceL s j‖≤1 := P.size_ ..
lemma bloom_t (p:Allows a j z): Commute (P.bloom s i) (P.stepT k j z p):=equilibrium (P.norms' s i) (P.cool ..)
lemma bloom_c : Commute (P.bloom s i) (P.bloom k j):= dom_commute (P.norms' s i) (P.norms' k j) (P.cool ..)
abbrev pack (s:ℕ):List Axis→ ClosedSubmodule ℂ H
 | []=>⊤
 | j::v=> (domQ (P.onceL s j))⊓ (pack s v)
lemma pack_mem {z:H}(w:List Axis): z∈P.pack s w↔ ∀ i∈ w,z∈ domQ (P.onceL s i):=by induction w with
 | nil=> exact ⟨by simp,fun _=>by rw [pack]; trivial⟩
 | cons i w ih=>rw [pack,ClosedSubmodule.mem_inf,ih]; simp
lemma orchid (w:List Axis): planeP (P.pack s w) = (w.map (P.bloom s)).prod:=by
 induction w with
 | nil=> exact Submodule.starProjection_top'
 | cons i w ih=>
    rw [pack,infP, ih]; rfl
    rw [ih]; apply listProd i w -- where
where listProd i (w:List Axis): Commute (P.bloom s i) (w.map (P.bloom s)).prod:= by induction w with
                                                                                          | nil=> exact Commute.one_right _
                                                                                          | cons i v ih=> exact (P.bloom_c ..).mul_right ih -- args v
lemma siding (w:List Axis)(x:∀ i:Axis,i∈ w): P.pack s w=P.GalleryH s:= SetLike.ext (fun k=> by
 rw [P.pack_mem s]; exact ⟨fun p=>(P.mem_level s k).2 fun i=>(domQ_mem ..).1 (p i (x i)),fun u i _=> (domQ_mem ..).2 ((P.mem_level ..).1 u i)⟩)
abbrev scheduleL : List Axis := [0,1,2,3]
lemma scheduleV (i:Axis): i∈ scheduleL :=by fin_cases i <;> decide
lemma guide : (scheduleL.map (P.bloom s)).prod = planeP (P.GalleryH s):= by rw [← P.orchid, P.siding s _ scheduleV]
lemma bloom_pay (p:Allows a j z): Commute (planeP (P.GalleryH s)) (P.stepT k j z p):=by
 rw [← P.guide]; exact commute_orchard P s k j z p scheduleL
where
 commute_orchard {H:Hilbert}{L:Side}{a:Axis}(P:Terrace H L a)(s k:ℕ)(j:Axis)(z:ℤ)(p:Allows a j z)(w:List Axis): Commute (w.map (P.bloom s)).prod (P.stepT k j z p):= by induction w with | nil=> exact Commute.one_left _ | cons a v ih=> exact (P.bloom_t ..).mul_left ih
lemma unity_c (p:Allows a j z): Commute (planeP P.Unity) (P.stepT s j z p):= by
 apply ContinuousLinearMap.ext; intro x; let T':= P.stepT s j z p
 exact tendsto_nhds_unique_of_eventuallyEq (P.retreat (T' x)) ((T'.continuous.tendsto _).comp (P.retreat x)) (Eventually.of_forall fun k=> DFunLike.congr_fun (P.bloom_pay k s j z p).eq x)
lemma unity_pay (p:Allows a j z): P.stepT s j z p *planeP P.Unity=planeP P.Unity := ContinuousLinearMap.ext fun x=>(P.unityH _).1 (through x) _ _ _ _
lemma flat_pay (p:Allows a j z): planeP P.Unity * P.stepT s j z p=planeP P.Unity:=by rw [(P.unity_c _ _ _ p).eq,P.unity_pay]
lemma dip_step (p:Allows a j z): (dip P.Unity).comp (P.stepT s j z p)=dip P.Unity:=by ext1 x; apply Subtype.ext; exact DFunLike.congr_fun (P.flat_pay ..) x
lemma dip_left (p: Allows a j z): (P.stepT s j z p).comp (cpo P.Unity)=cpo P.Unity:= ContinuousLinearMap.ext fun y=> (P.unityH _).1 (show cpo P.Unity y∈ P.Unity from among y) ..
-- extended representations on CoreH.IrBound.
lemma passage_fwd : strong (meanL (fun k:ℕ=>P.stepT s j k (fun _=>Nat.cast_nonneg' _))) (P.bloom s j):= by simp_rw [atom_pows]; exact mean_s _ (P.norms' ..)
lemma passage_bck (t:j≠a): strong (meanL (fun k:ℕ=>P.stepT s j (- (k:ℤ)) (fun i=> (t i).elim))) (P.bloom s j) := by
 let U:=P.stepT s j (-1) (fun i=> (t i).elim); let V(k:ℕ):=P.stepT s j (-(k:ℤ)) (fun i=> (t i).elim); have he(k:ℕ): V k= U^k:=by induction k with
    | zero=> rw [pow_zero]; apply Eq.trans (mem_anti.level_of P s (y:=0) ?_) (P.ident ..); simp -- dependent
    | succ n ih=> rw [pow_succ',← ih]; exact (P.via s j (-1) (-n) (-↑(n+1)) _ _ _ (by omega)).symm -- -n lift
 have hx:domQ U= domQ (P.onceL s j):= by
    apply SetLike.ext; intro x; rw [domQ_mem,domQ_mem]; constructor
    · intro h; have ht:= P.via s j 1 (-1) 0 (fun _=>zero_le_one) (fun i=>(t i).elim) (fun _=>le_rfl) (by omega); rw [P.ident] at ht; nth_rw 1 [←h]; exact DFunLike.congr_fun ht x
    intro h; exact P.account s j (-1) _ ((domQ_mem ..).2 h)
 change strong (meanL V) (P.bloom s j); rw [show V=(fun k=> U^k) from funext he,bloom,←hx]; exact mean_s U (P.size_ ..)
end Terrace
#print axioms Terrace.flat_pay
#print axioms Terrace.passage_bck
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
variable (a j:Axis)(R:Universal Y h u v I E)(L:Rolled Y h u v J P)(A:Repertory Y h R L a)
include A
lemma tock_next (z:ℤ)(p:Allows a j z)(q:Allows a j (Λ.R.L.val*z)): tock Y h s R L a j A z p=tock Y h (s+1) R L a j A (Λ.R.L.val*z) q:=by
 have hd:∀ q:Allows a j (scaleR Λ s (s+1) z), tock Y h s R L a j A z p=tock Y h (s+1) R L a j A (scaleR Λ s (s+1) z) q:= cohere_clock Y h s (s+1) R L a j A z p (by omega); rw [scale_step s s z (by omega),scale_same] at hd; exact hd q

def StructureH : Terrace A.space Λ.R.L a where
 stepT s j z v:= tock Y h s R L a j A z v
 size_ _ _ _ _:= toll_bound ..
 ident s j:= tock_zero ..
 via s j z t v u p q h:= tock_plus Y _ s R L a j A z u t v p q h
 cool s i j z n w p u:= tock_free Y h s n R L a i A z p j w u -- order binder? defined `(s i)-> R`
 repeats s j z p u:= tock_next ..
lemma goldHill : goldStar Y h R L a A∈ (StructureH Y h a R L A).Unity:= ((StructureH Y h a R L A).unityH _).2 fun s _ _ _=> seed_stay ..
end Hills
end YM.CF.Buffered.Afterglow.Hierarchy
