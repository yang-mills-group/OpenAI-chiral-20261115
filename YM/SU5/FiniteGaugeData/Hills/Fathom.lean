import YM.SU5.FiniteGaugeData.Hills.Motion
import YM.SU5.FiniteGaugeData.Hills.Sync
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
open Nacre Heat Charm Chrono SalonG Journey
namespace Hills
variable (a b:Axis)(d:ℕ)
section
variable (K:Calibration)(Δ:Axis ×ℕ→ StampK)(L:List (Axis×ℕ))(x y:W K) (s:ℤ)
-- equality of the actual word rather than its afterglow in the two time towers
lemma shearK (j:Axis): clockW K j s (disperse K Δ L x) = disperse K Δ L (clockW K j s x):= (disperse_comm K Δ L x (j,s)).symm
abbrev wander2 := clockW K a s (disperse K Δ L x)
lemma clock_union : Swing K a d x (disperse K Δ L (clockW K b d y))= Swing K b d x (disperse K Δ L (clockW K a d y)):=by unfold Swing; rw [shearK K Δ,shearK K Δ,clock_cross]
abbrev hopDeck (s':ℤ): W K := clockW K b s' (clockW K a s (disperse K Δ L x))
lemma clock_opposite : hopDeck a b K (StampK.neg ∘ Δ) L (Swing K a d x (disperse K Δ L (clockW K b (-(d:ℤ)) y))) (-(d:ℤ)) d= Swing K b d y (disperse K (StampK.neg ∘ Δ) L (clockW K a (-(d:ℤ)) x)) := by
 let Δ':= StampK.neg ∘ Δ; unfold hopDeck Swing; rw [disperse_mul]; simp_rw [clock_mul]; rw [shearK K Δ' L x (-(d:ℤ)) a, ←shearK K (StampK.neg ∘ Δ) L (disperse K Δ L _) (d:ℤ) a, clock_add, neg_add_cancel, tic_zero, disperse_inv, clock_add, add_neg_cancel,tic_zero,commW] -- choose occ using Clock Cancel
#print axioms clock_opposite
end
variable {u v:ℕ→ℕ}{I:ℕ→Family (tent Y h)→ℕ→ℂ}{E:ℕ→ Family (tent Y h)→ℂ}{P:Call Λ l}{J:Wicket Λ l}
variable (W':Universal Y h u v I E)(R:Rolled Y h u v J P)
variable (A:Repertory Y h W' R a)(B:Repertory Y h W' R b)(p:a≠b)
local notation "Tz"=> StructureH Y h a W' R A
local notation "Zb"=> StructureH Y h b W' R B
local notation "Va"=> (StructureH Y h a W' R A).Unity
local notation "Vb"=> (StructureH Y h b W' R B).Unity
local notation "G"=> Camera Y h b W' R B
abbrev Pears (x: (Camera Y h a W' R A).Op)(y:(Camera Y h b W' R B).Op): Prop:=∃ (s:ℕ)(f:W (tent Y h)),x=route Y h s a W' R A f∧ y=route Y h s b W' R B f
local notation "T"=>Pears Y h a b W' R A B
variable {x y x' y':W (tent Y h)}
private lemma in_gallery {H:Hilbert}{L:Side}{a:Axis}(P:Terrace H L a)(s:ℕ)(i:Axis)(z:ℤ)(p:Allows a i z) : planeP (P.GalleryH s) * P.stepT s i z p= planeP (P.GalleryH s):=by
 rw [(P.bloom_pay ..).eq]; apply ContinuousLinearMap.ext; intro x; exact P.account s i z p ((domQ_mem ..).mpr ((P.mem_level s _).1 (through x) i))

variable (f:Plan Y h a d x)(g:Plan Y h a d y)
 (f':Plan Y h b d x')(g':Plan Y h b d y')(e:0 < d)
local notation "W" x:max=> Wedge Y h s a d W' R A x e
local notation "M" x:max=> Wedge Y h s b d W' R B x e
local notation "Wg"=> Charm.W Kₜ
include f g f' g' e A B p
-- every Pair in both products backed by lists.Motion.
lemma plotMean (Δ Δ':Axis×ℕ→StampK)(u v:ℤ)
    (c₁:∀ i,Allows a (Δ i).1 (Δ i).2)(c₂:∀ i,Allows b (Δ' i).1 (Δ' i).2) (t:Allows a b u)(v':Allows b a v)
    (he:∀ i:Axis,strong (meanL (fun k:ℕ=> passingH Y h s a W' R A Δ c₁ (i,k))) ((StructureH Y h a W' R A).bloom s i))
    (hz:∀ i:Axis,strong (meanL (fun k:ℕ=> passingH Y h s b W' R B Δ' c₂ (i,k))) ((StructureH Y h b W' R B).bloom s i))
    (F₁:∀ L:List (Axis ×ℕ),route Y h s b W' R B (Swing Kₜ a d x (disperse Kₜ Δ L (clockW Kₜ b u y)))= route Y h s b W' R B (Swing Kₜ b d x' (disperse Kₜ Δ' L (clockW Kₜ a v y')))) :
    Sync (T) (social (Va) ((W f)*planeP ((Tz).GalleryH s)*(W g))) (social (Vb) ((M f')*planeP ((Zb).GalleryH s)*(M g'))) := by
 let U:= passingH Y h s a W' R A Δ c₁; let V:= passingH Y h s b W' R B Δ' c₂; let S:=Terrace.scheduleL; let R':=tock Y h s W' R a b A u t; let Y':=tock Y h s W' R b a B v v';
 have h₀:= Sync.group (p:=T) (curry U) (curry V) ((Tz).bloom s) ((Zb).bloom s) S (W f) (R'*(W g)) (M f') (Y'*(M g')) he hz (fun L _=>?_)
 · rw [((Tz).guide s), ((Zb).guide s), ←mul_assoc _ R', ←mul_assoc _ Y',mul_assoc _ _ R',mul_assoc _ _ Y',show planeP ((Tz).GalleryH s)*R'=_ from in_gallery (Tz) s b u t,show planeP ((Zb).GalleryH s)*Y'=_ from in_gallery (Zb) s a v v'] at h₀; exact h₀
 let Z:= Swing Kₜ a d x (disperse Kₜ Δ L (clockW Kₜ b u y)); let X':= Swing Kₜ b d x' (disperse Kₜ Δ' L (clockW Kₜ a v y'))
 apply Sync.joint; use s,Z; constructor
 · rw [← mul_assoc (_ * _) R' _]; exact (flashR Y h s a b u d d W' R A f e Δ L c₁ t (Ne.symm p) g e).symm -- defeq conveying
 rw [← mul_assoc (_ * _) Y' _]; exact ((flashR Y h s b a v d d W' R B f' e Δ' L c₂ v' p g' e).symm.trans (F₁ L).symm)
#print axioms plotMean
omit f' g'
private abbrev affirm (x:Axis×ℕ): StampK := (x.1,(x.2:ℤ))
omit e p A B f g in
private lemma permitAny (i:Axis×ℕ):Allows a (affirm i).1 (affirm i).2:=fun _=>Nat.cast_nonneg' _
lemma happy (Fa:Plan Y h b d x)(Fb:Plan Y h b d y):
    Sync (T) (social (Va) ((W f)*planeP ((Tz).GalleryH s)*(W g))) (social (Vb) ((M Fa)*planeP ((Zb).GalleryH s)*(M Fb))) := plotMean Y h s a b d W' R A B p f g Fa Fb e affirm affirm d d (permitAny a) (permitAny b) (fun _=>Nat.cast_nonneg' _) (fun _=>Nat.cast_nonneg' _) (fun i=> (Tz).passage_fwd s i) (fun i=> (Zb).passage_fwd s i) (fun L=>congrArg (route Y h s b W' R B) (clock_union ..))
section reverse
omit A B f g e
private abbrev stripe (x:Axis×ℕ): StampK:= (x.1,if x.1=b then -(x.2:ℤ) else (x.2:ℤ))
private lemma allowedA (x:Axis×ℕ):Allows a (stripe b x).1 (stripe b x).2 := by rintro t; change 0 ≤ if _=b then _ else _; change x.1=a at t; rw [if_neg]; exact Nat.cast_nonneg' _; rw [t]; exact p
omit p in
private lemma allowedB (x:Axis×ℕ): Allows b ((stripe b x).neg).1 ((stripe b x).neg).2 := by rintro t; change 0 ≤ -(if _=b then _ else _); change x.1=b at t; rw [if_pos t,neg_neg]; exact Nat.cast_nonneg' _
omit p in
private lemma castT {H:Hilbert}{L:Side}{a:Axis}(P:Terrace H L a)(s:ℕ){i j:Axis}{u v:ℤ}(X:i=j)(Q:u=v){p w}: P.stepT s i u p=P.stepT s j v w:=by subst j v; rfl
include A in
private lemma passageA (i:Axis) : strong (meanL (fun k:ℕ=> passingH Y h s a W' R A (stripe b) (allowedA a b p) (i,k))) ((Tz).bloom s i):= by
 let F:= fun k:ℕ=> passingH Y h s a W' R A (stripe b) (allowedA a b p) (i,k); change strong (meanL F) _
 by_cases e:i=b
 · have hx:i≠ a:=fun V=>p (V ▸ e); have he:F=(fun k:ℕ=> (Tz).stepT s i (-(k:ℤ)) (fun j=> (hx j).elim)):=funext (fun k=> castT (Tz) s (i:=(stripe b (i,k)).1) (u:=(stripe b (i,k)).2) rfl (by change (if i=b then _ else _)=_; rw [if_pos e])); rw [he]; exact (Tz).passage_bck s _ hx
 have he:F=(fun k:ℕ=> (Tz).stepT s i (k:ℤ) (fun _=>Nat.cast_nonneg' _)):=funext (fun k=> castT (Tz) s (i:=(stripe b (i,k)).1) (u:=(stripe b (i,k)).2) rfl (by change (if i=b then _ else _)=_; rw [if_neg e])); rw [he]; exact (Tz).passage_fwd s i
include B
omit p in
private lemma passageB (i:Axis) : strong (meanL (fun k:ℕ=> passingH Y h s b W' R B (StampK.neg ∘ stripe b) (allowedB b) (i,k))) ((Zb).bloom s i):= by
 let F':= fun k:ℕ=> passingH Y h s b W' R B (StampK.neg ∘ stripe b) (allowedB b) (i,k); change strong (meanL F') _
 let v(i':Axis)(k:ℕ):ℤ:= - (stripe b (i',k)).2
 by_cases e:i=b
 · have he:F'=(fun k:ℕ=>(Zb).stepT s i (k:ℤ) (fun _=> Nat.cast_nonneg' _)):=funext (fun k=>castT (Zb) s (i:=i) (u:=v i k) rfl (by change -(if i=b then _ else _) =_;rw [if_pos e,neg_neg])); rw [he]; exact (Zb).passage_fwd s i
 have he:F'=(fun k:ℕ=> (Zb).stepT s i (-(k:ℤ)) (fun j=> (e j).elim)):=funext (fun k=>castT (Zb) s (i:=i) (u:=v i k) rfl (by change -(if i=b then _ else _) =_; rw [if_neg e])); rw [he]; exact (Zb).passage_bck s _ e
end reverse
lemma reversal (Fa:Plan Y h b d x)(Fb:Plan Y h b d y):
    Sync (T) (social (Va) ((W f)*planeP ((Tz).GalleryH s)*(W g))) (social (Vb) ((M Fb)*planeP ((Zb).GalleryH s)*(M Fa))) := by
 apply plotMean Y h s a b d W' R A B p f g Fb Fa e (stripe b) (StampK.neg ∘ stripe b) (-(d:ℤ)) (-(d:ℤ)) (allowedA a b p) (allowedB b) (fun i=>(p i.symm).elim) (fun i=>(p i).elim) (passageA Y h s a b W' R A p) (passageB Y h s b W' R B)
 intro L; rw [← clock_opposite a b ..]; unfold hopDeck; rw [stayP,stayP,wander]
#print axioms reversal
end Hills
end YM.CF.Buffered.Afterglow.Hierarchy
