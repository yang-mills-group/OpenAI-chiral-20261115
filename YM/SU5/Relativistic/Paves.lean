import YM.SU5.Relativistic.Parkway
import YM.SU5.Relativistic.Intervals
import YM.SU5.Relativistic.StreetSign
import YM.SU5.Relativistic.FirGreen
set_option autoImplicit false
set_option synthInstance.maxSize 26000
set_option maxHeartbeats 400000
set_option maxRecDepth 5000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.Reconstruction.FermionSlab
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common Fock
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder NNReal ENNReal Classical InnerProductSpace
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Heat PhaseChoice SlabMark Vacancy Tapestry Tapestry.Altitude Tapestry.Exhibition Tower.Selected
variable {Λ:Preparation}{l:ℕ}(Y:Course Λ (VolumeCape.Dream.Nimbus l))(H:Real.exp 1≤Λ.x)
local notation "K"=>tent Y H
variable {a b:ℕ→ℕ}{I:ℕ→Family (tent Y H)→ℕ→ℂ}{E:ℕ→Family (tent Y H)→ℂ}{L:Rack Λ l}{B:Clay Λ l}
    (D : Exhibition Y H a b I E L B)
local notation "V"=>D.univ_
variable (G:SatinVerification.GroundExtension (i:=a) (k:=b) (E:=E) Y H)
variable (u:ℕ→ℕ) {T:ℕ→Bool→Family (tent Y H)→Family (tent Y H)}(t:GradesAll (i:=a) (a:=G.rows) (k:=b) (b:=G.columns) Y H u T)
variable (d j:Axis) (c:∀ j:Axis,Arena Y H G.history.circuit j 0 false)
variable (x:displayAlgebra Y H D.univ_ G.history G.clipped d false (c d)→⋆ₐ[ℂ] ℂ)
local notation "χ" i:max=> displacement Y H D.univ_ G.history G.clipped d false (c d) x i (c i)
local notation "ψ"=>evaluate Y H D.univ_ G d c (SameCharacter.resident Y H D.univ_ G d false (c d) x)
local notation "D₀"=> Dome (tent Y H)
local notation "Ξ"=> Cloud (Dome (tent Y H))
local notation "φ" n:max => response Y H V n G.history G.clipped j false (c j) (χ j)
local notation "P" s:max F:max=>stream Y H (fun s=>T s true) s F
local notation "Q"=> G.history
variable (s:ℕ)
local notation "α" => walkV Y H j
local notation "F₀"=> Cabin (tent Y H) j
local notation "κ" u:max=>mirror K j u
local notation "Λ₀"=> Λ.R.L.val
local notation "M" n:max=> cargoV Y H D G u t j s n
local notation "B₁" s:max=> creed Y H D G d j c x s

open HostLegal MeshClock
local notation "R₁"=> timeMesh Λ
local notation "U"=>flier Y H D G u t d j c x
lemma unions (Z:Calibration){S:Finset Cover}(a b:Axis){v w:Bool}{F:Family Z}(p:InTest Z v S w F)(x y:ℤ) : relocate Z a x (relocate Z b y F)= relocate Z b y (relocate Z a x F):=by
 unfold relocate; by_cases h:a=b
 · subst b; rw [hoops Z a _ p,hoops Z a _ p,add_comm]
 change chime _ _ _ (mirror Z b _ (mirror Z b _ F))= _; rw [straddle a b h _ _ (axial Z b 0 p),straddle a b h _ _ p]; rfl
-- across directions all stamps, then bill on arrays
variable (A:Trans j)
noncomputable def dwell (q:ℤ): Cabin (tent Y H) j →ₗ[ℂ] Cabin (tent Y H) j where
 toFun f:=by
    refine ⟨relocate K A.val q f.val,?_⟩; obtain ⟨S,h,p⟩:= hutSpec j K f
    refine ⟨plow K A.val q S,flow_port K A.val _ h,fun i u=>?_⟩; obtain ⟨i,h',rfl⟩:=plow_stays K A.val q S u
    rw [moves,if_neg (show j ≠ A.val from Ne.symm A.property)]; exact p _ h'
 map_add' x y:=Subtype.ext (chime_plus ..)
 map_smul' a x:=Subtype.ext (chime_scale ..)
local notation "E₀" k:max=> dwell Y H j k
lemma dwelling (r v:ℤ)(f:F₀): (E₀ A) r ((E₀ A) v f)=(E₀ A) (r+v) f:=by
 obtain ⟨S,h,z⟩:=hutSpec j K f
 apply Subtype.ext; change chime _ _ _ (chime _ _ _ _) = chime _ _ _ _; rw [hoops K _ _ h]; congr 1; unfold gaugeT gaugeShift; ring
lemma nilD (f:F₀): (E₀ A) 0 f=f:=by
 apply Subtype.ext; change chime K _ (gaugeShift Λ.block (2*0)) _=_; rw [show gaugeShift Λ.block (2*0)=0 by simp [gaugeShift]]; exact reversal K _ 0 (hutSpec j K f).choose_spec.1
include D G t
lemma shrines (v:ℤ)(f g:F₀): (B₁ s) ((E₀ A) v f) ((E₀ A) v g)= (B₁ s) f g:=by
 let Θ:= Heat.gaugeShift Λ.block (2*v)
 change ψ s (Complex.I • (mirror K j 0 (chime K A.val Θ f.val) * chime K A.val Θ g.val))= ψ s (Complex.I • (mirror K j 0 f.val*g.val))
 rw [←straddle A.val j A.property _ _ (hutSpec j K f).choose_spec.1, ←chime_product,←chime_scale]; exact elect_slide _ _ _ _ _ _ _ _ ((levied j K f g).scale Complex.I) (2*v) _
lemma feltNorm (v:ℤ) (f:F₀): ‖(U).entry s ((E₀ A) v f)‖= ‖(U).entry s f‖:=by
 have h: (U).F s ((E₀ A) v f) ((E₀ A) v f)= (U).F s f f:=shrines Y H D G u t d j c x s A v f f
 apply pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero |>.mp; rw [←payBasis,←payBasis,h]
lemma feltFine {k:ℕ}(h:s≤k)(v:ℤ) (f:F₀): (U).cl s k ((E₀ A) v f)= (E₀ A) (castor R₁ s k v) ((U).cl s k f):=by
 apply Subtype.ext; let Q':=s
 obtain ⟨S,h,g⟩:=hutSpec j K f; let i:=Heat.gaugeShift Λ.block (2*v)
 change (P s (k-s)) (chime K A.val i f.val)=chime K A.val (Heat.gaugeShift Λ.block (2*castor R₁ s k v)) _
 unfold chime; rw [t.allTurning Y H V Q _ s (k-s) (axial K A.val 0 h), t.allTurning Y H V Q _ s (k-s) h,planeAt,planeAt,mul_zero]; rw [show (Λ₀:ℤ)^(k-s)*i = Heat.gaugeShift Λ.block (2*castor R₁ s k v) from ?_]; rfl
 unfold i Heat.gaugeShift castor; change _= 4*_* (2*((Λ₀:ℤ)^_*_)); ring
noncomputable def lamina (z:ℤ) : Tier.Lamination (flier Y H D G u t d j c x) s where
 mover k:=dwell Y H j A (castor (timeMesh Λ) s k z)
 weak k p f:= (feltNorm Y H D G u t d j c x k A ..).le
 roll k q h v f:=by
    rw [feltFine Y H D G u t d j c x k A v]; rw [show castor R₁ k q (castor R₁ s k z)=castor R₁ s q z by unfold castor; rw [←mul_assoc,←pow_add,show q-k+(k-s)=q-s by omega]]
noncomputable def sendU (v:ℤ):(U).booth.Op:= ((U).choose_ext s (lamina Y H D G u t d j c x s A v)).choose
local notation "σ" s:max p:max=> sendU Y H D G u t d j c x s p
lemma sendsL (v:ℤ){k:ℕ}(h:s≤k)(f:F₀): (σ s A) v ((U).entry k f)= (U).entry k ((E₀ A) (castor R₁ s k v) f):=((U).choose_ext _ _).choose_spec.2 k h f -- parentheses
noncomputable def perroll : Rolls (flier Y H D G u t d j c x).booth where
 wind:=sendU Y H D G u t d j c x s A
 small v:= ((U).choose_ext s (lamina Y H D G u t d j c x s A v)).choose_spec.1
 along i j':=by
    apply Tier.by_front (D:=(U).booth) (U) s; intro k v z
    rw [ContinuousLinearMap.comp_apply,sendsL Y H D G u t d j c x s A _ v,sendsL Y H D G u t d j c x s A _ v,sendsL Y H D G u t d j c x s A _ v,dwelling]; rw [castor]; unfold castor; rw [mul_add]
 nil:=by refine Tier.by_front (D:=(U).booth) (U) s (fun k v x'=>?_); rw [sendsL Y H D G u t d j c x s A _ v,castor,mul_zero,nilD]; rfl
lemma grove {r:ℕ}(R:s≤r)(v:ℤ) : (σ s A) v=(σ r A) (castor R₁ s r v):=by
 apply Tier.by_front (D:=(U).booth) (U) r; intro i p f; rw [sendsL Y H D G u t d j c x s A _ (R.trans p),sendsL Y H D G u t d j c x r A _ p]; unfold castor; rw [←mul_assoc,←pow_add,show i-r+(r-s)=i-s by omega]
lemma alongD (B:Trans j)(v w:ℤ)(r:ℕ): (σ s A) v * (σ r B) w=(σ r B) w*(σ s A) v:=by
 apply Tier.by_front (D:=(U).booth) (U) (max s r); intro k h x'
 obtain ⟨hs,hv⟩:= max_le_iff.mp h; simp only [ContinuousLinearMap.mul_apply]; rw [sendsL Y H D G u t d j c x s A _ hs,sendsL Y H D G u t d j c x r B _ hv,sendsL Y H D G u t d j c x s A _ hs,sendsL Y H D G u t d j c x r B _ hv]; apply congrArg ((U).entry k)
 exact Subtype.ext (unions K _ _ (hutSpec j K x').choose_spec.1 _ _)
lemma acrossH (i r:ℕ)(v:ℤ): (σ s A) v * (hiker Y H D G u t d j c x).fare i r= (hiker Y H D G u t d j c x).fare i r*(σ s A) v:=by
 apply Tier.by_front (D:=(U).booth) (U) (max s i); intro k h x'; obtain ⟨hs,hv⟩:=max_le_iff.mp h
 let X:=hiker Y H D G u t d j c x
 simp only [ContinuousLinearMap.mul_apply]; rw [Ride.rides _ _ _ _ hv,sendsL Y H D G u t d j c x s A _ hs,sendsL Y H D G u t d j c x s A _ hs,Ride.rides _ _ _ _ hv]
 apply congrArg; exact Subtype.ext (unions K _ _ (hutSpec j K x').choose_spec.1 _ _)
local notation "W₀"=>upCycle Y H D G u t d j c x
lemma acrossE (i:ℝ≥0)(v:ℤ) : (σ s A) v*(W₀).E i=(W₀).E i * (σ s A) v:=by
 let U':=(σ s A) v
 ext1 y
 suffices H : (fun i:ℝ≥0=> U' ((W₀).E i y))= fun i:ℝ≥0=> (W₀).E i (U' y) from congrFun H i
 apply (fills R₁).denseRange_val.equalizer (U'.continuous.comp ((W₀).continuousE y)) ((W₀).continuousE _)
 funext b'; obtain ⟨k,q,t'⟩:=MeshClock.split R₁ b'.property; dsimp only [Function.comp_apply]; rw [←t']
 rw [show (W₀).E _ = (hiker Y H D G u t d j c x).fare k q from Ride.reaches ..]
 exact congrArg (fun t:(U).booth.Op=>t y) (acrossH Y H D G u t d j c x s A k q v)
-- extend Γ all later
end YM.CF.Buffered.Afterglow.Tower.Reconstruction.FermionSlab
#print axioms YM.CF.Buffered.Afterglow.Tower.Reconstruction.FermionSlab.acrossE
