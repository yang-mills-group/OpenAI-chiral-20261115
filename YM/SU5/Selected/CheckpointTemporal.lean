import VerifiedSatinGroundInteraction
import YM.SU5.Selected.Edges
import YM.SU5.Selected.Survives
/-!
# Apply pure-sector continuation on the actual law, checkpoint 1

This is the native Euclidean test of `Fixture` (in the correlated
multi-resolution sense). Reconstruction so far for *temporal* operators on the
same correlations with spatial real and rotational restoration NOT supplied.
A few of the conclusions packed here; many ancillary `Acting.*` lemmas on
those operators (power-spectrum support, commutation & continuation, all
in chosen physical units).
-/
set_option autoImplicit false
set_option synthInstance.maxSize 30000
set_option maxRecDepth 6000
set_option maxHeartbeats 600000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.PhaseChoice
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Heat Fock Analysis SlabMark Vacancy SatinVerification
variable {Λ:Preparation}{l:ℕ}(Y:Course Λ (VolumeCape.Dream.Nimbus l))(H:Real.exp 1≤Λ.x)
local notation "K"=>tent Y H
variable {i k:ℕ→ℕ}{I:ℕ→Family (tent Y H)→ℕ→ℂ}{E:ℕ→Family (tent Y H)→ℂ}
  (V:Universal Y H i k I E)
  (G:GroundExtension (i:=i) (k:=k) (E:=E) Y H)
variable (j : Axis) (strict : Bool) (C : Arena Y H G.history.circuit j 0 strict)
local notation "A"=>Ark.Ht Y H G.history.circuit j 0 strict C
local notation "Fₛ" i:max=>Tower.Field Y H i j 0 strict
local notation "κ" s:max=>actor Y H s G.history.circuit j 0 strict C
local notation "ω"=>floorV Y H G.history.circuit j 0 strict C
local notation "Γ"=>Aurora Y H V G.history j strict C
local notation "Ω"=>seat0 Y H V G.history j strict C
local notation "ι₀"=> (Γ).subtypeL
local notation "π"=> (Γ).orthogonalProjectionOnto
local notation "B" s:max f:max h:max=>boxOp Y H V s G.history G.clipped j strict C _ f h
local notation "P" s:max=>cap Y H V s G.history G.clipped j strict C
open Theory Set MeshClock
variable (D:Axis)(room:Arena Y H G.history.circuit D 0 strict) (x:Resident (catalog Y H V G D strict room))
local notation "T"=> bank Y H V G j strict C D room
local notation "S"=> stationC Y H V G j strict C
local notation "O"=> fiberVec Y H V G j strict C D room x
local notation "Φ"=> fiberOp Y H V G j strict C D room x
local notation "L"=> fiberH Y H V G j strict C D room x
local notation "Eχ"=> markE Y H V G strict D room x

lemma fiber_sees : DenseRange fun i=> Φ i O := by
  apply ((T).show_spin x).mono
  rintro _ ⟨i,rfl⟩
  exact ⟨i,(T).show_stamp x i⟩

noncomputable def engaged : Acting Y H V G j strict C where
 space := L
 showL := Φ
 ground := O
 norm1 := Transaction.show_norm T x
 holds u p:= Transaction.show_queue T x u p
 sees:= fiber_sees Y H V G j strict C D room x
local notation "Δ"=>engaged Y H V G j strict C D room x
local notation "γ" s:max a:max=>Acting.voice Y H V G j strict C Δ s a

/-- The entire selected Hilbert space is reconstructed from these marked
E reads (`Acting.densely`, `climbs`, with this equality). All positive
matrices follow. *Candidate v* not the vacuum, `x` here is the resident. -/
theorem engaged_form (s:ℕ) (f g:Fₛ s) (v:observable K strict) (p:v.val=mirror K j 0 f.val * g.val):
    inner ℂ (γ s f) (γ s g)= markE Y H V G strict D room x s v:=by
  obtain ⟨u,⟨X,rfl⟩,h⟩ := ((field_entry Y H j strict s f).and (eventually_gt_atTop (0:ℕ))).exists
  obtain ⟨u',⟨Y₀,rfl⟩,h'⟩:= ((field_entry Y H j strict s g).and (eventually_gt_atTop (0:ℕ))).exists
  rw [Acting.notes Y H V G j strict C Δ s h X,Acting.notes Y H V G j strict C Δ s h' Y₀]
  exact entry_sampling Y H V G j strict C D room x s X h Y₀ h' v p

-- specify the stage timing in writer without claiming momentum vs translations
-- outside mesh, and check common vacuum. supply also unrestricted rank.
namespace Acting
variable (X:Acting Y H V G j strict C)
local notation "Ψ"=> X.clock Y H V G j strict C
local notation "W"=> X.unitaryTime Y H V G j strict C
local notation "U"=> X.lattice Y H V G j strict C
local notation "µ"=> X.pvM Y H V G j strict C
local notation "F"=> X.halfSpaceFunction Y H V G j strict C

structure Permit : Prop where
 density : Dense (citizens Y H V G j strict C X)
 heat_cont (v:X.space): Continuous (fun t=> Ψ t v)
 mink_cont (v:X.space): Continuous (fun t=> W t v)
 mink_unitary (t:ℝ)(v:X.space):‖W t v‖=‖v‖
 mink_law (a b:ℝ): W (a+b) = W a * W b
 origin : W 0=1
 positive_energy(v:X.space): ∀ᵐ t:ℝ ∂(µ v), 0 ≤ t
 represents (v:X.space)(t:ℝ): inner ℂ v (W t v)= ∫ z:ℝ, Complex.exp ((z:ℂ)*(t:ℂ)*Complex.I) ∂(µ v)
 hol : AnalyticOnNhd ℂ F {z:ℂ|0<z.im}
 bridge (t b:ℕ) (a:ℝ) (p:0<b) (v:Fₛ t): let σ:= whenly (timeMesh Λ) t b; let α:= voice Y H V G j strict C X t; F ((a:ℂ)+ (σ:ℝ)*Complex.I) (α v)= W a (α (tick Y H t j 0 strict (2*b) v))
 joins_grid (a:Trans j)(x:marks (timeMesh Λ))(t:ℝ): Commute (W t) (U a x)

lemma permitted : Permit Y H V G j strict C X := by
  refine ⟨Acting.densely Y H V G j strict C X, X.price_every Y H V G j strict C, X.unitary_time_cont Y H V G j strict C,X.norm_time Y H V G j strict C,X.unitary_time_comm Y H V G j strict C,X.unitary_time_zero ..,X.billE_positive Y H V G j strict C,fun v t=>Acting.billE_char Y H V G j strict C X t v, Acting.linker_analytic Y H V G j strict C X,?_,?_⟩ -- syntax tune
  · intro t b a p v σ α; rw [X.linked Y H V G j strict C (t:=σ) (when_pos _ _ _ p)]; exact congrArg (W a) (X.clock_voice Y H V G j strict C t b v)
  exact fun a x t=> X.spacetime_lattice Y H V G j strict C t a x
end Acting

section gate
variable (R : ∀ j:Axis,Arena Y H G.history.circuit j 0 false) (x':Resident (catalog Y H V G D false (R D)))
local notation "Δ" j:max=>engaged Y H V G j false (R j) D (R D) x'
local notation "Ps" j:max s:max=>Acting.voice Y H V G j false (R j) (Δ j) s
local notation "M"=> evaluate Y H V G D R x'
local notation "Z" j:max=> fiberState Y H V G j false (R j) D (R D) x'
local notation "St" j:max=>stationC Y H V G j false (R j)

structure Receipt (s:ℕ)(z:SU.Slot)(q d w:ℕ)(o:Cover)(f:observable K true)(a:ℝ):Prop where
 one_test : Seen Y H V G D R x' s z q d w o f a
 oslo (j:Axis) : Acting.Permit Y H V G j false (R j) (Δ j)
 eform (j:Axis) (s:ℕ)(y v:Tower.Field Y H s j 0 false):
   inner ℂ ((Ps j s) y) ((Ps j s) v) = M s (mirror K j 0 y.val*v.val)
 doesMixture (s:ℕ)(f:observable K false) : (∫ x : Resident (catalog Y H V G D false (R D)), evaluate Y H V G D R x s f.val ∂residents Y H V G false D (R D))=E s f.val
 uses (t:ℕ):∀ᶠ r in atTop, Ferry Y t (i (G.rows r)) (k (G.columns r))
      ∧ ((((Y.voyage (i (G.rows r))).X (Y.uv (k (G.columns r)))).gram 0).beta)= Λ.x

lemma once {s q d w z o f a} (p:Seen Y H V G D R x' s z q d w o f a) : Receipt Y H V G D R x' s z q d w o f a := by
  refine ⟨p,fun j=>Acting.permitted Y H V G j false (R j) (Δ j), ?_, ?_, ?_⟩
  · intro j s y v; let F':= mirror K j 0 y.val*v.val; have hF:TestFamily K true F' := (reflect_ok K j 0 (field_test Y H s j 0 false y)).mul (field_test Y H s j 0 false v); let z':= observe hF
    exact (engaged_form Y H V G j false (R j) D (R D) x' s y v z' rfl).trans (evaluates Y H V G D R x' s z').symm
  · intro s f; simp_rw [evaluates]; exact residents_mean Y H V G false D (R D) s f
  intro t; exact (G.history.finance t).mono fun r v => ⟨v,(coupling_clock Y _ _ v.depth).1⟩

/-- Actual joint election (a witness for any *one* requested slot/center
on this law, phase can depend on that request) with multi-resolution temporal
Hilbert reconstruction checked into `Permit`. Does NOT claim continuum SU(5)
existence & Haag-Kastler conclusions. -/
theorem selected_temporal (ε η:ℝ)(u:0<η)(D:Axis) :
    ∃ (Λ:Preparation)(l:ℕ), ε<Λ.x ∧ Λ.d≤η ∧ Λ.nominated (VolumeCape.Dream.Nimbus l) ∧
      ∃ (H: Real.exp 1≤Λ.x) (Y : Course Λ (VolumeCape.Dream.Nimbus l)) (q d w:ℕ)
        (i k:ℕ→ℕ)(I:ℕ→Family (tent Y H)→ℕ→ℂ) (E:ℕ→Family (tent Y H)→ℂ)
        (V:Universal Y H i k I E) (G:GroundExtension (i:=i) (k:=k) (E:=E) Y H)
        (R:∀j:Axis,Arena Y H G.history.circuit j 0 false),
        ∀ (o:Cover) (z:SU.Slot), ∃ (s:ℕ) (x:Resident (catalog Y H V G D false (R D))) (f:observable (tent Y H) true) (a:ℝ), Receipt Y H V G D R x s z q d w o f a := by
  obtain ⟨Q,l,g,q,b,h,Tt,d,v,w,i,k,x,y,J,W,R,p⟩:= chosen_mixed ε η u D
  exact ⟨Q,l,g,q,b,h,Tt,d,v,w,i,k,x,y,J,W,R,fun z t=>by obtain ⟨s,i,f,a,hv⟩:=p z t; exact ⟨s,i,f,a,once Tt h J W D R i hv⟩⟩
end gate

end YM.CF.Buffered.Afterglow.Tower.PhaseChoice
#print axioms YM.CF.Buffered.Afterglow.Tower.PhaseChoice.engaged
#print axioms YM.CF.Buffered.Afterglow.Tower.PhaseChoice.engaged_form
#print axioms YM.CF.Buffered.Afterglow.Tower.PhaseChoice.selected_temporal
#check @YM.CF.Buffered.Afterglow.Tower.PhaseChoice.selected_temporal
