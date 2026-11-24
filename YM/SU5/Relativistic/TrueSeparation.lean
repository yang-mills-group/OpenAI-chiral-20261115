import YM.SU5.Relativistic.DiagonalBoundary
/-! # Center/collar real and finite in boundary tomography

As well as using every letter right at price height, can take the genuinely COUPLED
probe along the actual selected-boundary sequence without contact bill: they're
identical to the products below. The outside marks (and preparations) also
indicate genuine nonaliasing through every level used to obtain the trace at cutoff,
even with size changing.
-/
set_option autoImplicit false
set_option maxHeartbeats 430000
set_option maxRecDepth 6000
set_option synthInstance.maxSize 28000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.Reconstruction
open Function NormedSpace Filter Metric Lattice Cube Finset MeasureTheory RG Wilson
open Lat Mir Phase RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Scree Window Vale Girt Lifted
open Py Py.Rate LocalLimit Preparation Satin Heat Fock SlabMark PhaseChoice Push.SectorMeasure
open Tapestry Tapestry.Altitude Tapestry.Exhibition MeshClock
open Tower.Selected Vacancy Journey
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder NNReal ENNReal Classical InnerProductSpace
attribute [local instance] opCStarAlgebra
section generic
lemma wait_grows (Λ:Preparation): Tendsto (fun n:ℕ=> (whenly (timeMesh Λ) 0 n:ℝ)) atTop atTop := by
   let l:= ((mill (timeMesh Λ) 0):ℝ)
   have h:0<l:= mill_pos ..
   have ht: Tendsto (fun n:ℕ=> (n:ℝ)*l) atTop atTop:= Tendsto.atTop_mul_const h tendsto_natCast_atTop_atTop
   apply ht.congr ; intro a; simp [whenly,l]
lemma eventually_sans (Λ:Preparation)(J:Set RSpace) (j:Axis) (k:IsCompact J) :∀ᶠ n:ℕ in atTop,let t:=(whenly (timeMesh Λ) 0 n:ℝ); Disjoint J ({u:RSpace| t≤ u j}∪{u:RSpace| u j≤ -t}):=by
   have hx:= k.image (continuous_apply j : Continuous (fun u:RSpace=> u j))
   obtain ⟨b,h⟩:=hx.bddAbove; obtain ⟨c,g⟩:=hx.bddBelow
   filter_upwards [(wait_grows Λ).eventually (eventually_gt_atTop b),(wait_grows Λ).eventually (eventually_gt_atTop (-c))] with i (r : b < (whenly (timeMesh Λ) 0 i:ℝ)) (z : -c < (whenly (timeMesh Λ) 0 i:ℝ))
   apply Set.disjoint_left.mpr
   intro u y k; rcases k with k'|k'
   · exact r.not_ge (le_trans k' (h (Set.mem_image_of_mem _ y)))
   have ht: c ≤ u j:=g (Set.mem_image_of_mem _ y)
   change u j ≤ -(whenly (timeMesh Λ) 0 i:ℝ) at k'; linarith only [z,ht,k']
lemma potential_union (Λ:Preparation)(l s:ℕ)(S T:Finset Cover): footprint Λ l s (S∪T)=footprint Λ l s S∪footprint Λ l s T:=by rw [footprint,Finset.coe_union, Set.biUnion_union]; rfl
lemma volume_add (Λ:Preparation)(l s n:ℕ)(S:Finset Cover): volumeAround Λ l (s+n) S=volumeAround Λ l n (volumeAround Λ l s S):=by
   induction n with| zero => rfl| succ n ih=> exact congrArg (wingspan Λ l) ih
lemma separated_in_foot (Λ:Preparation)(l s:ℕ)(S T:Finset Cover)(p:Disjoint (footprint Λ l s S) (footprint Λ l s T)) : Detached Λ l S T:= PhaseChoice.separatedPhys (show printedHere Λ l s S (handstamp (footprint Λ l s S)) from has_footprint Λ l s S) (show printedHere Λ l s T (handstamp (footprint Λ l s T)) from has_footprint Λ l s T) (Disjoint.preimage _ p)
end generic
section futureSector
variable {Λ:Preparation}{l:ℕ}(Y:Course Λ (VolumeCape.Dream.Nimbus l))(H:Real.exp 1≤Λ.x)
local notation "K"=>tent Y H
local notation "γ"=> Dome (tent Y H)
local notation "𝒞"=> Cloud (Dome (tent Y H))
variable (j:Axis)
section late_multiplication
local notation "D" i:max k:max s:max z:max=> attire (breathing Y H s i k z)
-- separated checked on actual paid assembly (no convolution modular overlap)
lemma late_product (s i k:ℕ){x:𝒞}{u:γ}{S T:Finset Cover} (v:x∈ shorter γ s)
   (p:AtSupport false (Satin.region S (side Y i s)) (attire (breathing Y H s i k x)))
   (q:u∈bay K T true) (e:Host Y H i s (S∪T))(r:Detached Λ l S T) :
   ∀ n,Tapestry.Pay Y (s+n) i k→
     AtSupport false (Satin.region (volumeAround Λ l n S) (side Y i (s+n))) (D i k (s+n) x) ∧
     AtSupport false (Satin.region (volumeAround Λ l n T) (side Y i (s+n))) (D i k (s+n) (pinhole γ s u)) ∧
     attire (breathing Y H (s+n) i k (x*pinhole γ s u))=(D i k (s+n) x) * D i k (s+n) (pinhole γ s u):=by
    intro n g
    let y:= pinhole γ s u
    have hw:= Host.shrink Y H (S:=T) subset_union_right e
    induction n with
    | zero=>
       have ht: breathing Y H s i k (x*y)=breathing Y H s i k x*breathing Y H s i k y:=by
          unfold y breathing; rw [Decking.outcrop]; exact Decking.last _ _ x s v u
       have he := agrees_at_pin Y H s i k u T q hw 0 g
       refine ⟨p,?_,?_⟩
       · rw [he]
         exact stationed Y H s T i q
       change attire (breathing Y H s i k (x*y)) = _; rw [ht]; exact attire_mul _ _
    | succ n ih=>
      obtain ⟨a,b,c⟩:= ih ⟨g.1,(by have e:=g.2; omega)⟩
      have h:(Tapestry.Pay Y (s+n+1) i k):= g
      have ht:= climbs γ (Nat.le_add_right s n)
      have hx:= ht v; have hy:= ht (short_pinhole s u)
      rw [← Nat.add_assoc]
      rw [ascent_actual Y H (s+n) i k hx,ascent_actual Y H (s+n) i k hy,ascent_actual Y H (s+n) i k ((shorter ..).mul_mem hx hy),c]
      exact ⟨ascendSupport Y (s+n) i k _ h a, ascendSupport Y (s+n) i k _ h b, ascendSep Y (s+n) i k h a b (Host.far Y H r e n)⟩
end late_multiplication
variable {i k:ℕ→ℕ}{I:ℕ→Family (tent Y H)→ℕ→ℂ}{E:ℕ→Family (tent Y H)→ℂ}
    {L:Rack Λ l}{Θ:Clay Λ l}{T:ℕ→ℕ→ Tariff}{t:ℕ→ Tariff}(D : Fashion Y H i k I E L Θ T t)
local notation "D'"=> D.toExhibition
local notation "V"=> D.univ_
variable (G:SatinVerification.GroundExtension (i:=i) (k:=k) (E:=E) Y H)
variable (U : ∀ j:Axis,Arena Y H G.history.circuit j 0 false)(q:Panel Y H D.univ_ G.history G.clipped j false (U j))
variable (x:q.X)
local notation "R"=> SameCharacter.resident Y H V G j false (U j) (q.character x)
local notation "M"=> onDrawing Y H V G D' j U R
variable (c:∀ i,Future Y H j i)
local notation "ϕ" n:max=> Future.boundary Y H j (c n)
variable (m d:ℕ→ℕ)(h:Buys Y H D G j U q x c m d)
local notation "i₀" x:max=> i (m x)
local notation "k₀" x:max=> k (d x)
local notation "μ" x:max=> microscope Y (i (m x)) (k (d x))
local notation "s₀" x:max=> Y.uv (k (d x))
local notation "Δ" x:max s:max=> fun y:𝒞=> attire (breathing Y H s (i (m x)) (k (d x)) y)
local notation "t₀" n:max=> (c n).t
local notation "S₁" n:max=> Future.opening Y H j (c n)
local notation "S₂" n:max=> Future.closing Y H j (c n)
local notation "u₀" n:max=> Future.kernelPast Y H j (c n)
local notation "v₀" n:max=> Future.kernelRoot Y H j (c n)
local notation "γ₀" n:max x:max=> pinhole γ (c n).t x

include h
lemma prepare_each {z : 𝒞}{s:ℕ}(J:BillOfWork)(g:z ∈ fountainHeads K J s): ∀ᶠ n in atTop,
  s ≤ (c n).t ∧
  let S:= volumeAround Λ l ((c n).t-s) (frameBudget J Λ l s)
  let S':= Future.opening Y H j (c n)∪ Future.closing Y H j (c n)
  Disjoint (footprint Λ l (c n).t S') (footprint Λ l s (frameBudget J Λ l s)) ∧
  Host Y H (i (m n)) (c n).t (S∪S') ∧
  ∀ r:ℕ,(c n).t+r≤ Y.uv (k (d n)) → AtSupport false (Satin.region (volumeAround Λ l r S) (side Y (i (m n)) ((c n).t+r))) ((Δ n ((t₀ n)+r)) z) ∧
    AtSupport false (Satin.region (volumeAround Λ l r S') (side Y (i (m n)) ((c n).t+r))) ((Δ n ((t₀ n)+r)) (ϕ n)) ∧
    ((Δ n ((t₀ n)+r)) (z*(ϕ n)))=((Δ n ((t₀ n)+r)) z)*((Δ n ((t₀ n)+r)) (ϕ n)) ∧
    AtSupport false (Satin.region (volumeAround Λ l r (S₂ n)) (side Y (i (m n)) ((c n).t+r))) ((Δ n ((t₀ n)+r)) (γ₀ n (u₀ n))) ∧
    AtSupport false (Satin.region (volumeAround Λ l r (S₁ n)) (side Y (i (m n)) ((c n).t+r))) ((Δ n ((t₀ n)+r)) (γ₀ n (v₀ n))) ∧
    ((Δ n ((t₀ n)+r)) (ϕ n))=((Δ n ((t₀ n)+r)) (γ₀ n (u₀ n)))*((Δ n ((t₀ n)+r)) (γ₀ n (v₀ n))) := by
  obtain ⟨C,p⟩:= issued.mp g
  let X:=frameBudget J Λ l s
  let F:= footprint Λ l s X
  obtain ⟨Q,(t:progressBoard _=_)⟩:= (exists_surjective_nat (Finset Cover × ℕ)).choose_spec (X,s)
  filter_upwards [eventually_ge_atTop Q,eventually_ge_atTop s, (wait_grows Λ).eventually (eventually_gt_atTop 0), eventually_sans Λ F j (footprint_compact Λ l s X)] with n hv k hp k'
  have he : s ≤ t₀ n:= le_trans k (c n).arrival; refine ⟨he,?_⟩
  intro S S'; let K₁:= footprint Λ l (t₀ n) (S₁ n); let K₂ := footprint Λ l (t₀ n) (S₂ n)
  let d₀:= (whenly (timeMesh Λ) 0 n:ℝ); have hd:0<d₀:=hp
  obtain ⟨a,b⟩:= Future.labels_far Y H j (c n)
  have Hx : Disjoint (footprint Λ l (t₀ n) S') F := by
     unfold S'; rw [potential_union]
     exact Disjoint.mono_left (Set.union_subset_union a b) (Disjoint.symm k')
  have hy := h.growsHost n Q hv; rw [t] at hy; have hh: Host Y H (i (m n)) (t₀ n) (S'∪S):= hy
  rw [union_comm] at hh
  have hΥ:Tapestry.Pay Y (t₀ n) (i₀ n) (k₀ n) := h.payHigh n
  refine ⟨Hx,hh,?_⟩; intro r x'
  have hx:Tapestry.Pay Y ((t₀ n)+r) (i₀ n) (k₀ n):= ⟨hΥ.1,x'⟩
  have hi: Detached Λ l S S':= separated_in_foot Λ l _ _ _ (Disjoint.symm (Hx.mono_right (by
      let P:= t₀ n-s; have he' : t₀ n=s+P:=by unfold P; omega
      change footprint Λ l _ (volumeAround Λ l P X) ⊆ _; rw [he']; exact covers_footprint ..)))
  have hz: AtSupport false (Satin.region S (side Y (i₀ n) (t₀ n))) ((Δ n (t₀ n)) z):=by
     let α:= t₀ n-s; have v:t₀ n=s+α:=by unfold α; omega
     change AtSupport false (Satin.region (volumeAround Λ l α X) (side Y _ _)) _
     rw [v]; exact multi_extent Y H s (i₀ n) (k₀ n) p α (v ▸ hΥ)
  have p₁: InTest K true (S₁ n) false (v₀ n).val:= Future.emit_extent Y H j (c n)
  have p₂: InTest K true (S₂ n) false (u₀ n).val:= axial K j 0 (Future.emit_extent Y H j (c n))
  have pp:= late_product Y H (t₀ n) (i₀ n) (k₀ n) (u:=Future.kernelPath Y H j (c n)) (Altitude.climbs γ he p.funded) hz ((p₂.mono (Finset.subset_union_right)).mul (p₁.mono (Finset.subset_union_left))) hh hi r hx
  have v: Detached Λ l (S₂ n) (S₁ n):=by
     apply separated_in_foot Λ l (t₀ n); refine Set.disjoint_left.mpr ?_; intro u h q
     have ht: u j ≤ -d₀:= b h; have hc:d₀ ≤ u j := a q; linarith
  have hc:Host Y H (i₀ n) (t₀ n) (S₂ n ∪ S₁ n):= by rw [Finset.union_comm]; exact h.host n
  have hP:= (show AtSupport false (Satin.region (S₂ n) (side Y (i₀ n) (t₀ n))) ((Δ n (t₀ n)) (γ₀ n (u₀ n))) from by
     have hj:Host Y H (i₀ n) (t₀ n) (S₂ n):= Host.shrink Y H subset_union_left hc
     have hv:= agrees_at_pin Y H (t₀ n) (i₀ n) (k₀ n) (u₀ n) (S₂ n) p₂ hj 0 hΥ
     rw [show t₀ n+0=t₀ n from rfl] at hv
     dsimp only; rw [hv]; exact stationed Y H (t₀ n) (S₂ n) (i₀ n) p₂)
  obtain ⟨u,w,q⟩:= late_product Y H (t₀ n) (i₀ n) (k₀ n) (short_pinhole (t₀ n) (u₀ n)) hP (u:=v₀ n) (S:=S₂ n) p₁ hc v r hx
  exact ⟨pp.1,pp.2.1,pp.2.2,u,w,by rw [(c n).twoEnds Y H j]; exact q⟩

end futureSector
end YM.CF.Buffered.Afterglow.Tower.Reconstruction
#print axioms YM.CF.Buffered.Afterglow.Tower.Reconstruction.prepare_each
