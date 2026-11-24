import YM.SU5.FiniteGaugeData.Pannier.Trefl
/-! # Dual volume renewal. Controller on the projection f heights earlier than measured Mark. Geometry proof adapts Afterglow.twice. -/
set_option autoImplicit false
set_option synthInstance.maxSize 24000
noncomputable section
namespace YM.CF.Buffered.Afterglow
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder NNReal
attribute [local instance] opCStarAlgebra

open CF.Pannier.Chancel
variable {N B:Side}{D:ℕ}
namespace Again
private lemma anon_cross (i j:Axis)(e:j ≠ i)(s:ℤ)(x:Seat N) : (plane i s).anon N x j=x j := by
  simp [plane,Shape.anon,affine,Signed.mirror,Signed.act,wrap_here,e,e.symm]

def stepAgain (B:Side) (D:ℕ) := D+4*B.val
def plusAgain (B:Side) (D:ℕ) := 2*stepAgain B D
lemma gap_pos : 0 < stepAgain B D := by unfold stepAgain; have ht : 0<B.val:=B.property; omega
lemma plusAgain_pos : 0 < plusAgain B D := Nat.mul_pos two_pos gap_pos

private lemma alignAgain (b:ℤ):
    ∃ z:ℤ, let s:=Heat.gaugeShift B z; s+D ≤ b ∧ b ≤ s+stepAgain B D := by
  let c:ℤ:=4*B.val
  have hc:0<c:=by unfold c; positivity
  let z:=(b-D)/c
  refine ⟨z,?_⟩; change c*z+D ≤ b ∧ b ≤ c*z+stepAgain B D
  have he:=(Int.emod_add_mul_ediv (b-(D:ℤ)) c)
  have hv:=Int.emod_nonneg (b-(D:ℤ)) hc.ne'
  have h':=Int.emod_lt_of_pos (b-(D:ℤ)) hc
  unfold stepAgain; push_cast; change _ ∧ b ≤ c*z + ((D:ℤ)+c)
  change _ + c*z = _ at he
  omega

/-- Leave room on the other side too. -/
private lemma inhalf {x:Seat N} (i:Axis){d:ℕ}{s b:ℤ}(a:s+D ≤ b)(r:b ≤ s+stepAgain B D)(p:Chord b d (x i)) (h:d+plusAgain B D ≤ (N).val):
    x∈ band N i s D := by
  obtain ⟨y,t,e,q⟩:=p
  let n:=N
  have hz: (D:ℤ) ≤ y-s := by omega
  have hp: y-s+(D:ℤ) ≤ (N).val := by
    unfold plusAgain stepAgain at *; omega
  let Y:=(y-s).toNat
  have hh:Y<(More n).val:=by change _< n.val*2; have w:0<n.val:=n.property; change _≤(n.val:ℤ) at hp; unfold Y; omega
  apply (band_spec ..).mpr
  rw [show x i - (s:Per (More N))=(Y:Per (More n)) from ?_,ZMod.val_natCast_of_lt hh]; swap
  · rw [←Int.cast_natCast,Int.toNat_of_nonneg (by omega),Int.cast_sub,q]
  unfold Y; omega

lemma additional (i:Axis) {d:ℕ} {S:Support (More N)} (a:cows i S d)(h:d+plusAgain B D≤ (N).val) :
    ∃ z:ℤ, let s:=Heat.gaugeShift B z; let T:Support (More N):= S.image ((plane i s).anon N) ∪ S
           S ⊆ band N i s D ∧ cows i T (2*d+plusAgain B D) ∧
           ∀ j:Axis,j≠i → ∀ d', cows j S d' → cows j T d' := by
  obtain ⟨b,a⟩:=a; obtain ⟨z,u,v⟩:=alignAgain (B:=B) (D:=D) b
  let s:=Heat.gaugeShift B z
  change s+D ≤ _ at u; change _≤ s+_ at v
  refine ⟨z,fun x p=>inhalf i u v (a x p) h,⟨2*s-(b+d),?_⟩,?_⟩
  · intro x tx; rcases mem_union.mp tx with E|E
    · obtain ⟨p,t,rfl⟩:= mem_image.mp E; obtain ⟨y,hp,e,q⟩:= a p t
      refine ⟨2*s-y,by omega,by unfold plusAgain; push_cast; omega,?_⟩
      let x:=(plane i s).anon N p
      have ht : x i-(s:Per (More N))=-(p i-(s:Per (More N))) := across_coord i s _
      change ((2*s-y:ℤ):Per (More N)) = x i
      rw [Int.cast_sub,Int.cast_mul,Int.cast_ofNat,q,eq_add_of_sub_eq ht]; ring
    obtain ⟨y,p,v',q⟩:=a _ E; refine ⟨y,by omega,?_,q⟩; unfold plusAgain; push_cast; omega
  intro j hv d' ⟨b,w⟩; refine ⟨b,?_⟩; intro x hx; rcases mem_union.mp hx with y|y
  · obtain ⟨x,hx',rfl⟩:=mem_image.mp y; rw [anon_cross i j hv]; exact w x hx'
  exact w x y

end Again
end YM.CF.Buffered.Afterglow
