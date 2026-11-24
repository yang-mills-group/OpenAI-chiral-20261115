import YM.SU5.Reconstruct.Bare
/-!
# The readings factor as insertions for disjoint physical windows

(meaning factorization of the FIELD PRODUCT under resolution, emphatically
not factorization of expectations.) Being able to place stencils on the
cover at any resolution is only a statement about the limit in general. To
get the bare dictionary uniformly up to the UV cutoffs, we instead prove a
metric unwrap estimate along IR, *uniform in* all the physical resolutions
and already for all of the Course's periods above a threshold. Thus even
microscopic representatives of different factors stay observationally
separated. In particular the bare reading of two overlapping multi-scale
polynomials in the algebra still requires its coincidence prescription, but
if they are from **disjoint** physical sets then evaluate the pointwise
product of the actual two at the top.
-/
set_option autoImplicit false
set_option synthInstance.maxSize 30000
set_option maxRecDepth 6000
set_option maxHeartbeats 270000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.Reconstruction
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Heat Fock Analysis SlabMark Vacancy SatinVerification
open Tapestry Tapestry.Altitude PhaseChoice
variable {Λ:Preparation}{l:ℕ}(Y:Course Λ (VolumeCape.Dream.Nimbus l))(H:Real.exp 1≤Λ.x)
local notation "K" => tent Y H
section unwrap
-- no descent of dists purchased merely at a fixed s
lemma modulus_exact (i j:ℕ) : ((More (side Y i j)).val : ℝ) = 4 * Λ.block.val*(Y.ir i).val * Tapestry.precisionAt Λ j := by
  unfold side Preparation.Ctor cell CSide More Vale.mesh Tapestry.precisionAt
  push_cast; ring

def GrowsPast (i:ℕ)(C:ℝ): Prop:= 8*C<4*(Λ.block.val:ℝ)*(Y.ir i).val
lemma wide_calendar (C:ℝ): ∀ᶠ i:ℕ in atTop, GrowsPast Y i C := by
  have he:0 < (Λ.block.val:ℝ):= by positivity
  exact ((tendsto_natCast_atTop_atTop.comp Y.ir_grows.tendsto_atTop).const_mul_atTop (show 0<4*(Λ.block.val:ℝ) by positivity)).eventually (eventually_gt_atTop _)

private lemma pointEstimate {s:ℕ}{C:ℝ}{z:Cover}
    (p:location Λ s z ∈ Tapestry.cabin C) (j:Axis): |(z j:ℝ)| ≤ 2*C*Tapestry.precisionAt Λ s := by
  have h:= p j
  change |((z j:ℝ)/Tapestry.precisionAt Λ s)/2| ≤ C at h
  rw [abs_div,abs_of_pos (show (0:ℝ)<2 by norm_num),abs_div,abs_of_pos (positiveScale Λ s),div_le_iff₀ (show (0:ℝ)<2 by norm_num),div_le_iff₀ (positiveScale Λ s)] at h
  linarith only [h]

lemma unwrap (i:ℕ)(C:ℝ)(p:GrowsPast Y i C) :
    ∀ j:ℕ, ∀ S:Finset Cover, (∀ x∈S,location Λ j x ∈ Tapestry.cabin C)→FullDistances S (side Y i j) := by
  intro j S s a ua b ub
  rw [← map_sub]
  refine lift_eq_iff.mpr ⟨rfl,fun n=>?_⟩
  have hp : 8*C*precisionAt Λ j < ((More (side Y i j)).val : ℝ) := by
    rw [modulus_exact]; exact mul_lt_mul_of_pos_right p (positiveScale Λ j)
  obtain ⟨hx,hy⟩:=abs_le.mp (pointEstimate (s a ua) n)
  obtain ⟨ha,hb⟩:=abs_le.mp (pointEstimate (s b ub) n)
  simp only [Pi.sub_apply]
  have hl : -((More (side Y i j)).val : ℝ) < 2*((b n:ℝ)-a n):=by linarith only [hx,hy,ha,hb,hp]
  have hk : 2*((b n:ℝ)-a n) ≤ ((More (side Y i j)).val:ℝ):=by linarith only [hx,hy,ha,hb,hp]
  exact ⟨by exact_mod_cast hl,by exact_mod_cast hk⟩

lemma unwrapSupported {C:ℝ}{U:Set RSpace}(h:U ⊆ Tapestry.cabin C) :
    ∀ᶠ i:ℕ in atTop, ∀ j:ℕ,∀ S:Finset Cover,SupportedPhysically Λ l j S U → FullDistances S (side Y i j):=
  (wide_calendar Y C).mono fun i p j S v=> unwrap Y i C p j S (fun _ w=> h (v.contains w))

private lemma descended {d:ℕ}{S T:Finset Cover} (s:Side) (p:FullDistances (S∪T) s)
    (h:Tower.separated d S T)(x:Site (More s)) (u:x∈Satin.region S s)(y:Site (More s))(v:y∈Satin.region T s):
    d < separation x y:=by
  obtain ⟨a,w,rfl⟩:= Finset.mem_image.mp u; obtain ⟨b,t,rfl⟩:=Finset.mem_image.mp v
  have he := p b (Finset.mem_union_right _ t) a (Finset.mem_union_left _ w)
  by_contra! g
  apply h a w b t
  have hp(i:Axis): ((a-b) i).natAbs ≤ d := he ▸ ((component_le (_-wrap _ b) i).trans g)
  rw [box_test]; constructor <;> intro i <;> specialize hp i <;> omega
end unwrap

section product
variable {U W: Set RSpace} {C:ℝ}

local notation "keepM" s:max Z:max => keep Λ l s K true (handstamp Z)

lemma togetherAt (i k n:ℕ)(p:GrowsPast Y i C) (hU:U⊆Tapestry.cabin C)(hW:W⊆Tapestry.cabin C)
    (d:Disjoint U W) (x y:sequenceOf (tent Y H))
    (q:∀ t:ℕ,x t∈ keepM t U)(r:∀ t:ℕ, y t ∈ keepM t W) (v:Pay Y n i k) :
    let D:=tidalDressing Y H i k; D.finish n (x*y) = D.finish n x * D.finish n y := by
  intro D
  induction n with
  | zero=> exact map_mul (roving Y H 0 i) _ _
  | succ s ih=>
    rw [Decking.finish,Decking.finish,Decking.finish,ih ⟨v.1,Nat.le_of_lt v.2⟩, Pi.mul_apply]
    have h: D.surge s (D.finish s x * D.finish s y)= D.surge s (D.finish s x)*D.surge s (D.finish s y):= by
       obtain ⟨S,u,e⟩:= finish_location Y H s x q; obtain ⟨T,v',g⟩:=finish_location Y H s y r
       have hp:= separatedPhys (show printedHere Λ l s S (handstamp U) from u) v' (Disjoint.preimage _ d)
       have hE: FullDistances (S∪T) _ := unwrap Y i C p s _ (fun z t=> (Finset.mem_union.mp t).elim (fun t=>hU (u.contains t)) (fun t=>hW (v'.contains t)))
       let X:= D.finish s x; let Y':= D.finish s y
       apply attireL_inj
       change attire (music Y s i k (X * Y'))=attire (music Y s i k X*music Y s i k Y')
       simp_rw [attire_mul,music,flowing,attire_mul] -- repeat
       exact Tapestry.ascendSep Y _ _ _ v (e _ k ⟨v.1,Nat.le_of_lt v.2⟩) (g _ k ⟨v.1,Nat.le_of_lt v.2⟩) (descended _ hE (hp.act Λ l))
    rw [h]
    rw [map_mul]; ac_rfl

lemma pair_breathing (i k n:ℕ) (p:GrowsPast Y i C)(hU:U⊆Tapestry.cabin C)(hW:W⊆Tapestry.cabin C)
    (d:Disjoint U W)(a b:Set ℕ){x y: Altitude.Cloud (Dome K)}
    (hx:x∈jetty Λ l K true (handstamp U) (a∩ Set.Iic n))
    (hy:y∈jetty Λ l K true (handstamp W) (b∩ Set.Iic n)) (v:Pay Y n i k) :
    breathing Y H n i k (x*y) = breathing Y H n i k x * breathing Y H n i k y:=by
  let A:=a∩ Set.Iic n; let B:=b∩ Set.Iic n
  let Kp:=breathing Y H n i k
  apply boarded (P:={f| Officer A (fun i=> keep Λ l i K true (handstamp U)) f})
    (M:=fun x=> Kp (x*y)= Kp x*Kp y) ?_ ?_ ?_ ?_ hx
  · intro f (h:Officer A _ f)
    apply boarded (P:={g| Officer B (fun i=> keep Λ l i K true (handstamp W)) g})
      (M:=fun y=> Kp ((pureShot K f)*y)=Kp (pureShot K f)*Kp y) ?_ ?_ ?_ ?_ hy
    · intro g (w: Officer B _ g); have he:=h.visible A _ Set.inter_subset_right; have h₁:= w.visible B _ Set.inter_subset_right
      unfold pureShot Kp breathing; rw [PiTensorProduct.tprod_mul_tprod, Decking.reckon_paid _ _ _ he, Decking.reckon_paid _ _ _ h₁, Decking.reckon_paid _ _ _ (he.together h₁)]
      exact togetherAt Y H i k n p hU hW d f g h.observes w.observes v
    · simp only [mul_zero,map_zero]
    · intro x' y' _ _ u w; rw [mul_add,map_add,map_add,mul_add,u,w]
    intro z u _ w; rw [Algebra.mul_smul_comm,map_smul,map_smul,Algebra.mul_smul_comm,w]
  · simp only [zero_mul,map_zero]
  · intro p q _ _ u w; rw [add_mul,map_add,map_add,add_mul,u,w]
  intro z u _ w; rw [Algebra.smul_mul_assoc,map_smul,map_smul,Algebra.smul_mul_assoc,w]

lemma pairAtCutoff (i k n:ℕ) (p:GrowsPast Y i C)(hU:U⊆Tapestry.cabin C)(hW:W⊆Tapestry.cabin C)
    (d:Disjoint U W)(a b:Set ℕ){x y: Altitude.Cloud (Dome K)}
    (hx:x∈jetty Λ l K true (handstamp U) (a∩ Set.Iic n))
    (hy:y∈jetty Λ l K true (handstamp W) (b∩ Set.Iic n)) (v:Pay Y n i k) :
    atCutoff Y H i k (x*y)=atCutoff Y H i k x * atCutoff Y H i k y := by
  unfold atCutoff
  rw [pair_breathing Y H i k _ p hU hW d a b (tallerJets Y H n hx v.2) (tallerJets Y H n hy v.2) ⟨v.1,le_rfl⟩,attire_mul]; rfl
end product
end YM.CF.Buffered.Afterglow.Tower.Reconstruction
