import YM.SU5.FiniteGaugeData.Cirrus.Litany
/-!
# Reeh--Schlieder. No bounded replacement of realized fields.
-/
set_option autoImplicit false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Hierarchy.Seld.Poin.Maison
open Complex Filter Function Set MeasureTheory MeasureTheory.Measure Boundary OS OS.Semigroup Probe
open scoped Topology NNReal InnerProductSpace
variable {H:Hilbert}(S: OS.Semigroup H timeAxis)
variable (F: H.space→L[ℂ]ℂ)(x:Bench S)(Ω:Bench S)(hΩ:∀ p:E4,M S p Ω.val=Ω.val)
variable {ι:Type}(G:Canopy H ι)(t:G.Chip)(w v:List G.Token)
local notation "D"=> Bench S
variable (U:Set E4)(f:Test4)(u:IsOpen U)(d:U.Nonempty)(A: Distn E4)
include u d
open Distribution
lemma everyone (h:∀ f:Test4, OrbitBox U f→ A f=0): A f=0 :=by
 obtain ⟨y,H⟩:= d
 apply ((Distn.general_open A isClosed_dsupport.isOpen_compl).2 disjoint_compl_left)
 intro x p; let r:=y-x; let V:= (fun i:E4=>i+r) ⁻¹' U; apply (notMem_dsupport_iff x).mpr; refine ⟨V,?_,u.preimage (continuous_id.add continuous_const),show x+r∈ U from ?_⟩; swap; · rw [show x+r=y from (by unfold r;abel)]; exact H
 apply (Distn.from_compact A).2; intro f z b; refine h f ⟨-r,ahead r f,⟨support_G _ _ b, fun x p=>?_⟩,?_⟩; obtain ⟨x,e,rfl⟩:= support_F f r p; exact z e
 rw [shuttle,neg_add_cancel,ahead₀]
omit u d
lemma elder : G.desire S (w++v)= (G.desire S w)*(G.desire S v):=by simp [Canopy.desire]
lemma stream (m:ℕ): Continuous (fun f:Test4=> F (hall S m (G.desire S w (G.horizon S (t,f) x)))):=by
 let c:= fun f:Test4=> G.horizon S (t,f) x; have H (m:ℕ)(w:List G.Token): Continuous (fun f=> hall S m (G.desire S w (c f))):=by
    let n:=G.grade t; induction w generalizing m with
    | nil=> change Continuous (fun f=>hall S m (ℑ S (G.dep t) f n x)); simp_rw [graphN]; exact (BroCt S _ (n+m)).clm_apply continuous_const
    | cons a w ih=> let p:= (G.grade a.1); change Continuous (fun f=> hall S m (ℑ S _ _ p _ )); simp_rw [graphN]; exact (brochure S (G.dep a.1) (p+m) a.2).continuous.comp (ih _)
 exact F.continuous.comp (H m w)
def fleetR(m:ℕ) : Distn E4 :=
 { (F.toLinearMap ∘ₗ hall S m ∘ₗ G.desire S w ∘ₗ (LinearMap.applyₗ x).comp (σV S (G.dep t) (G.grade t))) with
     cont:= stream S F x G t w m }
-- Distribution on arbitrary words. No operator algebra/traces assumed yet; purely Wight reconstruction.
variable (X:Boundary.Action H)(e:∀ p:E4,X.orbit.translation p=M S p) (hF:∀ x∈ SampleInR S Ω G U, F x=0)
include u d hΩ e hF
local notation "¥"=> G.Ticket S Ω
lemma with_all (p:∀ t∈w,OrbitBox U t.2) : F (¥ (w++v))=0:=by
 induction v generalizing w with
 | nil=> rw [List.append_nil]; exact folk_B S F Ω hΩ G w U u X e hF p
 | cons a v ih=>
    let A:= fleetR S F (G.bud S Ω v) G a.1 w 0
    have he(f:Test4) : A f= F (¥ (w++(a.1,f)::v)):=by unfold Canopy.Ticket Canopy.bud; rw [elder]; change F (hall S 0 _) =_; rw [home]; rfl
    rw [← he]; apply everyone U a.2 u d A; intro f h; rw [he,show w++(a.1,f)::v=w++[(a.1,f)]++v from by simp]
    refine ih _ ?_; intro t e; exact (List.mem_append.mp e).elim (p t) (fun i=>(List.mem_singleton.mp i) ▸ h)
omit hF
open Submodule
-- usual condition: ℋ-completion of the canopy.
abbrev LocalSeed(U:Set E4): Submodule ℂ H.space:= span ℂ (SampleInR S Ω G U)
theorem breeds : (LocalSeed S Ω G U).topologicalClosure= G.Climb S Ω:=by
 let f:= G.Ticket S Ω
 rw [Canopy.Climb,Canopy.models]
 apply le_antisymm (topologicalClosure_mono ?_) _
 · apply span_mono; rintro _ ⟨x,⟨w,u,rfl⟩,rfl⟩; exact ⟨w,rfl⟩
 rw [← orthogonal_orthogonal_eq_closure, ← orthogonal_orthogonal_eq_closure]
 apply orthogonal_le; intro x p
 let A:= innerSL ℂ x
 have H:∀ y∈ SampleInR S Ω G U,A y=0:=fun y v=> inner_left_of_mem_orthogonal (subset_span v) p
 have he: (span ℂ (Set.range f)) ≤ (A.ker) := by
    apply span_le.mpr; rintro _ ⟨w,rfl⟩; exact with_all S A Ω hΩ G [] w U u d X e H (by simp)
 apply (mem_orthogonal' _ _).mpr; exact fun y=>fun e=> he e
#print axioms everyone
#print axioms breeds
end YM.CF.Buffered.Afterglow.Hierarchy.Seld.Poin.Maison
