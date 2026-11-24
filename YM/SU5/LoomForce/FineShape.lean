import YM.SU5.LoomForce.FrameTaylor
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 2000
set_option maxHeartbeats 500000
noncomputable section
namespace YM.CF.LitCurrent.Surplus
open Function Filter Topology NormedSpace Lattice Wilson Fock Pastry Scree Sault Sour
open Stax Skye Jet Scroll Finset Palot Cadre Vow RG Rive Nor Hake MeasureTheory
open Metric Drapes Tulip Lat Branch Cube Tenant
section
open scoped Topology Matrix.Norms.Frobenius Classical
open Rill
private lemma tGerm2 {N:Type} [NormedAddCommGroup N][NormedSpace ℝ N] {A B : N→ SU.group.El}{b:ℝ}{x:N}{k:ℕ}
    (e:Rill.Tender A x b k)(p:A =ᶠ[𝓝 x] B): Rill.Tender B x b k:=
  e.same (p.mono fun _ e'=> congrArg SU.group.mat e')
end
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Topology Classical ContDiff
attribute [local instance] opCStarAlgebra
open Rush SU Prism Nacre Laic Tap Levier Thera Moto Oath Font Haro Spire Dial Rill
open Kennel Swell StressExchange
variable {N:Side}{P T:SOp N}{a b d v g t u:ℝ}{r k:ℕ}
open Next.Rank Spindle
-- stronger application needed to compute the pair expectation without assuming
-- convergence at arbitrary precision rates in Fourier ruler. Use the exponential
-- locality in the kernel receipt, get absolute l1 bound on the Hessian coefficients!
-- Uniform across all probes in those engagements, not assuming bounded count of curvature legs.

abbrev Sheds (B:ℕ) := Spindle.Turn B × group.ColorIndex
abbrev Stern {B:ℕ} (i:Sheds B) := Pi.single (M:=fun _:Turn B=>group.Color) i.1 (EuclideanSpace.single i.2 1)
variable (o:Seat N) (B:ℕ) (h:2*(B+1)< (More N).val)
local notation "Σ" => Turn B
local notation "D" => Dim o B
local notation "Δ" => Finset.card
local notation "J" => install B o ∘L collectF B o h

lemma sternNorm (i:Sheds B): ∀ x, ‖Stern i x‖≤1:=by
 intro x; by_cases p:x=i.1; · simp [Stern,p,PiLp.norm_single]
 simp [Stern,p]

section shed
variable {Ω:Sa N}{i j:Single N} (T:StageTree N d (4*a) v)
-- leak-block adjacency o. Each link uses a `word` whose *used faces count*,
-- not just position, fits the hull-size of its own stencil contribution here.
include h
lemma local_card (T:Sa N)(x:Dim o B)(k:ℕ)(g:T.card=k)(v: separation o x.val.1 ≤ T.card) : (word group h x).length ≤ 4*k:=by
 refine le_trans (Classical.choose_spec (rolled group _ _ (register h x).property.1 (register h x).property.2)).1 (bounded (R:=k) ?_)
 change lift (x.val.1 - o)∈ box k
 exact Work.E08.lift_mem_box (g ▸ v)

noncomputable def cages (X:Sa N) := ((univ:Finset (Dim o B)).filter (fun y=>y.val∈leaks X))
noncomputable def contact (X:Sa N)(i:Sheds B):Prop:= ∃ e∈cages o B X,i.1∈ ((word group h e).map Prod.fst).toFinset
omit h in
lemma cages_card (X:Sa N) : (cages o B X).card ≤ X.card*4:=by
 calc
  _ ≤ ((cages o B X).image Subtype.val).card:=(card_image_of_injective (cages ..) Subtype.val_injective).symm.le
  _ ≤ (X ×ˢ (univ:Finset Axis)).card:=card_le_card (fun y p=>?_)
  _ ≤ _:=by simp [Axis]
 obtain ⟨x,a,rfl⟩:=mem_image.mp p; exact mem_product.mpr ⟨(mem_filter.mp (mem_filter.mp a).2).2.1,mem_univ _⟩

variable (g0:0<a) (X:Sa N) (hv:T.W Ω i j≠0) (K:HopeT d b g 3)
variable (hh:∀ Y:Seat N,Y∈X→separation o Y≤X.card)
include hh
lemma touched_cage : ∑ l∈cages o B X,(word group h l).length ≤ Δ (cages o B X)*(4*Δ X) := by
 have he(e:Dim o B)(hu:e∈ cages o B X) : (word group h e).length≤4*X.card:=local_card o B h X e X.card rfl (hh e.val.1 (mem_filter.mp (mem_filter.mp hu).2|>.2.1))
 exact (sum_le_sum (s:=cages o B X) he).trans (by simp)

lemma flagged_card : (Δ ((univ:Finset (Sheds B)).filter (contact o B h X)):ℝ) ≤ (4*X.card)^2*Fintype.card group.ColorIndex:=by
 let u:= fun e:Dim o B=> ((word group h e).map Prod.fst).toFinset; let v:= cages o B X
 let T:=(univ: Finset (Sheds B)).filter (contact o B h X)
 refine le_trans (a:=(Δ T:ℝ)) (Nat.cast_le.mpr (card_le_card (show T⊆ v.biUnion u ×ˢ univ from ?_))) ?_
 · intro i p; obtain ⟨e,a,b⟩:= (show contact o B h X i from (mem_filter.mp p).2); exact mem_product.mpr ⟨mem_biUnion.mpr ⟨e,a,b⟩, mem_univ _⟩
 have ht:=card_biUnion_le (s:=v) (t:=u)
 have hp(e:Dim o B):Δ (u e) ≤ (word group h e).length:= (List.toFinset_card_le ..).trans (List.length_map ..|>.le)
 rw [card_product,card_univ,Nat.cast_mul]; have hc := le_trans ht (le_trans (sum_le_sum (s:=v) (fun i _=> hp i)) (touched_cage o B h X hh));
 exact mul_le_mul_of_nonneg_right (by norm_cast; rw [pow_two]; exact hc.trans (Nat.mul_le_mul_right _ ((cages_card o B X).trans_eq (mul_comm ..)))) (by positivity)

-- source pieces at true identity profile. can't use wirings on tags with unproved regularity
omit h hh
variable (i j:Single N)
def pieces (U:Pane N):ℂ:= if p: profile U∈Openc (More N) d then T.F X () ⟨profile U,p⟩ i j else 0
local notation "αK" => T.W X i j
local notation "M" => More N
local notation "A"=> tangD N
local notation "Ωp"=> pieces T X i j
local notation "τ"=> increment (1: Pane N)
local notation "Κ"=> Openc (More N) d
local notation "L"=> Ωp∘τ
variable (d0:0<d)
include d0
lemma tent_profile (G : Pane N)(h:Guard G d) : profile G ∈ Openc (More N) d:= ⟨G,h,(show ‖profile G-profile G‖<d from by simpa using d0)⟩
lemma tent_germ : ∀ᶠ u in 𝓝 (0:A), Guard (increment 1 u) d:=by
 obtain ⟨x,t,-,h⟩:= Chaff.toll_y d0; exact (show ∀ᶠ u:A in 𝓝 0,u∈ Metric.ball (0:A) x from (Metric.ball_mem_nhds _ t)).mono fun u h'=> h _ _ (guard0 le_rfl) _ (mem_ball_zero_iff.mp h')
-- suppress connection to composeCost effect 
include K
lemma parts_jet : Allows 3 (pieces T X i j ∘increment 1) (0:tangD N) (composeCost 3 (T.W X i j) g⁻¹) := by
 let f(x:A):= g • x; let V(x:A):= if Guard (τ (f x)) d then (τ (f x)) else 1; 
 have hv : τ ∘ f =ᶠ[𝓝 (0:A)] V:=(((show Tendsto f (𝓝 0) (𝓝 (0:A)) from by simpa [f] using (show Continuous f by unfold f; fun_prop).tendsto 0).eventually (tent_germ d0)).mono (fun i h=> by change τ (f i)=V i; unfold V; rw [if_pos h]))
 have he(y):Guard (V y) d:=by unfold V; split; assumption; exact guard0 d0.le
 let U(y:A):↑Κ:=⟨_,tent_profile d0 (V y) (he y)⟩
 let H(y:A) := Ωp (τ (f y))
 have hp:Allows 3 H 0 (T.W X i j) := by
    refine Allows.germ (K.warm (F:= T.F X ()) (T.W X) (T.coat X|>.1 ()) A U 0 V (fun _=>rfl) (he 0) ?_ i j) (hv.mono ?_)
    · intro x _; let Jl := (ContinuousLinearMap.proj (R:=ℝ) (φ:=fun _:Edge (Site (More N))=>group.Color) x); have hl: ‖g • Jl‖≤g:= by rw [norm_smul,Real.norm_eq_abs,abs_of_pos K.peta]; exact mul_le_of_le_one_right K.peta.le (ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun y=> (norm_le_pi_norm y x).trans_eq (one_mul _).symm))
      have hd:Rill.Tender (fun y:A=> τ (f y) x) 0 b 3:= K.until' A (g • Jl) ((1:Pane N) x) hl
      exact tGerm2 hd (hv.mono fun i e=> congrFun e x)
    intro y (ht: τ (f y)=V y)
    change T.F X () (U y) i j=Ωp (τ (f y)); rw [ht,pieces,dif_pos (U y).property]
 let z: A→L[ℝ] A:=g⁻¹ • ContinuousLinearMap.id ℝ A
 have hu: ‖z‖ ≤ g⁻¹:= by
    unfold z; rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (inv_nonneg.mpr K.peta.le)]
    exact mul_le_of_le_one_right (inv_nonneg.mpr K.peta.le) (ContinuousLinearMap.norm_id_le (E:=A))
 have hed : H ∘ z = L:= by funext x; change Ωp (τ (g • (g⁻¹ • x)))=Ωp _; rw [smul_inv_smul₀ K.peta.ne']
 change Allows 3 L 0 _; rw [←hed]; exact Allows.comp (f:=z) (show Allows 3 H (z 0) _ from by rw [map_zero]; exact hp) (allows_linear hu (by rw [map_zero,norm_zero]; exact (norm_nonneg _).trans hu))

def pruning : A →L[ℝ] A:=
 ({ toFun y i := if i∈ leaks X then y i else 0
    map_add' f g := funext fun i=>by dsimp; split <;> simp [*]
    map_smul' c f:=funext fun i=>by dsimp; split <;> simp [*] : A→ₗ[ℝ]A}).toContinuousLinearMap

omit K in
lemma lone_germ : L ∘ pruning X =ᶠ[𝓝 (0:A)] L := by
 let P:= pruning X
 filter_upwards [tent_germ (N:=N) d0, ((show Tendsto P (𝓝 0) (𝓝 (0:A)) from by simpa using P.continuous.tendsto 0).eventually (tent_germ d0))] with x g f
 change Ωp (τ (P x))= Ωp (τ x)
 unfold pieces; rw [dif_pos (tent_profile d0 (τ (P x)) f),dif_pos (tent_profile d0 (τ x) g)]
 let v:↑Κ:=⟨profile (τ x),tent_profile d0 _ g⟩; let w: ↑Κ:=⟨profile (τ (P x)),tent_profile d0 _ f⟩
 have hc: fare X w.val v.val=0:=by
   refine Finset.sum_eq_zero ?_; intro i hi; have hp:P x i=x i:=by unfold P; change (if _ then x i else 0)=x i; rw [if_pos hi]
   change ‖profile (τ (P x)) i-profile (τ x) i‖=0; rw [show profile (τ (P x)) i=profile (τ x) i from (by funext j; unfold profile; unfold increment; rw [hp]),sub_self,norm_zero]
 have hx:= (T.coat X|>.1 ()).expo i j|>.variation w v; change ‖T.F X _ w i j-T.F X _ v i j‖≤_* (fare X _ _/_) at hx
 exact sub_eq_zero.mp (norm_le_zero_iff.mp (hx.trans_eq (by rw [hc,zero_div,mul_zero])))
lemma lone_cost (F G: A) : donor Ωp F G=donor Ωp ((pruning X) F) ((pruning X) G) := by
 let P:=pruning X; let D_ :=iteratedFDeriv ℝ 2 L 0; let hU :=lone_germ T X i j d0
 have he : D_ = D_.compContinuousLinearMap (fun _=> P):= (Filter.EventuallyEq.eq_of_nhds ((hU.iteratedFDeriv (𝕜:=ℝ) 2))).symm.trans (Next.Foundations.jets_linear (pruning X) ((parts_jet T X K i j d0).smooth.of_le (m:= ↑(2:ℕ)) (by decide)))
 change (2:ℝ)⁻¹ • fderiv ℝ (fderiv ℝ L) 0 F G= (2:ℝ)⁻¹ • ((fderiv ℝ (fderiv ℝ L) 0 (P F)) (P G):ℂ); apply congrArg
 let f:= (![F,G]:Fin 2→A); rw [show fderiv ℝ (fderiv ℝ L) 0 F G=D_ f from (iteratedFDeriv_two_apply L 0 f).symm,he]; exact iteratedFDeriv_two_apply L 0 (fun i=>P (f i))
#print axioms lone_cost
end shed
end YM.CF.LitCurrent.Surplus
