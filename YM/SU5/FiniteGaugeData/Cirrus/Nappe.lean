import YM.SU5.FiniteGaugeData.Cirrus.SingularW
/-! # Net relative descriptors in positive-energy pvm Hilbert space. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Hierarchy.Seld.Poin.Cirrus.PavilionM
open Complex Filter Function Set MeasureTheory MeasureTheory.Measure Boundary OS OS.Semigroup Probe Maison Flute Mink Metric
open scoped Topology NNReal InnerProductSpace
variable {H:Hilbert}(S: OS.Semigroup H timeAxis)(Ω:Bench S)(hΩ:∀ x:E4,M S x Ω.val=Ω.val) {ι:Type}(G:Canopy H ι) (J K:Set ι)(U V:Set E4)
local notation "X"=> Effort S Ω G
local notation "Ω₁"=>G.focus S Ω []
local notation "Kₐ"=> Hull S Ω G
open Canopy Submodule
variable (Pn:Boundary.Action H)(L:G.Arrival S Ω Pn)
local notation "T₂"=> DualR S Ω G
private lemma vista (p q:E4)(e:p-q∈ Mink.spacelike) : ∃ r:ℝ,0<r∧ separated (ball p r) (ball q r):=by
 let E: Set (E4× E4):=(fun x=>x.1-x.2) ⁻¹' Mink.spacelike; obtain ⟨U,V,v,x,w,y,o⟩:=mem_nhds_prod_iff'.1 ( (Mink.open_spacelike.preimage (continuous_fst.sub continuous_snd)).mem_nhds (show (p,q)∈ E from e))
 obtain ⟨r,k,h⟩:= Metric.mem_nhds_iff.mp (v.mem_nhds x); obtain ⟨s,l,t⟩:=Metric.mem_nhds_iff.mp (w.mem_nhds y)
 exact ⟨min r s,lt_min k l,fun x u y v=> o (show (x,y)∈U ×ˢ V from ⟨h (ball_subset_ball (min_le_left _ _) u), t (ball_subset_ball (min_le_right ..) v)⟩)⟩
lemma anywhere (x:E4)(s:ℝ)(k:0<s)(e:Mink.Ray): ∃ y:E4,x-y∈Mink.spacelike∧time y=time x∧ dist x y=s := by
 let q:= (magnet e).val; have he : time q=0:= (magnet e).property; let y:=x-s • q; have hy:x-y=s • q:= sub_sub_cancel ..; refine ⟨y,?_,?_,?_⟩
 · rw [hy,lateral]; rw [Mink.clock_mul,he,mul_zero, abs_zero,rest_mul,norm_smul]; unfold q magnet; simp [e.property,k.ne']
 · unfold y; simp [sub_eq_add_neg,he]
 rw [dist_eq_norm,hy,norm_smul,Real.norm_eq_abs, abs_of_pos k,show ‖q‖=1 from bearing e,mul_one]
structure NetStory :Prop where
 isotony(J K:Set ι)(U V:Set E4)(p:J ⊆ K)(q:U ⊆ V): Kₐ J U≤Kₐ K V
 adjacency(J K:Set ι)(U V:Set E4) (e:separated U V)(A B:X)(u:A∈Kₐ J U)(p:B∈Kₐ K V): Commute A B
 move(P:Mink.Poincare)(J:Set ι)(U:Set E4)(A:X): A∈ Hull S Ω G J U ↔ actionAt S Ω G Pn L P A∈ Hull S Ω G J (P.sends '' U)
 starR(J:Set ι)(U:Set E4)(A:X)(p:A∈ Hull S Ω G J U): ∃ B∈Hull S Ω G J U,T₂ A B∧ ∀ C:X,T₂ A C→ C=B
 graphR(J:Set ι)(U:Set E4)(A:X)(p:A∈ Hull S Ω G J U)(x:ℕ→ G.Model S Ω)(y:H) (q:Tendsto (fun i=>G.lens S Ω (x i)) atTop (𝓝 0))(t:Tendsto (fun i=>G.lens S Ω (A (x i))) atTop (𝓝 y)): y=0
 coverage (J:Set ι)(A:X)(p:A∈ Hull S Ω G J Set.univ): ∃ r:ℝ,0<r∧A∈ Hull S Ω G J (ball 0 r)
 height (J:Set ι)(U:Set E4)(_ : U.Nonempty)(_ :IsOpen U) : (CensusR S Ω G J U).topologicalClosure= Height S Ω G J
 localW (U:Set E4)(_ :U.Nonempty)(_ :IsOpen U): DenseRange (Sales S Ω G Set.univ U)
 faith (J:Set ι)(U V:Set E4)(_:separated U V)(_ :V.Nonempty)(_ :IsOpen V)(A:X) (_:A∈ Kₐ J U)(_ : A Ω₁=0): A=0
 keepCenter : (∀ x:H.space,(∀ p:E4,M S p x=x)→∃ z:ℂ,x=z• Ω.val) → (∀ T:H.Op,weakR S Ω G T → ∃ c:ℂ,T=c • 1)
include L hΩ
lemma berth : NetStory S Ω G Pn L:=by
 refine ⟨fun J K U V=>regi S Ω G J K U V, fun _ _ _ _ z A B p q=>apart S Ω G _ _ _ _ A B Pn L z p q, fun p J U A=>trunk S Ω G _ _ A Pn p L, ?_, fun J U A p x y h k=> final S Ω G _ _ A Pn L p _ _ h k, fun J A p=> globe _ _ _ _ _ p, fun J U u p=> plot_reach S Ω hΩ G J Pn L.time U p u, fun U u p=> blessed S Ω G _ Pn L hΩ p u, fun J U V z v q A p u=> separating S Ω G _ _ _ A Pn L hΩ z q v p u, fun h T v=> scalarB S Ω G T Pn L hΩ v h⟩
 intro J U A p; obtain ⟨B,z,u⟩:= reserve S Ω G _ _ _ Pn L p; exact ⟨B,z,u,fun C q=> uniq_δ S Ω G A B Pn L u q⟩
lemma pictureAnywhere (p:¬ Pale S Ω G J K)(x y:E4)(q:x-y∈ Mink.spacelike): ∃ ρ:ℝ,0<ρ∧∀ r:ℝ,0<r → r ≤ ρ → separated (ball x r) (ball y r)∧ Soul S Ω G J K (ball x r) (ball y r):= by
 obtain ⟨v,H,T⟩:=vista x y q; refine ⟨v,H,fun r h hp=>?_⟩; let U:= ball x r; let V:=ball y r; have hw:separated U V:= fun x p y q=>T x (ball_subset_ball hp p) y (ball_subset_ball hp q)
 exact ⟨hw,exactC S Ω G J K _ _ Pn L hΩ p isOpen_ball ⟨_,mem_ball_self h⟩ isOpen_ball ⟨_,mem_ball_self h⟩ hw⟩
#print axioms pictureAnywhere
#print axioms berth
end YM.CF.Buffered.Afterglow.Hierarchy.Seld.Poin.Cirrus.PavilionM
